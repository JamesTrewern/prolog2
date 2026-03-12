use std::{
    env, fs,
    io::{stdin, stdout, Write},
    process::ExitCode,
};

use console::Term;
use serde::{Deserialize, Serialize};

use crate::{
    heap::{
        heap::{Cell, Heap},
        query_heap::QueryHeap,
        symbol_db::SymbolDB,
    },
    parser::{
        build_tree::{TokenStream, TreeClause},
        execute_tree::{build_clause, execute_tree},
        tokeniser::tokenise,
    },
    predicate_modules::{load_predicate_module, PredicateModule},
    program::predicate_table::PredicateTable,
    resolution::proof::Proof,
};

/// Engine configuration loaded from a JSON setup file.
#[derive(Clone, Copy, Serialize, Deserialize, Debug)]
pub struct Config {
    /// Maximum proof search depth.
    pub max_depth: usize,
    /// Maximum number of learned clauses per hypothesis.
    pub max_clause: usize,
    /// Maximum number of invented predicates.
    pub max_pred: usize,
    /// Enable debug trace output.
    #[serde(default)]
    pub debug: bool,
}

/// A body predicate declaration in the setup file.
#[derive(Serialize, Deserialize, Debug)]
pub struct BodyClause {
    /// Predicate name.
    pub symbol: String,
    /// Predicate arity.
    pub arity: usize,
}

/// Positive and negative training examples.
#[derive(Serialize, Deserialize, Debug)]
pub struct Examples {
    /// Positive examples (goals that should succeed).
    pub pos: Vec<String>,
    /// Negative examples (goals that should fail).
    pub neg: Vec<String>,
}

/// Top-level setup loaded from a JSON configuration file.
#[derive(Serialize, Deserialize, Debug)]
pub struct SetUp {
    pub config: Config,
    pub body_predicates: Vec<BodyClause>,
    pub files: Vec<String>,
    pub examples: Option<Examples>,
    /// When true, run Top Program Construction instead of a direct query.
    #[serde(default)]
    pub top_prog: bool,
    /// When true, skip the reduction step in Top Program Construction.
    #[serde(default)]
    pub no_reduce: bool,
}

impl Examples {
    /// Convert the examples into a single Prolog query string.
    ///
    /// Positive examples become goals; negative examples are wrapped in `not(...)`.
    pub fn to_query(&self) -> String {
        let mut buffer = String::new();
        for pos_ex in &self.pos {
            buffer += pos_ex;
            buffer += ",";
        }
        for neg_ex in &self.neg {
            buffer += &format!("not({neg_ex}),");
        }
        buffer.pop();
        buffer += ".";
        buffer
    }
}

/// Builder for configuring and running the Prolog² engine.
///
/// # Example
///
/// ```no_run
/// use prolog2::app::App;
/// use prolog2::predicate_modules::{MATHS, META_PREDICATES};
///
/// App::from_args()
///     .add_module(&MATHS)
///     .add_module(&META_PREDICATES)
///     .run();
/// ```
pub struct App {
    modules: Vec<&'static PredicateModule>,
    config_path: String,
    auto: bool,
}

impl App {
    /// Create a new builder with no modules and default settings.
    pub fn new() -> Self {
        App {
            modules: Vec::new(),
            config_path: "setup.json".into(),
            auto: false,
        }
    }

    /// Create a builder pre-configured from command-line arguments.
    ///
    /// Parses `std::env::args()` for:
    /// - A config file path (first non-flag argument, default: `"setup.json"`)
    /// - `--all` / `-a` to auto-enumerate all solutions
    pub fn from_args() -> Self {
        let args: Vec<String> = env::args().collect();
        let auto = args.iter().any(|arg| arg == "--all" || arg == "-a");

        let config_path = args
            .iter()
            .filter(|arg| !arg.starts_with('-') && *arg != &args[0])
            .next()
            .cloned()
            .unwrap_or_else(|| "setup.json".into());

        App {
            modules: Vec::new(),
            config_path,
            auto,
        }
    }

    /// Register a predicate module.
    pub fn add_module(mut self, module: &'static PredicateModule) -> Self {
        self.modules.push(module);
        self
    }

    /// Set the config file path.
    pub fn config(mut self, path: impl Into<String>) -> Self {
        self.config_path = path.into();
        self
    }

    /// Set whether to auto-enumerate all solutions.
    pub fn auto(mut self, value: bool) -> Self {
        self.auto = value;
        self
    }

    /// Load the configuration, register modules, and run.
    ///
    /// If the config contains examples, they are run as a query.
    /// Otherwise an interactive REPL is started.
    pub fn run(self) -> ExitCode {
        let (config, predicate_table, heap, examples, top_prog, no_reduce) = self.load_setup();

        match (examples, top_prog) {
            (Some(examples), true) => {
                crate::top_prog::run(examples, &predicate_table, heap, config, no_reduce)
            }
            (Some(examples), false) => {
                start_query(&examples.to_query(), &predicate_table, &heap, config, self.auto)
                    .unwrap();
                ExitCode::SUCCESS
            }
            (None, _) => main_loop(config, predicate_table, &heap),
        }
    }

    fn load_setup(&self) -> (Config, PredicateTable, Vec<Cell>, Option<Examples>, bool, bool) {
        let mut heap = Vec::new();
        let mut predicate_table = PredicateTable::new();

        for module in &self.modules {
            load_predicate_module(&mut predicate_table, module);
        }

        let setup: SetUp = serde_json::from_str(
            &fs::read_to_string(&self.config_path)
                .unwrap_or_else(|_| panic!("Failed to read config file: {}", self.config_path)),
        )
        .unwrap_or_else(|e| {
            panic!("Failed to parse config file '{}': {}", self.config_path, e)
        });
        let config = setup.config;

        for file_path in setup.files {
            load_file(file_path, &mut predicate_table, &mut heap);
        }

        for BodyClause { symbol, arity } in setup.body_predicates {
            let sym = SymbolDB::set_const(symbol.clone());
            predicate_table
                .set_body((sym, arity), true)
                .unwrap_or_else(|e| panic!("{e}: {symbol}/{arity}"));
        }

        (config, predicate_table, heap, setup.examples, setup.top_prog, setup.no_reduce)
    }
}

fn load_file(file_path: String, predicate_table: &mut PredicateTable, heap: &mut Vec<Cell>) {
    let file = fs::read_to_string(&file_path)
        .unwrap_or_else(|_| panic!("Failed to read file: {}", file_path));
    let syntax_tree = TokenStream::new(tokenise(file).unwrap())
        .parse_all()
        .unwrap();

    execute_tree(syntax_tree, heap, predicate_table);
}

fn continue_proof(auto: bool) -> bool {
    if auto {
        return true;
    }
    let term = Term::stderr();
    loop {
        match term.read_key_raw().unwrap() {
            console::Key::Enter | console::Key::Backspace | console::Key::Char('.') => {
                return false
            }
            console::Key::Char(' ' | ';') | console::Key::Tab => return true,
            _ => (),
        }
    }
}

fn start_query(
    query_text: &str,
    predicate_table: &PredicateTable,
    heap: &[Cell],
    config: Config,
    auto: bool,
) -> Result<(), String> {
    let query = format!(":-{query_text}");
    let literals = match TokenStream::new(tokenise(query)?).parse_clause()? {
        Some(TreeClause::Directive(literals)) => literals,
        _ => return Err(format!("Query: '{query_text}' incorrectly formatted")),
    };

    let mut query_heap = QueryHeap::new(heap, None);
    let goals = build_clause(literals, None, None, &mut query_heap, true);
    let mut vars = Vec::new();
    for literal in goals.iter() {
        vars.extend(query_heap.term_vars(*literal, false).iter().map(|addr| {
            (
                SymbolDB::get_var(*addr, query_heap.get_id()).unwrap(),
                *addr,
            )
        }));
    }
    let mut proof = Proof::new(query_heap, &goals);

    loop {
        if proof.prove(&predicate_table, config) {
            println!("TRUE");
            for (symbol, addr) in &vars {
                println!("{symbol} = {}", proof.heap.term_string(*addr))
            }
            // TODO: display variable bindings
            if proof.hypothesis.len() != 0 {
                println!("{}", proof.hypothesis.to_string(&proof.heap));
            }
            if !continue_proof(auto) {
                break;
            }
        } else {
            println!("FALSE");
            break;
        }
    }

    drop(proof);

    Ok(())
}

fn main_loop(
    config: Config,
    predicate_table: PredicateTable,
    heap: &[Cell],
) -> ExitCode {
    let mut buffer = String::new();
    loop {
        if buffer.is_empty() {
            print!("?-");
            stdout().flush().unwrap();
        }
        match stdin().read_line(&mut buffer) {
            Ok(_) => {
                if buffer.contains('.') {
                    match start_query(
                        &buffer,
                        &predicate_table,
                        heap,
                        config,
                        false,
                    ) {
                        Ok(_) => buffer.clear(),
                        Err(error) => println!("{error}"),
                    }
                } else {
                    continue;
                }
            }
            Err(error) => {
                println!("error: {error}");
                break;
            }
        }
    }
    ExitCode::SUCCESS
}
