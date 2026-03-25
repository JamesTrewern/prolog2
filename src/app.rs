use std::{
    fs,
    io::{stdin, stdout, Write},
    process::ExitCode,
    sync::Arc,
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
    predicate_modules::{PredicateModule, DEFAULT_MODULES},
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

impl Default for Config {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_clause: 4,
            max_pred: 2,
            debug: false,
        }
    }
}

/// A body predicate declaration in the setup file.
#[derive(Serialize, Deserialize, Debug)]
pub struct BodyPred {
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

pub enum TopProg {
    True(bool), //Run Top Program Construction with option to reduce or not
    False,
}
/// Top-level setup loaded from a JSON configuration file.
#[derive(Serialize, Deserialize, Debug)]
pub struct SetUp {
    pub config: Config,
    pub body_predicates: Vec<BodyPred>,
    pub files: Vec<String>,
    pub examples: Option<Examples>,
    /// When true, run Top Program Construction instead of a direct query.
    #[serde(default)]
    pub auto: bool,
    /// When true, run Top Program Construction instead of a direct query.
    #[serde(default)]
    pub top_prog: bool,
    /// When true, skip the reduction step in Top Program Construction.
    #[serde(default)]
    pub reduce: bool,
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

pub struct App {
    predicate_table: PredicateTable,
    prog_heap: Vec<Cell>,
    config: Config,
    auto: bool,
    examples: Option<Examples>,
    top_prog: TopProg,
    // log_file: Option<String>
}

impl Default for App {
    fn default() -> Self {
        let mut app = App::new();
        for predicate_module in DEFAULT_MODULES {
            app.load_module(predicate_module);
        }
        app
    }
}

impl App {
    pub fn new() -> Self {
        App {
            predicate_table: PredicateTable::new(),
            prog_heap: Vec::new(),
            config: Config::default(),
            auto: false,
            examples: None,
            top_prog: TopProg::False,
        }
    }

    pub fn config(self, config: Config) -> Self {
        App { config, ..self }
    }

    pub fn auto(self, auto: bool) -> Self {
        App { auto, ..self }
    }

    pub fn top_prog(self, top_prog: TopProg) -> Self {
        App { top_prog, ..self }
    }

    pub fn examples(self, examples: Examples) -> Self {
        App {
            examples: Some(examples),
            ..self
        }
    }

    pub fn from_setup_json(path: impl AsRef<str>) -> Self {
        let path = path.as_ref();
        let setup: SetUp = serde_json::from_str(
            &fs::read_to_string(path)
                .unwrap_or_else(|_| panic!("Failed to read config file: {}", path)),
        )
        .unwrap_or_else(|e| panic!("Failed to parse config file '{}': {}", path, e));
        let top_prog = if setup.top_prog {
            TopProg::True(setup.reduce)
        } else {
            TopProg::False
        };
        let mut app = App {
            predicate_table: PredicateTable::new(),
            prog_heap: Vec::<Cell>::new(),
            config: setup.config,
            auto: setup.auto,
            examples: setup.examples,
            top_prog,
        };

        for predicate_module in DEFAULT_MODULES {
            app.load_module(predicate_module);
        }

        for file in setup.files {
            app.load_file(file);
        }
        app.add_body_predicates(setup.body_predicates);

        app
    }

    pub fn load_code(&mut self, code: impl AsRef<str>) {
        let syntax_tree = TokenStream::new(tokenise(code).unwrap())
            .parse_all()
            .unwrap();

        execute_tree(syntax_tree, &mut self.prog_heap, &mut self.predicate_table);
    }

    pub fn load_file(&mut self, file: impl AsRef<str>) {
        self.load_code(fs::read_to_string(file.as_ref()).unwrap());
    }

    pub fn load_module(&mut self, predicate_module: &PredicateModule) {
        for (symbol, arity, pred_fn) in predicate_module.0.iter() {
            self.predicate_table
                .insert_predicate_function(
                    (SymbolDB::set_const((*symbol).to_string()), *arity),
                    *pred_fn,
                )
                .unwrap();
        }
        for &code in predicate_module.1 {
            self.load_code(code);
        }
    }

    pub fn add_body_predicates(&mut self, body_preds: impl AsRef<[BodyPred]>) {
        for BodyPred { symbol, arity } in body_preds.as_ref() {
            let sym = SymbolDB::set_const(symbol.clone());
            self.predicate_table
                .set_body((sym, *arity), true)
                .unwrap_or_else(|e| panic!("{e}: {symbol}/{arity}"));
        }
    }

    pub fn start_query(&self, query: impl AsRef<str>) -> Result<(), String> {
        let mut session = self.query_session(query)?;
        while let Some(solution) = session.next_solution() {
            println!("TRUE");
            for (name, value) in &solution.bindings {
                println!("{name} = {value}");
            }
            if !solution.hypothesis.is_empty() {
                println!("{}", solution.hypothesis);
            }
            if !continue_proof(self.auto) {
                break;
            }
        }
        Ok(())
    }

    pub fn query_session(&self, query: impl AsRef<str>) -> Result<QuerySession<'_>, String> {
        let query = query.as_ref();
        let literals = match TokenStream::new(tokenise(format!(":-{query}"))?).parse_clause()? {
            Some(TreeClause::Directive(literals)) => literals,
            _ => return Err(format!("Query: '{query}' incorrectly formatted")),
        };

        let mut query_heap = QueryHeap::new(&self.prog_heap, None);
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
        let proof = Proof::new(query_heap, &goals);
        Ok(QuerySession {
            proof,
            vars,
            predicate_table: &self.predicate_table,
            config: self.config,
        })
    }

    pub fn query_session_from_examples(&self) -> Result<QuerySession<'_>, String> {
        self.query_session(
            self.examples
                .as_ref()
                .map(|examples| examples.to_query())
                .ok_or("No examples in app state")?,
        )
    }

    /// If examples are provided run automatic query
    /// otherwise await console input query
    pub fn run(self) -> ExitCode {
        match &self.examples {
            Some(examples) => match self.top_prog {
                TopProg::True(reduce) => crate::top_prog::run(
                    examples,
                    &self.predicate_table,
                    self.prog_heap,
                    self.config,
                    reduce,
                ),
                TopProg::False => self.start_query(examples.to_query()).map_or_else(
                    |e| {
                        eprintln!("{e}");
                        ExitCode::FAILURE
                    },
                    |_| ExitCode::SUCCESS,
                ),
            },
            None => self.main_loop(),
        }
    }

    pub fn main_loop(&self) -> ExitCode {
        let mut buffer = String::new();
        loop {
            if buffer.is_empty() {
                print!("?-");
                stdout().flush().unwrap();
            }
            match stdin().read_line(&mut buffer) {
                Ok(_) => {
                    if buffer.contains('.') {
                        match self.start_query(&buffer) {
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

pub struct QuerySession<'a> {
    proof: Proof<'a>,
    vars: Vec<(Arc<str>, usize)>, // (variable_name, heap_address)
    predicate_table: &'a PredicateTable,
    config: Config,
}

pub struct Solution {
    pub bindings: Vec<(Arc<str>, String)>, // (var_name, value_string)
    pub hypothesis: String,                // learned clauses as text
}

impl<'a> QuerySession<'a> {
    /// Step to the next solution. Returns None when exhausted.
    pub fn next_solution(&mut self) -> Option<Solution> {
        if self.proof.prove(self.predicate_table, self.config) {
            let bindings = self
                .vars
                .iter()
                .map(|(name, addr)| (name.clone(), self.proof.heap.term_string(*addr)))
                .collect();
            let hypothesis = if self.proof.hypothesis.len() > 0 {
                self.proof.hypothesis.to_string(&self.proof.heap)
            } else {
                String::new()
            };
            Some(Solution {
                bindings,
                hypothesis,
            })
        } else {
            None
        }
    }
}

impl<'a> Iterator for QuerySession<'a>{
    type Item = Solution;

    fn next(&mut self) -> Option<Self::Item> {
        if self.proof.prove(self.predicate_table, self.config) {
            let bindings = self
                .vars
                .iter()
                .map(|(name, addr)| (name.clone(), self.proof.heap.term_string(*addr)))
                .collect();
            let hypothesis = if self.proof.hypothesis.len() > 0 {
                self.proof.hypothesis.to_string(&self.proof.heap)
            } else {
                String::new()
            };
            Some(Solution {
                bindings,
                hypothesis,
            })
        } else {
            None
        }
    }
}
