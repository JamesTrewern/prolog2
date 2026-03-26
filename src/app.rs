use std::{
    fs::{self, metadata},
    io,
    path::Path,
    process::ExitCode,
    sync::Arc,
};

use rustyline::error::ReadlineError;

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
    Error,
    Result,
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
/// Deserialized from a string whith predicate and arity seperated by '/'
/// e.g `"p/2"`.
#[derive(Serialize, Debug)]
pub struct BodyPred {
    /// Predicate name.
    pub symbol: String,
    /// Predicate arity.
    pub arity: usize,
}

impl TryFrom<&str> for BodyPred {
    type Error = String;

    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        let (symbol, arity_str) = value
            .rsplit_once('/')
            .ok_or_else(|| format!("expected \"symbol/arity\", got {value:?}"))?;
        let arity = arity_str
            .parse()
            .map_err(|_| format!("arity must be a non-negative integer, got {arity_str:?}"))?;
        Ok(Self {
            symbol: symbol.into(),
            arity,
        })
    }
}

impl<'de> serde::Deserialize<'de> for BodyPred {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        use serde::de::{self, Visitor};
        use std::fmt;

        struct BodyPredVisitor;

        impl<'de> Visitor<'de> for BodyPredVisitor {
            type Value = BodyPred;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str(r#"a string like "p/2""#)
            }

            fn visit_str<E: de::Error>(self, v: &str) -> std::result::Result<BodyPred, E> {
                v.try_into().map_err(|err|E::custom(err))
            }
        }

        deserializer.deserialize_any(BodyPredVisitor)
    }
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

/// The top-level Prolog² engine.
///
/// `App` owns the program heap and predicate table and exposes a builder API
/// for constructing an engine, loading code, and running queries.
///
/// # Building an engine
///
/// Use [`App::new`] for a bare engine with no built-in predicates, or
/// [`App::default`] to include the standard built-in modules. Chain builder
/// methods to configure the engine before running:
///
/// ```no_run
/// use prolog2::app::App;
/// use prolog2::predicate_modules::MATHS;
///
/// let app = App::default()
///     .load_module(&MATHS).unwrap()
///     .load_file("facts.pl".as_ref()).unwrap();
/// ```
///
/// Alternatively, load the full configuration from a JSON setup file with
/// [`App::from_setup_json`].
///
/// # Running queries
///
/// - [`App::run`] is the high-level entry point used by the binary; it starts
///   an interactive REPL or runs configured examples depending on state.
/// - [`App::start_query`] runs a single query string and prints solutions
///   interactively to stdout.
/// - [`App::query_session`] returns a [`QuerySession`] for programmatic
///   iteration over solutions without any I/O side-effects.
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
            app = app.load_module(predicate_module).expect("built-in module should always load");
        }
        app
    }
}

impl App {
    /// Creates a bare engine with no predicates loaded.
    ///
    /// Use [`App::default`] instead if you want the standard built-in modules
    /// (arithmetic, meta-predicates, etc.) included automatically.
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

    /// Sets the engine configuration (search depth, clause limits, debug mode).
    pub fn config(self, config: Config) -> Self {
        App { config, ..self }
    }

    /// When `true`, solution search runs without pausing to ask the user
    /// whether to continue — equivalent to always pressing `;`.
    pub fn auto(self, auto: bool) -> Self {
        App { auto, ..self }
    }

    /// Configures whether Top Program Construction is run instead of a direct
    /// query, and whether the learned program is reduced afterwards.
    pub fn top_prog(self, top_prog: TopProg) -> Self {
        App { top_prog, ..self }
    }

    /// Sets the positive and negative training examples used by [`App::run`]
    /// when no interactive REPL is desired.
    pub fn examples(self, examples: Examples) -> Self {
        App {
            examples: Some(examples),
            ..self
        }
    }

    /// Loads and fully initialises an engine from a JSON setup file.
    ///
    /// The setup file controls the [`Config`], which `.pl` source files to
    /// load, which predicates are available as body predicates for MIL, and
    /// any training examples. See [`SetUp`] for the full schema.
    ///
    /// # Errors
    ///
    /// Returns [`Error::IO`] if the file cannot be read, [`Error::Setup`] if
    /// the JSON is malformed, or [`Error::Parser`] if any of the loaded `.pl`
    /// files contain a syntax error.
    pub fn from_setup_json(path: impl AsRef<str>) -> Result<Self> {
        let path = path.as_ref();
        let setup: SetUp = serde_json::from_str(&fs::read_to_string(path)?)?;

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
            app = app.load_module(predicate_module).expect("built-in module should always load");
        }

        for path in setup.files {
            let path = Path::new(&path);
            if path.metadata()?.is_dir() {
                app = app.load_dir(path)?;
            } else {
                app = app.load_file(&path)?;
            }
        }
        app.add_body_predicates(setup.body_predicates)
    }

    /// Parses a Prolog source string and adds all clauses to the program.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Parser`] if the source contains a syntax error.
    pub fn load_code(mut self, code: impl AsRef<str>) -> Result<Self> {
        let syntax_tree = TokenStream::new(tokenise(code)?).parse_all()?;
        execute_tree(syntax_tree, &mut self.prog_heap, &mut self.predicate_table);
        Ok(self)
    }

    /// Reads a `.pl` file from disk and loads it with [`App::load_code`].
    ///
    /// # Errors
    ///
    /// Returns [`Error::IO`] if the file cannot be read, or [`Error::Parser`]
    /// if it contains a syntax error.
    pub fn load_file(self, file: &Path) -> Result<Self> {
        self.load_code(fs::read_to_string(file)?)
    }

    /// Recursively loads all `.pl` files found under `dir_path`.
    ///
    /// Subdirectories are traversed depth-first. Files with extensions other
    /// than `.pl` are silently skipped.
    ///
    /// # Errors
    ///
    /// Returns [`Error::IO`] on filesystem errors or [`Error::Parser`] if any
    /// file contains a syntax error.
    pub fn load_dir(mut self, dir_path: &Path) -> Result<Self> {
        let paths = fs::read_dir(&dir_path)?;
        for path_result in paths {
            let path = path_result?.path();
            if path.metadata()?.is_dir() {
                self = self.load_dir(&path)?
            } else {
                if path.extension().map(|extension| extension.to_str()) == Some("pl".into()) {
                    self = self.load_file(&path)?;
                }
            }
        }
        Ok(self)
    }

    /// Registers a [`PredicateModule`], making its built-in predicates and
    /// any bundled Prolog source available to the engine.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Parser`] if the module's bundled source contains a
    /// syntax error.
    pub fn load_module(mut self, predicate_module: &PredicateModule) -> Result<Self> {
        for (symbol, arity, pred_fn) in predicate_module.0.iter() {
            self.predicate_table
                .insert_predicate_function(
                    (SymbolDB::set_const((*symbol).to_string()), *arity),
                    *pred_fn,
                )
                .unwrap();
        }
        for &code in predicate_module.1 {
            self = self.load_code(code)?;
        }
        Ok(self)
    }

    /// Marks a set of predicates as *body predicates* for Meta-Interpretive
    /// Learning.
    ///
    /// Body predicates are the background knowledge predicates that the MIL
    /// engine is permitted to use in the body of learned clauses. Any predicate
    /// listed here must already be present in the program (loaded via
    /// [`App::load_code`], [`App::load_file`], or [`App::load_module`]).
    ///
    /// # Panics
    ///
    /// Panics if a predicate named in `body_preds` does not exist in the
    /// predicate table.
    pub fn add_body_predicates<'a>(mut self, body_preds: impl AsRef<[BodyPred]>) -> Result<Self> {
        for BodyPred { symbol, arity } in body_preds.as_ref() {
            let sym = SymbolDB::set_const(symbol.clone());
            self.predicate_table
                .set_body((sym, *arity), true)
                .unwrap_or_else(|e| panic!("{e}: {symbol}/{arity}"));
        }
        Ok(self)
    }

    /// Runs a Prolog query and prints each solution to stdout interactively.
    ///
    /// After each solution the user is prompted to press `;` or Space to
    /// search for the next solution, or Enter/`.` to stop. When
    /// [`App::auto`] is `true` the engine finds all solutions without
    /// prompting.
    ///
    /// Output format per solution:
    /// ```text
    /// TRUE
    /// VarName = value
    /// ```
    /// Followed by `FALSE` once the search space is exhausted or the user
    /// stops early.
    ///
    /// For programmatic access to solutions without any I/O, use
    /// [`App::query_session`] instead.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Parser`] if `query` contains a syntax error.
    pub fn start_query(&self, query: impl AsRef<str>) -> Result<()> {
        let mut session = self.query_session(query)?;
        loop {
            if let Some(solution) = session.next_solution() {
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
            } else {
                println!("FALSE");
                break;
            }
        }
        Ok(())
    }

    /// Opens a [`QuerySession`] for a Prolog query string.
    ///
    /// Unlike [`App::start_query`], this method performs no I/O. Solutions are
    /// retrieved by calling [`QuerySession::next_solution`] (or by iterating,
    /// since [`QuerySession`] implements [`Iterator`]).
    ///
    /// The session borrows `self` for its lifetime, so the engine cannot be
    /// mutated while a session is open.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Parser`] if `query` contains a syntax error.
    pub fn query_session(&self, query: impl AsRef<str>) -> Result<QuerySession<'_>> {
        let query = query.as_ref();
        let literals = TokenStream::new(tokenise(query)?).parse_goals()?;

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

    /// Opens a [`QuerySession`] built from the training examples set on this
    /// engine.
    ///
    /// Positive examples become goals; negative examples are wrapped in
    /// `not(...)`. This is a convenience wrapper around [`App::query_session`]
    /// using [`Examples::to_query`].
    ///
    /// # Errors
    ///
    /// Returns [`Error::Query`] if no examples have been set, or
    /// [`Error::Parser`] if the generated query string is malformed.
    pub fn query_session_from_examples(&self) -> Result<QuerySession<'_>> {
        self.query_session(
            self.examples
                .as_ref()
                .map(|examples| examples.to_query())
                .ok_or(Error::Query("No examples in app state".into()))?,
        )
    }

    /// High-level entry point — runs the engine and returns an exit code.
    ///
    /// Behaviour depends on the engine state:
    ///
    /// - **No examples set** — starts the interactive REPL ([`App::main_loop`]).
    /// - **Examples set, no Top Program Construction** — runs
    ///   [`App::start_query`] on the examples and exits.
    /// - **Examples set, Top Program Construction enabled** — runs the TPC
    ///   algorithm and prints any learned clauses.
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

    /// Runs the interactive read-eval-print loop.
    ///
    /// Presents a `?- ` prompt and accepts Prolog queries terminated by `.`.
    /// Multi-line queries are supported; a `|  ` continuation prompt is shown
    /// until a `.` is seen.
    ///
    /// Input history is persisted to `~/.prolog2_history` across sessions.
    /// Arrow keys provide cursor movement (left/right) and history navigation
    /// (up/down). Press Ctrl+C or Ctrl+D to exit.
    pub fn main_loop(&self) -> ExitCode {
        let mut rl = rustyline::DefaultEditor::new().expect("Failed to initialise line editor");

        let history_path = home::home_dir().map(|p| p.join(".prolog2_history"));
        if let Some(path) = &history_path {
            let _ = rl.load_history(path); // silently ignore if file doesn't exist yet
        }

        let mut buffer = String::new();
        loop {
            let prompt = if buffer.is_empty() { "?- " } else { "|  " };
            match rl.readline(prompt) {
                Ok(line) => {
                    buffer.push_str(&line);
                    buffer.push('\n');
                    if buffer.contains('.') {
                        // Store the full query in history, collapsing newlines for readability
                        let entry = buffer.trim().replace('\n', " ");
                        let _ = rl.add_history_entry(&entry);
                        match self.start_query(&buffer) {
                            Ok(_) => {}
                            Err(error) => println!("{error}"),
                        }
                        buffer.clear();
                    }
                }
                Err(ReadlineError::Interrupted) => {
                    // Ctrl+C — quit the REPL
                    break;
                }
                Err(ReadlineError::Eof) => {
                    // Ctrl+D — quit the REPL
                    break;
                }
                Err(error) => {
                    println!("error: {error}");
                    break;
                }
            }
        }

        if let Some(path) = &history_path {
            let _ = rl.save_history(path);
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

/// An active proof-search session for a single Prolog query.
///
/// Created by [`App::query_session`] or [`App::query_session_from_examples`].
/// Borrows the engine for its lifetime.
///
/// Solutions are retrieved one at a time via [`QuerySession::next_solution`].
/// `QuerySession` also implements [`Iterator`]`<Item = `[`Solution`]`>`, so it
/// can be used directly in `for` loops or with iterator adaptors.
///
/// Backtracking state is maintained between calls, so each call to
/// `next_solution` resumes the proof search from where it left off.
pub struct QuerySession<'a> {
    proof: Proof<'a>,
    vars: Vec<(Arc<str>, usize)>, // (variable_name, heap_address)
    predicate_table: &'a PredicateTable,
    config: Config,
}

/// A single solution returned by [`QuerySession`].
pub struct Solution {
    /// Variable bindings as `(name, display_string)` pairs, in the order the
    /// variables appear in the query.
    pub bindings: Vec<(Arc<str>, String)>,
    /// Any clauses learned during this proof step via Top Program Construction,
    /// rendered as a Prolog source string. Empty if no hypothesis was formed.
    pub hypothesis: String,
}

impl<'a> QuerySession<'a> {
    /// Advances to the next solution, returning `None` when the search space
    /// is exhausted.
    ///
    /// Each call resumes backtracking from where the previous call left off.
    /// Variable bindings are returned as display strings; the hypothesis field
    /// contains any clauses learned via MIL during this proof step.
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

impl<'a> Iterator for QuerySession<'a> {
    type Item = Solution;

    fn next(&mut self) -> Option<Self::Item> {
        if self.proof.prove(self.predicate_table, self.config) {
            let bindings = self
                .vars
                .iter()
                .map(|(name, addr)| (name.clone(), self.proof.heap.term_string(*addr)))
                .collect();
            let hypothesis = if self.proof.hypothesis.len() > 0 {
                for clause in self.proof.hypothesis.iter() {
                    clause.normalise_clause_vars(&mut self.proof.heap);
                }
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
