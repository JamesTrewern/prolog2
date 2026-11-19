//! The [`App`] struct, its builder methods and its loading functions.

use std::{fs, path::Path};

use super::config::{
    BodyPred, Config, ExampleSource, Examples, ParallelConfig, ResolutionConfig, TryIntoBodyPred,
};
use crate::{
    heap::{Heap, ProgramHeap},
    parser::{execute_tree, tokenise, Namespaces, TokenStream},
    predicate_modules::{maths::set_approx_tolerance, PredicateModule, STANDARD_MODULES},
    program::PredicateTable,
    Error, Result,
};

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
/// Alternatively, load the full configuration from a JSON config file with
/// [`App::from_config_json`].
///
/// # Running queries
///
/// - [`App::run`] is the high-level entry point used by the binary; it starts
///   an interactive REPL or runs configured examples depending on state.
/// - [`App::start_query`] runs a single query string and prints solutions
///   interactively to stdout.
/// - [`App::query_session`] returns a [`QuerySession`](super::QuerySession) for programmatic
///   iteration over solutions without any I/O side-effects.
pub struct App {
    pub(crate) predicate_table: PredicateTable,
    pub(crate) prog_heap: ProgramHeap,
    pub(crate) resolution: ResolutionConfig,
    pub(crate) auto: bool,
    pub(crate) examples: Option<Examples>,
    pub(crate) parallel: Option<ParallelConfig>,
    pub(crate) namespaces: Namespaces,
    // log_file: Option<String>
}

impl Default for App {
    fn default() -> Self {
        let mut app = App::new();
        for predicate_module in STANDARD_MODULES {
            app = app
                .load_module(predicate_module)
                .expect("built-in module should always load");
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
            prog_heap: ProgramHeap::new(),
            resolution: ResolutionConfig::default(),
            auto: false,
            examples: None,
            parallel: None,
            namespaces: Namespaces::new(),
        }
    }

    /// Sets the resolution configuration (search depth, clause limits, debug mode).
    ///
    /// `update` is given the configuration so far and returns the one to
    /// use:
    ///
    /// ```
    /// use prolog2::app::App;
    ///
    /// let app = App::default().resolution(|resolution| resolution.max_depth(10).max_clause(3));
    /// ```
    ///
    /// To give the configuration whole, ignore the one passed in:
    ///
    /// ```
    /// use prolog2::{app::App, ResolutionConfig};
    ///
    /// let app = App::default().resolution(|_| ResolutionConfig {
    ///     max_depth: 10,
    ///     ..ResolutionConfig::default()
    /// });
    /// ```
    pub fn resolution(self, update: impl FnOnce(ResolutionConfig) -> ResolutionConfig) -> Self {
        App {
            resolution: update(self.resolution),
            ..self
        }
    }

    /// Sets the tolerance for the `=~=` (approximately-equal) operator.
    ///
    /// `pct` is an integer percentage: `5` means "within 5 %". The value is
    /// stored globally and takes effect immediately. The default is `10`.
    pub fn approx_tolerance(self, pct: u8) -> Self {
        set_approx_tolerance(pct);
        self
    }

    /// When `true`, solution search runs without pausing to ask the user
    /// whether to continue — equivalent to always pressing `;`.
    pub fn auto(self, auto: bool) -> Self {
        App { auto, ..self }
    }

    /// Learn from the examples by parallel Top Program Construction rather
    /// than running them as a direct query.
    ///
    /// `update` is given the parallel settings so far -- the defaults, if
    /// none were set -- and returns the ones to use:
    ///
    /// ```
    /// use prolog2::app::App;
    ///
    /// let app = App::default().parallel(|parallel| parallel.reduce(true).pos_noise(1));
    /// ```
    ///
    /// `.parallel(|parallel| parallel)` turns it on with nothing changed. To
    /// give the settings whole, ignore the ones passed in:
    ///
    /// ```
    /// use prolog2::{app::App, ParallelConfig};
    ///
    /// let app = App::default().parallel(|_| ParallelConfig {
    ///     reduce: true,
    ///     ..ParallelConfig::default()
    /// });
    /// ```
    pub fn parallel(self, update: impl FnOnce(ParallelConfig) -> ParallelConfig) -> Self {
        App {
            parallel: Some(update(self.parallel.unwrap_or_default())),
            ..self
        }
    }

    /// Names a set of predicate symbols that a meta variable declared as
    /// `P:name` may take. A meta rule using the namespace is compiled once
    /// for each choice of member, so the namespace must exist before the
    /// rule is loaded, and cannot be changed afterwards.
    ///
    /// ```
    /// use prolog2::app::App;
    ///
    /// let app = App::default().namespace("comparator", ["less_than", "greater_than"])?;
    /// # Ok::<(), prolog2::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`Error::NameSpace`] if the namespace already exists.
    pub fn namespace(
        mut self,
        name: impl Into<String>,
        members: impl IntoIterator<Item = impl Into<String>>,
    ) -> Result<Self> {
        let name = name.into();
        if self.namespaces.contains_key(&name) {
            return Err(Error::NameSpace(format!(
                "the namespace `{name}` already exists"
            )));
        }
        self.namespaces
            .insert(name, members.into_iter().map(Into::into).collect());
        Ok(self)
    }

    /// Sets the positive and negative training examples used by [`App::run`]
    /// when no interactive REPL is desired.
    ///
    /// Takes any [`ExampleSource`]: a file path or a list of literals for the
    /// positives alone, or a pair of them for the positives and negatives.
    ///
    /// ```
    /// use prolog2::app::App;
    ///
    /// # fn main() -> prolog2::Result<()> {
    /// let app = App::default().examples((["e(east1)", "e(east2)"], ["e(west6)"]))?;
    /// let app = App::default().examples(["e(east1)", "e(east2)"])?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// A file holds one literal per line, each ended by a `.`:
    ///
    /// ```no_run
    /// use prolog2::app::App;
    ///
    /// # fn main() -> prolog2::Result<()> {
    /// let app = App::default().examples(("pos.pl", "neg.pl"))?;
    /// let app = App::default().examples("pos.pl")?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`Error::IO`] if an examples file cannot be read, or
    /// [`Error::Example`] if an example is not a single literal.
    pub fn examples(self, examples: impl ExampleSource) -> Result<Self> {
        Ok(App {
            examples: Some(examples.into_examples()?),
            ..self
        })
    }

    /// Loads and fully initialises an engine from a JSON config file.
    ///
    /// The config file controls the [`ResolutionConfig`], which `.pl` source files to
    /// load, which predicates are available as body predicates for MIL, and
    /// any training examples. See [`Config`] for the full schema.
    ///
    /// # Errors
    ///
    /// Returns [`Error::IO`] if the file cannot be read, [`Error::Config`] if
    /// the JSON is malformed, or [`Error::Parser`] if any of the loaded `.pl`
    /// files contain a syntax error.
    pub fn from_config_json(path: impl AsRef<str>) -> Result<Self> {
        let path = path.as_ref();
        let config: Config = serde_json::from_str(&fs::read_to_string(path)?)?;

        set_approx_tolerance(config.approx_tolerance_pct);

        let mut app = App {
            predicate_table: PredicateTable::new(),
            prog_heap: ProgramHeap::new(),
            resolution: config.resolution,
            auto: config.auto,
            examples: config.examples,
            parallel: config.parallel,
            namespaces: config.namespaces,
        };

        for predicate_module in STANDARD_MODULES {
            app = app
                .load_module(predicate_module)
                .expect("built-in module should always load");
        }

        for path in config.files {
            let path = Path::new(&path);
            if path.metadata()?.is_dir() {
                app = app.load_dir(path)?;
            } else {
                app = app.load_file(&path)?;
            }
        }
        app.add_body_predicates(config.body_predicates)
    }

    /// Load the configuration from a JSON file
    pub fn load_config(mut self, path: impl AsRef<str>) -> Result<Self> {
        let path = path.as_ref();
        let config: Config = serde_json::from_str(&fs::read_to_string(path)?)?;

        set_approx_tolerance(config.approx_tolerance_pct);

        self.parallel = config.parallel;
        for (name, members) in config.namespaces {
            self = self.namespace(name, members)?;
        }
        self.resolution = config.resolution;
        self.examples = config.examples;
        self.auto = config.auto;
        Ok(self)
    }

    /// Parses a Prolog source string and adds all clauses to the program.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Parser`] if the source contains a syntax error, or
    /// [`Error::NameSpace`] if a meta rule uses a namespace that does not exist.
    pub fn load_code(mut self, code: impl AsRef<str>) -> Result<Self> {
        let syntax_tree = TokenStream::new(tokenise(code)?).parse_all()?;
        execute_tree(
            syntax_tree,
            &mut self.prog_heap,
            &mut self.predicate_table,
            &self.namespaces,
        )?;
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
                    (
                        self.prog_heap.symbols().set_const((*symbol).to_string()),
                        *arity,
                    ),
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
    /// Mark a set of predicates as body predicates available to the MIL engine.
    ///
    /// Body predicates are the background knowledge predicates that the MIL
    /// engine is permitted to use in the body of learned clauses. Any predicate
    /// listed here must already be present in the program (loaded via
    /// [`App::load_code`], [`App::load_file`], or [`App::load_module`]).
    ///
    /// The argument accepts anything that iterates over [`TryIntoBodyPred`]
    /// items, so you can pass a `Vec<BodyPred>` or a string slice directly:
    ///
    /// ```no_run
    /// # use prolog2::app::App;
    /// # let app = App::default();
    /// let app = app.add_body_predicates(&["succ/2", "plus/3"]).unwrap();
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::BodyPred`] if a specification string is
    /// malformed or if a named predicate does not exist in the predicate table.
    pub fn add_body_predicates(
        mut self,
        body_preds: impl IntoIterator<Item = impl TryIntoBodyPred>,
    ) -> Result<Self> {
        for item in body_preds {
            let BodyPred { symbol, arity } = item.try_into_body_pred()?;
            let sym = self.prog_heap.symbols().set_const(symbol.clone());
            self.predicate_table
                .set_body((sym, arity), true)
                .map_err(|e| Error::BodyPred(format!("{e}: {symbol}/{arity}")))?;
        }
        Ok(self)
    }
}

#[cfg(test)]
mod builder_tests {
    use super::App;
    use crate::{ParallelConfig, ResolutionConfig};

    #[test]
    fn app_resolution_updates_the_configuration_so_far() {
        let app = App::default()
            .resolution(|resolution| resolution.max_depth(7))
            .resolution(|resolution| resolution.max_clause(2));
        assert_eq!(
            (app.resolution.max_depth, app.resolution.max_clause),
            (7, 2)
        );
        // The rest is as it was.
        assert_eq!(app.resolution.debug, ResolutionConfig::default().debug);
    }

    #[test]
    fn app_parallel_updates_the_settings_so_far() {
        // From the defaults when none are set, which also turns it on.
        let app = App::default().parallel(|parallel| parallel.pos_noise(1));
        let parallel = app.parallel.expect("parallel learning is on");
        assert_eq!(parallel.pos_noise, 1);
        assert_eq!(
            parallel.final_h_count,
            ParallelConfig::default().final_h_count
        );

        // A second call builds on the first.
        let app = App::default()
            .parallel(|parallel| parallel.pos_noise(1))
            .parallel(|parallel| parallel.neg_noise(2));
        let parallel = app.parallel.unwrap();
        assert_eq!((parallel.pos_noise, parallel.neg_noise), (1, 2));
    }
}
