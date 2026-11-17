//! Running an [`App`]: queries, the interactive loop and parallel learning.

use std::{process::ExitCode, sync::Arc};

use console::Term;
use rustyline::error::ReadlineError;

use super::{app::App, config::ResolutionConfig};
use crate::{
    heap::{Heap, QueryHeap, VarBind::*},
    learners,
    parser::{build_clause, tokenise, TokenStream},
    program::PredicateTable,
    resolution::Proof,
    Error, Result,
};

impl App {
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
            if let Some(solution) = session.next() {
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
    /// retrieved by calling [`Iterator::next`] on it (or by iterating,
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
        let goals = build_clause(literals, None, &mut query_heap, true);
        let mut vars = Vec::new();
        for literal in goals.iter() {
            vars.extend(
                query_heap
                    .term_vars(*literal, false)
                    .iter()
                    // Every variable in a parsed query was named as it was
                    // read, so the heap has a name for each.
                    .map(|&var_id| {
                        (
                            query_heap
                                .var_name(var_id)
                                .expect("a parsed query variable is always named"),
                            var_id,
                        )
                    }),
            );
        }
        let proof = Proof::new(&query_heap, &goals);
        Ok(QuerySession {
            heap: query_heap,
            proof,
            vars,
            predicate_table: &self.predicate_table,
            config: self.resolution,
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
    pub fn run(mut self) -> ExitCode {
        match &self.examples {
            Some(examples) => match self.parallel {
                Some(_) => {
                    self.run_parallel();
                    ExitCode::SUCCESS
                }
                None => self.start_query(examples.to_query()).map_or_else(
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

    /// Learns from the configured examples in parallel MIL pipeline,
    /// (Detailed in [README](https://github.com/JamesTrewern/prolog2/tree/master/README.md))
    /// printing its progress and returning each program found
    /// as Prolog source, or `None` if no valid hypothesis was found.
    ///
    /// # Panics
    ///
    /// If no examples are set.
    pub fn run_parallel(&mut self) -> Option<Vec<String>> {
        let Some(examples) = self.examples.clone() else {
            panic!("Can't start top prog without examples");
        };
        learners::parallel(
            examples,
            &self.predicate_table,
            &mut self.prog_heap,
            self.resolution,
            self.parallel.unwrap_or_default(),
        )
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
/// Solutions are retrieved one at a time by iterating it.
/// `QuerySession` also implements [`Iterator`]`<Item = `[`Solution`]`>`, so it
/// can be used directly in `for` loops or with iterator adaptors.
///
/// Backtracking state is maintained between calls, so each call to
/// `next_solution` resumes the proof search from where it left off.
pub struct QuerySession<'a> {
    heap: QueryHeap<'a>,
    proof: Proof<'a>,
    vars: Vec<(Arc<str>, usize)>, // (variable_name, heap_address)
    predicate_table: &'a PredicateTable,
    config: ResolutionConfig,
}

/// A single solution returned by [`QuerySession`].
#[derive(Debug)]
pub struct Solution {
    /// Variable bindings as `(name, display_string)` pairs, in the order the
    /// variables appear in the query.
    pub bindings: Vec<(Arc<str>, String)>,
    /// Any clauses learned during this proof step via Top Program Construction,
    /// rendered as a Prolog source string. Empty if no hypothesis was formed.
    pub hypothesis: String,
}

impl<'a> Iterator for QuerySession<'a> {
    type Item = Solution;

    fn next(&mut self) -> Option<Self::Item> {
        if self
            .proof
            .prove(&mut self.heap, self.predicate_table, self.config)
        {
            let bindings = self
                .vars
                .iter()
                .map(|(name, var_id)| {
                    (
                        name.clone(),
                        match self.heap.var_deref(*var_id) {
                            VarId(var_id) => self.heap.var_string(var_id),
                            Addr(addr) => self.heap.term_string(addr),
                        },
                    )
                })
                .collect();
            let hypothesis = if self.proof.hypothesis.len() > 0 {
                let clause_strings = self
                    .proof
                    .hypothesis
                    .clause_strings(&mut self.heap, self.predicate_table);
                crate::normalise_hypothesis(&clause_strings).join("\n") + "\n"
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
