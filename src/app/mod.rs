//! The engine: its configuration, how it is built and how it is run.

// `app::app` keeps `App` in a file of its own name.
#[allow(clippy::module_inception)]
mod app;
mod config;
mod run;

pub use app::App;
pub use config::{BodyPred, Config, ExampleSource, Examples, ParallelConfig, ResolutionConfig, TryIntoBodyPred};
pub use run::{QuerySession, Solution};
