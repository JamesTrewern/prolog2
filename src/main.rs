use std::process::ExitCode;

use prolog2::{
    app::App,
};

fn setup_path() -> String {
    std::env::args()
        .nth(1)
        .unwrap_or_else(|| "setup.json".to_string())
}

fn main() -> ExitCode {
    App::from_setup_json(setup_path()).run()
}
