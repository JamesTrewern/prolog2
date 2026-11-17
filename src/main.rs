use std::process::ExitCode;

use prolog2::app::App;

fn config_path() -> String {
    std::env::args()
        .nth(1)
        .unwrap_or_else(|| "config.json".to_string())
}

fn main() -> ExitCode {
    match App::from_config_json(config_path()) {
        Ok(app) => app.run(),
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}
