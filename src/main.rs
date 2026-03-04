use std::process::ExitCode;

use prolog2::{
    app::App,
    predicate_modules::{MATHS, META_PREDICATES},
};

fn main() -> ExitCode {
    App::from_args()
        .add_module(&MATHS)
        .add_module(&META_PREDICATES)
        .run()
}
