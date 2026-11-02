//! Two engines in one process keep separate symbol spaces.
//!
//! Each [`App`] owns its program heap, and each program heap owns the symbol
//! table its cells are interpreted against.
//!
//! These guard that isolation; they are not regressions. When the table was a
//! global static the sharing was largely invisible from out here, because the
//! constant table only ever grew -- so an id meant the same thing in both
//! engines -- and each string literal took a fresh index. What it actually
//! broke was variable naming, which needs the program heap to observe and so
//! is covered by `program::clause` instead, plus growth that no engine could
//! reclaim. The value of these is that they are cheap and they fail loudly if
//! the table ever drifts back toward being shared.

use prolog2::app::App;

fn solutions(app: &App, query: &str) -> Vec<String> {
    let mut session = app.query_session(query).unwrap();
    let mut out = Vec::new();
    while let Some(solution) = session.next() {
        for (name, value) in &solution.bindings {
            out.push(format!("{name}={value}"));
        }
    }
    out.sort();
    out
}

#[test]
fn two_engines_resolve_their_own_constants() {
    // Deliberately disjoint symbols: if the two engines shared one table,
    // `beta` and `delta` would land on ids the other engine also uses.
    let first = App::default().load_code("p(alpha). p(beta).").unwrap();
    let second = App::default().load_code("q(gamma). q(delta).").unwrap();

    assert_eq!(solutions(&first, "p(X)."), ["X=alpha", "X=beta"]);
    assert_eq!(solutions(&second, "q(X)."), ["X=delta", "X=gamma"]);
}

#[test]
fn the_same_name_in_two_engines_is_two_symbols() {
    // Same spelling, different engines, different facts. Interning order
    // differs between them, so a shared table would give one engine an id
    // minted against the other's program.
    let first = App::default().load_code("fact(shared, one).").unwrap();
    let second = App::default()
        .load_code("other(x). fact(shared, two).")
        .unwrap();

    assert_eq!(solutions(&first, "fact(shared, X)."), ["X=one"]);
    assert_eq!(solutions(&second, "fact(shared, X)."), ["X=two"]);
}

#[test]
fn engines_can_be_queried_from_separate_threads() {
    let first = App::default().load_code("p(alpha). p(beta).").unwrap();
    let second = App::default().load_code("q(gamma). q(delta).").unwrap();

    std::thread::scope(|scope| {
        let a = scope.spawn(|| solutions(&first, "p(X)."));
        let b = scope.spawn(|| solutions(&second, "q(X)."));
        assert_eq!(a.join().unwrap(), ["X=alpha", "X=beta"]);
        assert_eq!(b.join().unwrap(), ["X=delta", "X=gamma"]);
    });
}

#[test]
fn string_literals_are_per_engine() {
    // String literals are stored by index into a per-program vector, which a
    // shared table would interleave between engines.
    let first = App::default().load_code(r#"greeting("hello")."#).unwrap();
    let second = App::default().load_code(r#"greeting("goodbye")."#).unwrap();

    assert_eq!(solutions(&first, "greeting(X)."), [r#"X="hello""#]);
    assert_eq!(solutions(&second, "greeting(X)."), [r#"X="goodbye""#]);
}
