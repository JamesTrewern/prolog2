use crate::interface::{parser::{parse_clause, parse_goals, tokenise}, term::Term};

#[test]
fn parse_fact() {
    let terms = parse_goals(&tokenise("p(a,b).")).unwrap();
    assert_eq!(
        terms[0],
        Term::STR(
            [
                Term::CON("p".into()),
                Term::CON("a".into()),
                Term::CON("b".into())
            ]
            .into()
        )
    );
}

#[test]
fn parse_simple_clause() {
    let terms = parse_goals(&tokenise("p(X,Y):-q(X,Y).")).unwrap();
    assert_eq!(
        terms[0],
        Term::STR(
            [
                Term::CON("p".into()),
                Term::VAR("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
    assert_eq!(
        terms[1],
        Term::STR(
            [
                Term::CON("q".into()),
                Term::VAR("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
}

#[test]
fn parse_clause_with_list() {
    let terms = parse_goals(&tokenise("p(X,Y):-q([X,Y]).")).unwrap();
    assert_eq!(
        terms[0],
        Term::STR(
            [
                Term::CON("p".into()),
                Term::VAR("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
    assert_eq!(
        terms[1],
        Term::STR(
            [
                Term::CON("q".into()),
                Term::LIS([Term::VAR("X".into()), Term::VAR("Y".into())].into(), false)
            ]
            .into()
        )
    );
}

#[test]
fn parse_clause_with_float() {
    let terms = parse_goals(&tokenise("p(X):-q(X,2.3).")).unwrap();
    assert_eq!(
        terms[0],
        Term::STR([Term::CON("p".into()), Term::VAR("X".into()),].into())
    );
    assert_eq!(
        terms[1],
        Term::STR([Term::CON("q".into()), Term::VAR("X".into()), Term::FLT(2.3)].into())
    );
}

#[test]
fn parse_clause_with_infix() {
    let terms = parse_goals(&tokenise("p(X,Y,Z):- Z is X**2/Y**2.")).unwrap();

    assert_eq!(
        terms[0],
        Term::STR(
            [
                Term::CON("p".into()),
                Term::VAR("X".into()),
                Term::VAR("Y".into()),
                Term::VAR("Z".into())
            ]
            .into()
        )
    );
    assert_eq!(
        terms[1],
        Term::STR(
            [
                Term::CON("is".into()),
                Term::VAR("Z".into()),
                Term::STR(
                    [
                        Term::CON("/".into()),
                        Term::STR(
                            [Term::CON("**".into()), Term::VAR("X".into()), Term::INT(2)].into()
                        ),
                        Term::STR(
                            [Term::CON("**".into()), Term::VAR("Y".into()), Term::INT(2)].into()
                        ),
                    ]
                    .into()
                )
            ]
            .into()
        )
    );
}

#[test]
fn parse_meta_no_uq() {
    let clause = parse_clause(&tokenise("P(X,Y):-Q(X,Y){}.")).unwrap();

    assert!(clause.meta);

    assert_eq!(
        clause[0],
        Term::STR(
            [
                Term::VAR("P".into()),
                Term::VAR("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
    assert_eq!(
        clause[1],
        Term::STR(
            [
                Term::VAR("Q".into()),
                Term::VAR("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
}

#[test]
fn parse_meta_with_uq() {
    let clause = parse_clause(&tokenise("P(X,Y):-Q(X,Y) {X}.")).unwrap();

    assert!(clause.meta);

    assert_eq!(
        clause[0],
        Term::STR(
            [
                Term::VAR("P".into()),
                Term::VARUQ("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
    assert_eq!(
        clause[1],
        Term::STR(
            [
                Term::VAR("Q".into()),
                Term::VARUQ("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
}

#[test]
fn parse_meta_with_list() {
    let clause = parse_clause(&tokenise("P(X,Y):-Q([X,Y]) {X}.")).unwrap();
    assert!(clause.meta);
    assert_eq!(
        clause[0],
        Term::STR(
            [
                Term::VAR("P".into()),
                Term::VARUQ("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
    assert_eq!(
        clause[1],
        Term::STR(
            [
                Term::VAR("Q".into()),
                Term::LIS(
                    [Term::VARUQ("X".into()), Term::VAR("Y".into())].into(),
                    false
                )
            ]
            .into()
        )
    );
}

#[test]
fn parse_meta_with_list_explicit_uq_tail() {
    let clause = parse_clause(&tokenise("P(X,Y):-Q([X,Y|Z]) {X,Z}.")).unwrap();

    assert!(clause.meta);

    assert_eq!(
        clause[0],
        Term::STR(
            [
                Term::VAR("P".into()),
                Term::VARUQ("X".into()),
                Term::VAR("Y".into())
            ]
            .into()
        )
    );
    assert_eq!(
        clause[1],
        Term::STR(
            [
                Term::VAR("Q".into()),
                Term::LIS(
                    [
                        Term::VARUQ("X".into()),
                        Term::VAR("Y".into()),
                        Term::VARUQ("Z".into())
                    ]
                    .into(),
                    true
                )
            ]
            .into()
        )
    );
}

#[test]
fn parse_meta_with_infix() {
    let clause = parse_clause(&tokenise("p(X,Y,Z):- Z is X**2/Y**2 {X,Y,Z}.")).unwrap();

    assert!(clause.meta);

    println!("{:?}", clause.literals);

    assert_eq!(
        clause[0],
        Term::STR(
            [
                Term::CON("p".into()),
                Term::VARUQ("X".into()),
                Term::VARUQ("Y".into()),
                Term::VARUQ("Z".into())
            ]
            .into()
        )
    );
    assert_eq!(
        clause[1],
        Term::STR(
            [
                Term::CON("is".into()),
                Term::VARUQ("Z".into()),
                Term::STR(
                    [
                        Term::CON("/".into()),
                        Term::STR(
                            [
                                Term::CON("**".into()),
                                Term::VARUQ("X".into()),
                                Term::INT(2)
                            ]
                            .into()
                        ),
                        Term::STR(
                            [
                                Term::CON("**".into()),
                                Term::VARUQ("Y".into()),
                                Term::INT(2)
                            ]
                            .into()
                        ),
                    ]
                    .into()
                )
            ]
            .into()
        )
    );
}