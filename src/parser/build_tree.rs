//! Syntax tree construction: parses a token stream into an AST of clauses and terms.

// TODO: Handle sets

use super::term::{
    Str::*,
    Term::{self, *},
};
use super::ParserError;

const INFIX_ORDER: &[&[&str]] = &[
    &[":"],
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &[
        "==", "=\\=", "\\=", "=:=", "=~=", "is", ">", ">=", "<", "=<", "=", "=..",
    ],
];

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum TreeClause {
    Fact(Term),
    Rule(Vec<Term>),
    MetaRule(Vec<Term>),
    MetaFact(Term, Term), // head and set of existentially quantified variables
}

pub(crate) struct TokenStream {
    tokens: Vec<String>,
    index: usize,
    line: usize,
}

impl TokenStream {
    pub(crate) fn new(tokens: Vec<String>) -> Self {
        TokenStream {
            tokens,
            index: 0,
            line: 0,
        }
    }

    pub(super) fn next(&mut self) -> Option<&str> {
        loop {
            if self.index == self.tokens.len() {
                return None;
            }
            match self.tokens[self.index].as_str() {
                "\n" => {
                    self.index += 1;
                    self.line += 1
                }
                token => {
                    self.index += 1;
                    return Some(token);
                }
            }
        }
    }

    pub(super) fn peek(&self) -> Option<&str> {
        let mut index = self.index;
        loop {
            if index == self.tokens.len() {
                return None;
            }
            match self.tokens[index].as_str() {
                "\n" => {
                    index += 1;
                }
                token => {
                    return Some(token);
                }
            }
        }
    }
}

/// A meta variable declaration: `P`, or `P:namespace`.
fn is_meta_var(term: &Term) -> bool {
    match term {
        Variable(_) => true,
        Str(Comp, terms) => {
            matches!(&terms[..], [Constant(op), Variable(_), Constant(_)] if op == ":")
        }
        _ => false,
    }
}

fn is_operator(token: &str) -> bool {
    INFIX_ORDER.iter().any(|group| group.contains(&token))
}

fn infix_order(operator: &str) -> usize {
    INFIX_ORDER
        .iter()
        .position(|ops| ops.contains(&operator))
        .unwrap()
}

fn resolve_infix(term_stack: &mut Vec<Term>, op_stack: &mut Vec<String>, max_prescendence: usize) {
    while let Some(p) = op_stack.last().map(|operator| infix_order(&operator)) {
        if p > max_prescendence {
            break;
        }
        let op = Constant(op_stack.pop().unwrap());
        let right = term_stack.pop().unwrap();
        let left = term_stack.pop().unwrap();
        term_stack.push(Str(Comp, vec![op, left, right]));
    }
}

impl TokenStream {
    fn expect(&mut self, value: &str) -> Result<(), ParserError> {
        match self.next() {
            Some(token) if token == value => Ok(()),
            Some(token) => Err(ParserError::Expected {
                expected: value.into(),
                got: Some(token.into()),
            }),
            None => Err(ParserError::Expected {
                expected: value.into(),
                got: None,
            }),
        }
    }

    fn consume_args(&mut self) -> Result<Vec<Term>, ParserError> {
        let mut args = Vec::new();
        loop {
            args.push(self.parse_expression()?);
            match self.peek() {
                Some(")" | "|" | "]" | "}") => return Ok(args), // TODO: end consuming args based on certain conditions, don't accept all end tokens
                Some(",") => {
                    self.next();
                }
                Some(token) => {
                    return Err(ParserError::UnexpectedToken {
                        token: token.to_string(),
                    })
                }
                None => return Err(ParserError::UnexpectedEof),
            }
        }
    }

    pub(super) fn parse_term(&mut self) -> Result<Term, ParserError> {
        match self.peek().ok_or(ParserError::UnexpectedEof)? {
            "{" => {
                self.next();
                let args = self.consume_args()?;
                if self.next() == Some("}") {
                    Ok(Str(Set, args))
                } else {
                    Err(ParserError::MalformedSet)
                }
            }
            "[" => {
                self.next();
                let head = self.consume_args()?;
                match self.next().ok_or(ParserError::UnexpectedEof)? {
                    "|" => {
                        let tail = Box::new(self.parse_expression()?);
                        self.expect("]")?;
                        Ok(List(head, tail))
                    }
                    "]" => Ok(List(head, Box::new(EmptyList))),
                    token => {
                        return Err(ParserError::UnexpectedToken {
                            token: token.to_string(),
                        })
                    }
                }
            }
            "[]" => {
                self.next();
                Ok(EmptyList)
            }
            "{}" => {
                self.next();
                Ok(EmptySet)
            }
            "()" => {
                self.next();
                Ok(Str(Tup, vec![]))
            }
            "(" => {
                // Grouped expression or tuple
                self.next();
                let mut args = self.consume_args()?;
                self.expect(")")?;
                if args.len() == 1 {
                    Ok(args.pop().unwrap())
                } else {
                    Ok(Str(Tup, args))
                }
            }
            token if is_operator(token) => {
                // Handle prefix operators (unary minus, unary plus)
                let op = self.next().unwrap().to_string();
                let operand = self.parse_term()?;
                Ok(Str(Comp, vec![Constant(op), operand]))
            }
            token => {
                let token = token.to_string();
                match Term::parse_unit(self.next().unwrap()) {
                    Some(functor @ (Constant(_) | Variable(_))) => {
                        if self.peek() == Some("(") {
                            self.next();
                            let mut args = self.consume_args()?;
                            args.insert(0, functor);
                            self.expect(")")?;
                            Ok(Str(Comp, args))
                        } else {
                            Ok(functor)
                        }
                    }
                    Some(unit) => Ok(unit),
                    None => Err(ParserError::UnexpectedToken {
                        token: token.to_string(),
                    }),
                }
            }
        }
    }

    pub(super) fn parse_expression(&mut self) -> Result<Term, ParserError> {
        let mut op_stack = Vec::<String>::new();
        let mut term_stack = Vec::<Term>::new();
        loop {
            //Consume a term
            if self.peek() == Some("(") {
                //Grouped Expression with brackets or tuple
                self.next();
                let mut args = self.consume_args()?;
                self.expect(")")?;
                if args.len() == 1 {
                    term_stack.push(args.pop().unwrap());
                } else {
                    term_stack.push(Str(Tup, args));
                }
            } else {
                term_stack.push(self.parse_term()?);
            }

            //Is next token an operator
            match self.peek() {
                Some(operator) if is_operator(operator) => {
                    resolve_infix(&mut term_stack, &mut op_stack, infix_order(operator));
                    op_stack.push(operator.into());
                    self.next();
                }
                // Some(token) => {println!("Token: {token}");break;}
                _ => break,
            }
        }

        resolve_infix(&mut term_stack, &mut op_stack, INFIX_ORDER.len());
        term_stack.pop().ok_or(ParserError::UnexpectedEof)
    }

    fn parse_body_literals(&mut self) -> Result<Vec<Term>, ParserError> {
        let mut body = Vec::new();
        loop {
            body.push(self.parse_expression()?);
            match self.next() {
                Some(",") => continue,
                Some(".") => break,
                Some(token) => {
                    return Err(ParserError::Expected {
                        expected: "',' or '.'".into(),
                        got: Some(token.to_string()),
                    })
                }
                None => return Err(ParserError::UnexpectedEof),
            }
        }
        Ok(body)
    }

    pub(super) fn parse_clause(&mut self) -> Result<Option<TreeClause>, ParserError> {
        match self.peek() {
            None => return Ok(None),
            Some(_) => {
                let mut literals = vec![self.parse_expression()?];
                match self.next() {
                    Some(":-") => {
                        literals.append(&mut self.parse_body_literals()?);
                        let len = literals.len();
                        let meta_rule = match literals.last() {
                            // Case 1: ...{P,Q,R}. — all constrained
                            Some(Str(Set, eq_vars)) => {
                                if eq_vars.iter().any(|eq_var| !is_meta_var(eq_var)) {
                                    return Err(ParserError::MalformedMetaRule { detail: format!("incorrectly formatted existentially quantified variables: {:?}", eq_vars) });
                                }
                                true
                            }
                            // Case 2 or 3: last is [Q1,Q2] — unconstrained vars list
                            Some(List(vars, tail)) if matches!(tail.as_ref(), EmptyList) => {
                                if vars.iter().any(|v| !is_meta_var(v)) {
                                    return Err(ParserError::MalformedMetaRule { detail: format!("unconstrained variable list should only contain variables, got {:?}", vars) });
                                }
                                // Case 2: ...{P},[Q1,Q2]. — check if second-to-last is a constrained set
                                if len >= 2 {
                                    if let Str(Set, eq_vars) = &literals[len - 2] {
                                        if eq_vars.iter().any(|eq_var| !is_meta_var(eq_var)) {
                                            return Err(ParserError::MalformedMetaRule { detail: format!("incorrectly formatted existentially quantified variables: {:?}", eq_vars) });
                                        }
                                    }
                                }
                                // Case 3: ...[Q1,Q2]. — no constrained set, just unconstrained list
                                true
                            }
                            _ => false,
                        };
                        if meta_rule {
                            Ok(Some(TreeClause::MetaRule(literals)))
                        } else {
                            Ok(Some(TreeClause::Rule(literals)))
                        }
                    }
                    Some(",") => {
                        // Could be a MetaFact: Head, {EQVars}.
                        let meta_data = self.parse_expression()?;
                        if let Str(Set, eq_vars) = &meta_data {
                            if eq_vars.iter().any(|eq_var| !is_meta_var(eq_var)) {
                                return Err(ParserError::MalformedMetaRule { detail: format!("incorrectly formatted existentially quantified variables: {:?}", eq_vars) });
                            }
                            self.expect(".")?;
                            Ok(Some(TreeClause::MetaFact(
                                literals.pop().unwrap(),
                                meta_data,
                            )))
                        } else {
                            Err(ParserError::MalformedMetaRule { detail: format!("expected set of existentially quantified variables after comma in meta-fact, got {:?}", meta_data) })
                        }
                    }
                    Some(".") => Ok(Some(TreeClause::Fact(literals[0].clone()))),
                    Some(token) => Err(ParserError::Expected {
                        expected: "'.' or ',' or ':-'".into(),
                        got: Some(token.to_string()),
                    }),
                    None => Err(ParserError::UnexpectedEof),
                }
            }
        }
    }

    pub(crate) fn parse_goals(&mut self) -> Result<Vec<Term>, ParserError> {
        let mut literals = vec![self.parse_expression()?];
        loop {
            match self.next() {
                Some(",") => literals.push(self.parse_expression()?),
                Some(".") => break,
                Some(token) => {
                    return Err(ParserError::UnexpectedToken {
                        token: token.to_string(),
                    })
                }
                None => return Err(ParserError::UnexpectedEof),
            }
        }

        Ok(literals)
    }

    pub(crate) fn parse_all(&mut self) -> Result<Vec<TreeClause>, ParserError> {
        let mut clauses = Vec::<TreeClause>::new();
        loop {
            match self.parse_clause() {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => return Ok(clauses),
                Err(msg) => {
                    return Err(ParserError::AtLine {
                        line: self.line,
                        cause: Box::new(msg),
                    })
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        super::{term::Str::*, tokeniser::tokenise, ParserError},
        {Term::*, TokenStream, TreeClause},
    };
    #[test]
    fn parse_number_term() {
        //Positive Integer
        let text = tokenise("10").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Int(10));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Int(10));

        //Negative Integer
        let text = tokenise("-10").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Int(-10));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Int(-10));

        //Positive Float
        let text = tokenise("1.01").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Float(1.01));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Float(1.01));

        //Negative Float
        let text = tokenise("-1.01").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Float(-1.01));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Float(-1.01));
    }

    #[test]
    fn parse_constant_term() {
        let text = tokenise("constant").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Constant("constant".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Constant("constant".into()));

        let text = tokenise("constant_1").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Constant("constant_1".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Constant("constant_1".into()));

        let text = tokenise("'file/path'").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Constant("file/path".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Constant("file/path".into()));

        let text = tokenise("'c*o/n\"s-t'").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Constant("c*o/n\"s-t".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Constant("c*o/n\"s-t".into()));
    }

    #[test]
    fn parse_variable_term() {
        let text = tokenise("Var").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Variable("Var".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Variable("Var".into()));

        let text = tokenise("VAR_Under").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Variable("VAR_Under".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Variable("VAR_Under".into()));

        let text = tokenise("VAR10").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Variable("VAR10".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Variable("VAR10".into()));

        let text = tokenise("VAR_Under2").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Variable("VAR_Under2".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Variable("VAR_Under2".into()));
    }

    #[test]
    fn parse_string_term() {
        let text = tokenise("\"A String\"").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, TermString("A String".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, TermString("A String".into()));

        let text = tokenise("\"A \\\"String\"").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, TermString("A \"String".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, TermString("A \"String".into()));

        let text = tokenise("\"A *+-=: String\"").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, TermString("A *+-=: String".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, TermString("A *+-=: String".into()));
    }

    #[test]
    fn parse_atom_term() {
        let p = Constant("p".into());
        let q = Variable("Q".into());
        let x = Variable("X".into());
        let y = Variable("Y".into());
        let a = Constant("a".into());
        let b = Constant("b".into());

        let text = tokenise("p(X,a)").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Str(Comp, vec![p.clone(), x.clone(), a.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Comp, vec![p.clone(), x.clone(), a.clone()]));

        let text = tokenise("Q(b,Y)").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Str(Comp, vec![q.clone(), b.clone(), y.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Comp, vec![q.clone(), b.clone(), y.clone()]));
    }

    #[test]
    fn parse_list_term() {
        let a = Constant("a".into());
        let b = Constant("b".into());
        let c = Constant("c".into());
        let t = Variable("T".into());
        let p = Constant("p".into());

        let text = tokenise("[a,b,c]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            List(vec![a.clone(), b.clone(), c.clone()], Box::new(EmptyList))
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            List(vec![a.clone(), b.clone(), c.clone()], Box::new(EmptyList))
        );

        let text = tokenise("[a,b,c|[]]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            List(vec![a.clone(), b.clone(), c.clone()], Box::new(EmptyList))
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            List(vec![a.clone(), b.clone(), c.clone()], Box::new(EmptyList))
        );

        let text = tokenise("[a|T]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, List(vec![a.clone()], Box::new(t.clone())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, List(vec![a.clone()], Box::new(t.clone())));

        let text = tokenise("[a,[b,c]]").unwrap();
        let sub_list = List(vec![b.clone(), c.clone()], Box::new(EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            List(vec![a.clone(), sub_list.clone()], Box::new(EmptyList))
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            List(vec![a.clone(), sub_list.clone()], Box::new(EmptyList))
        );

        let text = tokenise("p([a,[b,c|T]])").unwrap();
        let sub_list = List(vec![b.clone(), c.clone()], Box::new(t.clone()));
        let list = List(vec![a.clone(), sub_list.clone()], Box::new(EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Str(Comp, vec![p.clone(), list.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Comp, vec![p.clone(), list]));

        let text = tokenise("[]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, EmptyList);
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, EmptyList);
    }

    #[test]
    fn parse_set_term() {
        let a = Constant("a".into());
        let b = Constant("b".into());
        let c = Constant("c".into());
        let p = Constant("p".into());

        let abc = Str(Set, vec![a.clone(), b.clone(), c.clone()]);

        let text = tokenise("{a,b,c}").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, abc.clone());
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("p({a,b,c})").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Str(Comp, vec![p.clone(), abc.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Comp, vec![p.clone(), abc.clone()]));

        let text = tokenise("{a,{b,c}}").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Str(Set, vec![a.clone(), Str(Set, vec![b.clone(), c.clone()])])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Str(Set, vec![a.clone(), Str(Set, vec![b.clone(), c.clone()])])
        );

        let text = tokenise("{a,{}}").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Str(Set, vec![a.clone(), EmptySet]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Set, vec![a.clone(), EmptySet]));
    }

    #[test]
    fn parse_tuple() {
        let a = Constant("a".into());
        let b = Constant("b".into());
        let c = Constant("c".into());
        let p = Constant("p".into());

        let abc = Str(Tup, vec![a.clone(), b.clone(), c.clone()]);
        let bc = Str(Tup, vec![b.clone(), c.clone()]);

        let text = tokenise("(a,b,c)").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("(a,(b,c))").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Tup, vec![a.clone(), bc.clone()]));

        //This test fails
        let text = tokenise("(a,())").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Tup, vec![a.clone(), Str(Tup, vec![])]));

        let text = tokenise("p((a,b,c))").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Str(Comp, vec![p, abc.clone()]));
    }

    // TODO: Improve error messaging for unclosed structures
    #[test]
    fn unclosed_atom() {
        let mut tokens = TokenStream::new(tokenise("p(X,Y").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,Y.").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }

        let mut tokens = TokenStream::new(tokenise("p(X,(Y)").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,(Y).").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }
    }

    #[test]
    fn unclosed_list() {
        let mut tokens = TokenStream::new(tokenise("[X,Y").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("[X,Y.").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }

        let mut tokens = TokenStream::new(tokenise("[X,[Y]").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("[X,[Y].").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }
    }

    #[test]
    fn unclosed_set() {
        let mut tokens = TokenStream::new(tokenise("{X,Y").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("{X,Y.").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }

        let mut tokens = TokenStream::new(tokenise("{X,{Y}").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("{X,{Y}.").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }
    }

    #[test]
    fn unclosed_tuple() {
        let mut tokens = TokenStream::new(tokenise("(X,Y").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("(X,Y.").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }

        let mut tokens = TokenStream::new(tokenise("(X,(Y)").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert!(matches!(message, ParserError::UnexpectedEof)),
        }

        let mut tokens = TokenStream::new(tokenise("(X,(Y).").unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => {
                assert!(matches!(message, ParserError::UnexpectedToken { token } if token == "."))
            }
        }
    }

    #[test]
    fn infix_order() {
        let x = Variable("X".into());
        let _y = Variable("Y".into());
        let one = Int(1);
        let two = Int(2);
        let three = Int(3);
        let one_and_half = Float(1.5);
        let plus = Constant("+".into());
        let _minus = Constant("-".into());
        let divide = Constant("/".into());
        let _times = Constant("*".into());
        let power = Constant("**".into());
        let eqauls = Constant("=:=".into());

        let text = tokenise("X =:= 1 + 2 / 1.5**3").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Str(
                Comp,
                vec![
                    eqauls,
                    x.clone(),
                    Str(
                        Comp,
                        vec![
                            plus.clone(),
                            one.clone(),
                            Str(
                                Comp,
                                vec![
                                    divide.clone(),
                                    two.clone(),
                                    Str(
                                        Comp,
                                        vec![power.clone(), one_and_half.clone(), three.clone()]
                                    )
                                ]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn grouped_expression() {
        let x = Variable("X".into());
        let _y = Variable("Y".into());
        let one = Int(1);
        let two = Int(2);
        let three = Int(3);
        let one_and_half = Float(1.5);
        let plus = Constant("+".into());
        let _minus = Constant("-".into());
        let divide = Constant("/".into());
        let _times = Constant("*".into());
        let power = Constant("**".into());
        let equals = Constant("=:=".into());

        let text = tokenise("X =:= 1 + (2 / 1.5)**3").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Str(
                Comp,
                vec![
                    equals,
                    x,
                    Str(
                        Comp,
                        vec![
                            plus,
                            one,
                            Str(
                                Comp,
                                vec![power, Str(Comp, vec![divide, two, one_and_half]), three]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn tuple_or_grouped_expression() {
        let x = Variable("X".into());
        let y = Variable("Y".into());
        let a = Constant("a".into());
        let one = Int(1);
        let two = Int(2);
        let three = Int(3);
        let one_and_half = Float(1.5);
        let plus = Constant("+".into());
        let _minus = Constant("-".into());
        let divide = Constant("/".into());
        let _times = Constant("*".into());
        let power = Constant("**".into());
        let equals = Constant("=:=".into());

        let text = tokenise("(a,X =:= 1 + (2 / 1.5)**(3,Y))").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Str(
                Tup,
                vec![
                    a,
                    Str(
                        Comp,
                        vec![
                            equals,
                            x,
                            Str(
                                Comp,
                                vec![
                                    plus,
                                    one,
                                    Str(
                                        Comp,
                                        vec![
                                            power,
                                            Str(Comp, vec![divide, two, one_and_half]),
                                            Str(Tup, vec![three, y])
                                        ]
                                    )
                                ]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn parse_rule() {
        let mut token_stream = TokenStream::new(tokenise("gt1(X):-X>1.").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Str(Comp, vec![Constant("gt1".into()), Variable("X".into())]);
        let body = Str(
            Comp,
            vec![Constant(">".into()), Variable("X".into()), Int(1)],
        );

        assert_eq!(clause, TreeClause::Rule(vec![head, body]));
        // assert_eq!(token_stream.parse_clause().unwrap(),None);
    }

    #[test]
    fn parse_fact() {
        let mut token_stream = TokenStream::new(tokenise("man(plato).").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Str(Comp, vec![Constant("man".into()), Constant("plato".into())]);

        assert_eq!(clause, TreeClause::Fact(head));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule() {
        let mut token_stream = TokenStream::new(tokenise("P(X,Y):-Q(X,Y),{P,Q}.").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Str(
            Comp,
            vec![
                Variable("P".into()),
                Variable("X".into()),
                Variable("Y".into()),
            ],
        );
        let body = Str(
            Comp,
            vec![
                Variable("Q".into()),
                Variable("X".into()),
                Variable("Y".into()),
            ],
        );
        let meta_data = Str(Set, vec![Variable("P".into()), Variable("Q".into())]);

        assert_eq!(clause, TreeClause::MetaRule(vec![head, body, meta_data]));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule_with_unconstrained_list() {
        // {El},[Q1,Q2] — El is constrained, Q1 and Q2 are unconstrained
        let mut token_stream =
            TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),{El},[Q1,Q2].").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Str(
            Comp,
            vec![
                Constant("edge".into()),
                Variable("El".into()),
                Variable("Q1".into()),
                Variable("Q2".into()),
            ],
        );
        let body1 = Str(Comp, vec![Constant("q".into()), Variable("Q1".into())]);
        let body2 = Str(Comp, vec![Constant("q".into()), Variable("Q2".into())]);
        let constrained = Str(Set, vec![Variable("El".into())]);
        let unconstrained = List(
            vec![Variable("Q1".into()), Variable("Q2".into())],
            Box::new(EmptyList),
        );

        assert_eq!(
            clause,
            TreeClause::MetaRule(vec![head, body1, body2, constrained, unconstrained])
        );
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule_list_only() {
        // [Q1,Q2] only — no constrained variables
        let mut token_stream =
            TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),[El,Q1,Q2].").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Str(
            Comp,
            vec![
                Constant("edge".into()),
                Variable("El".into()),
                Variable("Q1".into()),
                Variable("Q2".into()),
            ],
        );
        let body1 = Str(Comp, vec![Constant("q".into()), Variable("Q1".into())]);
        let body2 = Str(Comp, vec![Constant("q".into()), Variable("Q2".into())]);
        let unconstrained = List(
            vec![
                Variable("El".into()),
                Variable("Q1".into()),
                Variable("Q2".into()),
            ],
            Box::new(EmptyList),
        );

        assert_eq!(
            clause,
            TreeClause::MetaRule(vec![head, body1, body2, unconstrained])
        );
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_fact() {
        let mut token_stream = TokenStream::new(tokenise("Map([],[],X),{Map}.").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Str(
            Comp,
            vec![
                Variable("Map".into()),
                EmptyList,
                EmptyList,
                Variable("X".into()),
            ],
        );
        let meta_data = Str(Set, vec![Variable("Map".into())]);

        assert_eq!(clause, TreeClause::MetaFact(head, meta_data));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_directive() {
        let mut token_stream = TokenStream::new(tokenise("test(a),goal([_|T],1).").unwrap());
        let clause = token_stream.parse_goals().unwrap();
        let body = Str(Comp, vec![Constant("test".into()), Constant("a".into())]);
        let body2 = Str(
            Comp,
            vec![
                Constant("goal".into()),
                List(vec![AnonVar], Box::new(Variable("T".into()))),
                Int(1),
            ],
        );

        assert_eq!(clause, vec![body, body2]);
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_all_clauses() {
        let text = "gt1(X):-X>1.\nman(plato).\nP(X,Y):-\n\tQ(X,Y),\n\t{P,Q}.".to_string();
        let mut token_stream = TokenStream::new(tokenise(text).unwrap());
        let clauses = token_stream.parse_all().unwrap();

        let head = Str(Comp, vec![Constant("gt1".into()), Variable("X".into())]);
        let body = Str(
            Comp,
            vec![Constant(">".into()), Variable("X".into()), Int(1)],
        );
        assert_eq!(clauses[0], TreeClause::Rule(vec![head, body]));

        let head = Str(Comp, vec![Constant("man".into()), Constant("plato".into())]);
        assert_eq!(clauses[1], TreeClause::Fact(head));

        let head = Str(
            Comp,
            vec![
                Variable("P".into()),
                Variable("X".into()),
                Variable("Y".into()),
            ],
        );
        let body = Str(
            Comp,
            vec![
                Variable("Q".into()),
                Variable("X".into()),
                Variable("Y".into()),
            ],
        );
        let meta_data = Str(Set, vec![Variable("P".into()), Variable("Q".into())]);
        assert_eq!(
            clauses[2],
            TreeClause::MetaRule(vec![head, body, meta_data])
        );
    }
}
