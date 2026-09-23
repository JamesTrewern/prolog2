//! Syntax tree construction: parses a token stream into an AST of clauses and terms.

// TODO: Handle sets

use super::term::{Str, Term};
use super::ParserError;

const INFIX_ORDER: &[&[&str]] = &[
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &[
        "==", "=\\=", "\\=", "=:=", "=~=", "is", ">", ">=", "<", "=<", "=", "=..",
    ],
];

#[derive(Debug, PartialEq, Clone)]
pub enum TreeClause {
    Fact(Term),
    Rule(Vec<Term>),
    MetaRule(Vec<Term>),
    MetaFact(Term, Term), // head and set of existentially quantified variables
}

pub struct TokenStream {
    tokens: Vec<String>,
    index: usize,
    line: usize,
}

impl TokenStream {
    pub fn new(tokens: Vec<String>) -> Self {
        TokenStream {
            tokens,
            index: 0,
            line: 0,
        }
    }

    pub fn next(&mut self) -> Option<&str> {
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

    pub fn peek(&self) -> Option<&str> {
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
        let op = Term::Constant(op_stack.pop().unwrap());
        let right = term_stack.pop().unwrap();
        let left = term_stack.pop().unwrap();
        term_stack.push(Term::Str(Str::Comp, vec![op, left, right]));
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
                    Ok(Term::Str(Str::Set, args))
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
                        Ok(Term::List(head, tail))
                    }
                    "]" => Ok(Term::List(head, Box::new(Term::EmptyList))),
                    token => {
                        return Err(ParserError::UnexpectedToken {
                            token: token.to_string(),
                        })
                    }
                }
            }
            "[]" => {
                self.next();
                Ok(Term::EmptyList)
            }
            "{}" => {
                self.next();
                Ok(Term::EmptySet)
            }
            "()" => {
                self.next();
                Ok(Term::Str(Str::Tup, vec![]))
            }
            "(" => {
                // Grouped expression or tuple
                self.next();
                let mut args = self.consume_args()?;
                self.expect(")")?;
                if args.len() == 1 {
                    Ok(args.pop().unwrap())
                } else {
                    Ok(Term::Str(Str::Tup, args))
                }
            }
            token if is_operator(token) => {
                // Handle prefix operators (unary minus, unary plus)
                let op = self.next().unwrap().to_string();
                let operand = self.parse_term()?;
                Ok(Term::Str(Str::Comp, vec![Term::Constant(op), operand]))
            }
            token => {
                let token = token.to_string();
                match Term::parse_unit(self.next().unwrap()) {
                    Some(functor @ (Term::Constant(_) | Term::Variable(_))) => {
                        if self.peek() == Some("(") {
                            self.next();
                            let mut args = self.consume_args()?;
                            args.insert(0, functor);
                            self.expect(")")?;
                            Ok(Term::Str(Str::Comp, args))
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
                    term_stack.push(Term::Str(Str::Tup, args));
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

    pub fn parse_clause(&mut self) -> Result<Option<TreeClause>, ParserError> {
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
                            Some(Term::Str(Str::Set, eq_vars)) => {
                                if eq_vars
                                    .iter()
                                    .any(|eq_var| !matches!(eq_var, Term::Variable(_)))
                                {
                                    return Err(ParserError::MalformedMetaRule { detail: format!("incorrectly formatted existentially quantified variables: {:?}", eq_vars) });
                                }
                                true
                            }
                            // Case 2 or 3: last is [Q1,Q2] — unconstrained vars list
                            Some(Term::List(vars, tail))
                                if matches!(tail.as_ref(), Term::EmptyList) =>
                            {
                                if vars.iter().any(|v| !matches!(v, Term::Variable(_))) {
                                    return Err(ParserError::MalformedMetaRule { detail: format!("unconstrained variable list should only contain variables, got {:?}", vars) });
                                }
                                // Case 2: ...{P},[Q1,Q2]. — check if second-to-last is a constrained set
                                if len >= 2 {
                                    if let Term::Str(Str::Set, eq_vars) = &literals[len - 2] {
                                        if eq_vars
                                            .iter()
                                            .any(|eq_var| !matches!(eq_var, Term::Variable(_)))
                                        {
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
                        if let Term::Str(Str::Set, eq_vars) = &meta_data {
                            if eq_vars
                                .iter()
                                .any(|eq_var| !matches!(eq_var, Term::Variable(_)))
                            {
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

    pub fn parse_goals(&mut self) -> Result<Vec<Term>, ParserError> {
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

    pub fn parse_all(&mut self) -> Result<Vec<TreeClause>, ParserError> {
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
        super::{tokeniser::tokenise, ParserError},
        {Str, Term, TokenStream, TreeClause},
    };
    #[test]
    fn parse_number_term() {
        //Positive Integer
        let text = tokenise("10").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Int(10));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Int(10));

        //Negative Integer
        let text = tokenise("-10").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Int(-10));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Int(-10));

        //Positive Float
        let text = tokenise("1.01").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Float(1.01));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Float(1.01));

        //Negative Float
        let text = tokenise("-1.01").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Float(-1.01));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Float(-1.01));
    }

    #[test]
    fn parse_constant_term() {
        let text = tokenise("constant").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Constant("constant".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Constant("constant".into()));

        let text = tokenise("constant_1").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Constant("constant_1".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Constant("constant_1".into()));

        let text = tokenise("'file/path'").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Constant("file/path".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Constant("file/path".into()));

        let text = tokenise("'c*o/n\"s-t'").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Constant("c*o/n\"s-t".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Constant("c*o/n\"s-t".into()));
    }

    #[test]
    fn parse_variable_term() {
        let text = tokenise("Var").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Variable("Var".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Variable("Var".into()));

        let text = tokenise("VAR_Under").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Variable("VAR_Under".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Variable("VAR_Under".into()));

        let text = tokenise("VAR10").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Variable("VAR10".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Variable("VAR10".into()));

        let text = tokenise("VAR_Under2").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Variable("VAR_Under2".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Variable("VAR_Under2".into()));
    }

    #[test]
    fn parse_string_term() {
        let text = tokenise("\"A String\"").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::String("A String".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::String("A String".into()));

        let text = tokenise("\"A \\\"String\"").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::String("A \"String".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::String("A \"String".into()));

        let text = tokenise("\"A *+-=: String\"").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::String("A *+-=: String".into()));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::String("A *+-=: String".into()));
    }

    #[test]
    fn parse_atom_term() {
        let p = Term::Constant("p".into());
        let q = Term::Variable("Q".into());
        let x = Term::Variable("X".into());
        let y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let b = Term::Constant("b".into());

        let text = tokenise("p(X,a)").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Comp, vec![p.clone(), x.clone(), a.clone()])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Comp, vec![p.clone(), x.clone(), a.clone()])
        );

        let text = tokenise("Q(b,Y)").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Comp, vec![q.clone(), b.clone(), y.clone()])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Comp, vec![q.clone(), b.clone(), y.clone()])
        );
    }

    #[test]
    fn parse_list_term() {
        let a = Term::Constant("a".into());
        let b = Term::Constant("b".into());
        let c = Term::Constant("c".into());
        let t = Term::Variable("T".into());
        let p = Term::Constant("p".into());

        let text = tokenise("[a,b,c]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );

        let text = tokenise("[a,b,c|[]]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );

        let text = tokenise("[a|T]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::List(vec![a.clone()], Box::new(t.clone())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::List(vec![a.clone()], Box::new(t.clone())));

        let text = tokenise("[a,[b,c]]").unwrap();
        let sub_list = Term::List(vec![b.clone(), c.clone()], Box::new(Term::EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList))
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList))
        );

        let text = tokenise("p([a,[b,c|T]])").unwrap();
        let sub_list = Term::List(vec![b.clone(), c.clone()], Box::new(t.clone()));
        let list = Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Comp, vec![p.clone(), list.clone()])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Str(Str::Comp, vec![p.clone(), list]));

        let text = tokenise("[]").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::EmptyList);
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::EmptyList);
    }

    #[test]
    fn parse_set_term() {
        let a = Term::Constant("a".into());
        let b = Term::Constant("b".into());
        let c = Term::Constant("c".into());
        let p = Term::Constant("p".into());

        let abc = Term::Str(Str::Set, vec![a.clone(), b.clone(), c.clone()]);

        let text = tokenise("{a,b,c}").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, abc.clone());
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("p({a,b,c})").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Str(Str::Comp, vec![p.clone(), abc.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Str(Str::Comp, vec![p.clone(), abc.clone()]));

        let text = tokenise("{a,{b,c}}").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Str(
                Str::Set,
                vec![
                    a.clone(),
                    Term::Str(Str::Set, vec![b.clone(), c.clone()])
                ]
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Str(
                Str::Set,
                vec![
                    a.clone(),
                    Term::Str(Str::Set, vec![b.clone(), c.clone()])
                ]
            )
        );

        let text = tokenise("{a,{}}").unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Set, vec![a.clone(), Term::EmptySet])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Str(Str::Set, vec![a.clone(), Term::EmptySet])
        );
    }

    #[test]
    fn parse_tuple() {
        let a = Term::Constant("a".into());
        let b = Term::Constant("b".into());
        let c = Term::Constant("c".into());
        let p = Term::Constant("p".into());

        let abc = Term::Str(Str::Tup, vec![a.clone(), b.clone(), c.clone()]);
        let bc = Term::Str(Str::Tup, vec![b.clone(), c.clone()]);

        let text = tokenise("(a,b,c)").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("(a,(b,c))").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Str(Str::Tup, vec![a.clone(), bc.clone()]));

        //This test fails
        let text = tokenise("(a,())").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Str(
                Str::Tup,
                vec![a.clone(), Term::Str(Str::Tup, vec![])]
            )
        );

        let text = tokenise("p((a,b,c))").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Str(Str::Comp, vec![p, abc.clone()]));
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
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let one = Term::Int(1);
        let two = Term::Int(2);
        let three = Term::Int(3);
        let one_and_half = Term::Float(1.5);
        let plus = Term::Constant("+".into());
        let _minus = Term::Constant("-".into());
        let divide = Term::Constant("/".into());
        let _times = Term::Constant("*".into());
        let power = Term::Constant("**".into());
        let eqauls = Term::Constant("=:=".into());

        let text = tokenise("X =:= 1 + 2 / 1.5**3").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Str(
                Str::Comp,
                vec![
                    eqauls,
                    x.clone(),
                    Term::Str(
                        Str::Comp,
                        vec![
                            plus.clone(),
                            one.clone(),
                            Term::Str(
                                Str::Comp,
                                vec![
                                    divide.clone(),
                                    two.clone(),
                                    Term::Str(
                                        Str::Comp,
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
        let x = Term::Variable("X".into());
        let _y = Term::Variable("Y".into());
        let one = Term::Int(1);
        let two = Term::Int(2);
        let three = Term::Int(3);
        let one_and_half = Term::Float(1.5);
        let plus = Term::Constant("+".into());
        let _minus = Term::Constant("-".into());
        let divide = Term::Constant("/".into());
        let _times = Term::Constant("*".into());
        let power = Term::Constant("**".into());
        let equals = Term::Constant("=:=".into());

        let text = tokenise("X =:= 1 + (2 / 1.5)**3").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Term::Str(
                Str::Comp,
                vec![
                    equals,
                    x,
                    Term::Str(
                        Str::Comp,
                        vec![
                            plus,
                            one,
                            Term::Str(
                                Str::Comp,
                                vec![
                                    power,
                                    Term::Str(Str::Comp, vec![divide, two, one_and_half]),
                                    three
                                ]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn tuple_or_grouped_expression() {
        let x = Term::Variable("X".into());
        let y = Term::Variable("Y".into());
        let a = Term::Constant("a".into());
        let one = Term::Int(1);
        let two = Term::Int(2);
        let three = Term::Int(3);
        let one_and_half = Term::Float(1.5);
        let plus = Term::Constant("+".into());
        let _minus = Term::Constant("-".into());
        let divide = Term::Constant("/".into());
        let _times = Term::Constant("*".into());
        let power = Term::Constant("**".into());
        let equals = Term::Constant("=:=".into());

        let text = tokenise("(a,X =:= 1 + (2 / 1.5)**(3,Y))").unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Term::Str(
                Str::Tup,
                vec![
                    a,
                    Term::Str(
                        Str::Comp,
                        vec![
                            equals,
                            x,
                            Term::Str(
                                Str::Comp,
                                vec![
                                    plus,
                                    one,
                                    Term::Str(
                                        Str::Comp,
                                        vec![
                                            power,
                                            Term::Str(
                                                Str::Comp,
                                                vec![divide, two, one_and_half]
                                            ),
                                            Term::Str(Str::Tup, vec![three, y])
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
        let head = Term::Str(
            Str::Comp,
            vec![Term::Constant("gt1".into()), Term::Variable("X".into())],
        );
        let body = Term::Str(
            Str::Comp,
            vec![
                Term::Constant(">".into()),
                Term::Variable("X".into()),
                Term::Int(1),
            ],
        );

        assert_eq!(clause, TreeClause::Rule(vec![head, body]));
        // assert_eq!(token_stream.parse_clause().unwrap(),None);
    }

    #[test]
    fn parse_fact() {
        let mut token_stream = TokenStream::new(tokenise("man(plato).").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Str(
            Str::Comp,
            vec![Term::Constant("man".into()), Term::Constant("plato".into())],
        );

        assert_eq!(clause, TreeClause::Fact(head));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule() {
        let mut token_stream = TokenStream::new(tokenise("P(X,Y):-Q(X,Y),{P,Q}.").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Str(
            Str::Comp,
            vec![
                Term::Variable("P".into()),
                Term::Variable("X".into()),
                Term::Variable("Y".into()),
            ],
        );
        let body = Term::Str(
            Str::Comp,
            vec![
                Term::Variable("Q".into()),
                Term::Variable("X".into()),
                Term::Variable("Y".into()),
            ],
        );
        let meta_data = Term::Str(
            Str::Set,
            vec![Term::Variable("P".into()), Term::Variable("Q".into())],
        );

        assert_eq!(clause, TreeClause::MetaRule(vec![head, body, meta_data]));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule_with_unconstrained_list() {
        // {El},[Q1,Q2] — El is constrained, Q1 and Q2 are unconstrained
        let mut token_stream =
            TokenStream::new(tokenise("edge(El,Q1,Q2):-q(Q1),q(Q2),{El},[Q1,Q2].").unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Str(
            Str::Comp,
            vec![
                Term::Constant("edge".into()),
                Term::Variable("El".into()),
                Term::Variable("Q1".into()),
                Term::Variable("Q2".into()),
            ],
        );
        let body1 = Term::Str(
            Str::Comp,
            vec![Term::Constant("q".into()), Term::Variable("Q1".into())],
        );
        let body2 = Term::Str(
            Str::Comp,
            vec![Term::Constant("q".into()), Term::Variable("Q2".into())],
        );
        let constrained = Term::Str(Str::Set, vec![Term::Variable("El".into())]);
        let unconstrained = Term::List(
            vec![Term::Variable("Q1".into()), Term::Variable("Q2".into())],
            Box::new(Term::EmptyList),
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
        let head = Term::Str(
            Str::Comp,
            vec![
                Term::Constant("edge".into()),
                Term::Variable("El".into()),
                Term::Variable("Q1".into()),
                Term::Variable("Q2".into()),
            ],
        );
        let body1 = Term::Str(
            Str::Comp,
            vec![Term::Constant("q".into()), Term::Variable("Q1".into())],
        );
        let body2 = Term::Str(
            Str::Comp,
            vec![Term::Constant("q".into()), Term::Variable("Q2".into())],
        );
        let unconstrained = Term::List(
            vec![
                Term::Variable("El".into()),
                Term::Variable("Q1".into()),
                Term::Variable("Q2".into()),
            ],
            Box::new(Term::EmptyList),
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
        let head = Term::Str(
            Str::Comp,
            vec![
                Term::Variable("Map".into()),
                Term::EmptyList,
                Term::EmptyList,
                Term::Variable("X".into()),
            ],
        );
        let meta_data = Term::Str(Str::Set, vec![Term::Variable("Map".into())]);

        assert_eq!(clause, TreeClause::MetaFact(head, meta_data));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_directive() {
        let mut token_stream = TokenStream::new(tokenise("test(a),goal([_|T],1).").unwrap());
        let clause = token_stream.parse_goals().unwrap();
        let body = Term::Str(
            Str::Comp,
            vec![Term::Constant("test".into()), Term::Constant("a".into())],
        );
        let body2 = Term::Str(
            Str::Comp,
            vec![
                Term::Constant("goal".into()),
                Term::List(vec![Term::AnonVar], Box::new(Term::Variable("T".into()))),
                Term::Int(1),
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

        let head = Term::Str(
            Str::Comp,
            vec![Term::Constant("gt1".into()), Term::Variable("X".into())],
        );
        let body = Term::Str(
            Str::Comp,
            vec![
                Term::Constant(">".into()),
                Term::Variable("X".into()),
                Term::Int(1),
            ],
        );
        assert_eq!(clauses[0], TreeClause::Rule(vec![head, body]));

        let head = Term::Str(
            Str::Comp,
            vec![Term::Constant("man".into()), Term::Constant("plato".into())],
        );
        assert_eq!(clauses[1], TreeClause::Fact(head));

        let head = Term::Str(
            Str::Comp,
            vec![
                Term::Variable("P".into()),
                Term::Variable("X".into()),
                Term::Variable("Y".into()),
            ],
        );
        let body = Term::Str(
            Str::Comp,
            vec![
                Term::Variable("Q".into()),
                Term::Variable("X".into()),
                Term::Variable("Y".into()),
            ],
        );
        let meta_data = Term::Str(
            Str::Set,
            vec![Term::Variable("P".into()), Term::Variable("Q".into())],
        );
        assert_eq!(
            clauses[2],
            TreeClause::MetaRule(vec![head, body, meta_data])
        );
    }
}
