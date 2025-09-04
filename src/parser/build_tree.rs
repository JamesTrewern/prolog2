//TODO Handle sets

use std::{fmt::format, str};

use fsize::fsize;

use super::term::{Term, Unit};

const INFIX_ORDER: &[&[&str]] = &[
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &["==", "=/=", "/=", "=:=", "is", ">", ">=", "<", "<="],
];

#[derive(Debug, PartialEq, Clone)]
pub enum TreeClause {
    Fact(Term),
    Rule(Vec<Term>),
    MetaRule(Vec<Term>),
    Directive(Vec<Term>),
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

    fn print_state(&self) {
        println!("{:?},{}", self.tokens, self.index);
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
        let op = op_stack.pop().unwrap();
        let right = term_stack.pop().unwrap();
        let left = term_stack.pop().unwrap();
        term_stack.push(Term::Atom(Unit::Constant(op), vec![left, right]));
    }
}

impl TokenStream {
    fn expect(&mut self, value: &str) -> Result<(), String> {
        match self.next() {
            Some(token) if token == value => Ok(()),
            Some(token) => Err(format!("Expected \"{value}\" recieved \"{token}\"")),
            None => Err(format!("Unexpected end of file in expect {value}")),
        }
    }

    fn consume_args(&mut self) -> Result<Vec<Term>, String> {
        let mut args = Vec::new();
        loop {
            args.push(self.parse_expression()?);
            match self.peek() {
                Some(")" | "|" | "]" | "}") => return Ok(args), //TODO end consuming args based on certain conditions dont accept all end tokens
                Some(",") => {
                    self.next();
                }
                Some(token) => return Err(format!("Unexpected token in arguments: {token}")),
                None => return Err("Unexpected End of File".into()),
            }
        }
    }

    /**
     *
     */
    pub(super) fn parse_term(&mut self) -> Result<Term, String> {
        match self.peek().ok_or("Unexpected end of file")? {
            "{" => {
                self.next();
                let args = self.consume_args()?;
                if self.next() == Some("}") {
                    Ok(Term::Set(args))
                } else {
                    Err("Incorrectly formatted set".into())
                }
            }
            "[" => {
                self.next();
                let head = self.consume_args()?;
                match self.next().ok_or("Unexpected end of file")? {
                    "|" => {
                        let tail = Box::new(self.parse_expression()?);
                        self.expect("]")?;
                        Ok(Term::List(head, tail))
                    }
                    "]" => Ok(Term::List(head, Box::new(Term::EmptyList))),
                    token => return Err(format!("Unexpected token in list: {token}")),
                }
            }
            "[]" => {
                self.next();
                Ok(Term::EmptyList)
            }
            "{}" => {
                self.next();
                Ok(Term::Set(vec![]))
            }
            "()" => {
                self.next();
                Ok(Term::Tuple(vec![]))
            }
            token if is_operator(token) => todo!("Operators Aren't handled"),
            token => {
                let token = token.to_string();
                match Unit::parse_unit(self.next().unwrap()) {
                    Some(unit @ (Unit::Constant(_) | Unit::Variable(_))) => {
                        if self.peek() == Some("(") {
                            self.next();
                            let args = self.consume_args()?;
                            self.expect(")")?;
                            Ok(Term::Atom(unit, args))
                        } else {
                            Ok(Term::Unit(unit))
                        }
                    }
                    Some(num @ (Unit::Float(_) | Unit::Int(_))) => Ok(Term::Unit(num)),
                    Some(unit @ Unit::String(_)) => Ok(Term::Unit(unit)),
                    None => todo!("handle: {token}"),
                }
            }
            _ => Err(format!("Uh oh \"{}\" confused me", self.peek().unwrap())),
        }
    }

    pub(super) fn parse_expression(&mut self) -> Result<Term, String> {
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
                    term_stack.push(Term::Tuple(args));
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
        term_stack.pop().ok_or("Empty expression".into())
    }

    fn parse_body_literals(&mut self) -> Result<Vec<Term>, String> {
        let mut body = Vec::new();
        loop {
            body.push(self.parse_expression()?);
            match self.next() {
                Some(",") => continue,
                Some(".") => break,
                Some(token) => {
                    return Err(format!(
                        "Unexpected token ({token}) after literal, expected either ',' or '.'"
                    ))
                }
                None => return Err("Unexpected end of file".into()),
            }
        }
        Ok(body)
    }

    pub fn parse_clause(&mut self) -> Result<Option<TreeClause>, String> {
        match self.peek() {
            None => return Ok(None),
            Some(":-") => {
                self.next();
                return Ok(Some(TreeClause::Directive(self.parse_body_literals()?)));
            }
            Some(_) => {
                let mut literals = vec![self.parse_expression()?];
                match self.next() {
                    Some(":-") => {
                        literals.append( &mut self.parse_body_literals()?);
                        let meta_rule = if let Some(Term::Set(eq_vars)) = literals.last() {
                            if eq_vars
                                .iter()
                                .any(|eq_var| !matches!(eq_var, Term::Unit(Unit::Variable(_))))
                            {
                                return Err(format!("Incorrectly formatted existentially quantified variables  {:?}", eq_vars));
                            }
                            true
                        } else {
                            false
                        };
                        if meta_rule {
                            Ok(Some(TreeClause::MetaRule(literals)))
                        } else {
                            Ok(Some(TreeClause::Rule(literals)))
                        }
                    }
                    Some(".") => Ok(Some(TreeClause::Fact(literals[0].clone()))),
                    Some(token) => Err(format!("Expected \".\" or \":-\", recieved {token}")),
                    None => Err("Unexpected end of file".into()),
                }
            }
        }
    }

    pub fn parse_all(&mut self) -> Result<Vec<TreeClause>, String> {
        let mut clauses = Vec::<TreeClause>::new();
        loop {
            match self.parse_clause() {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => return Ok(clauses),
                Err(msg) => return Err(format!("Line {}:  {msg}", self.line)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        super::tokeniser::tokenise,
        {TreeClause, Term, TokenStream, Unit},
    };
    #[test]
    fn parse_number_term() {
        //Positive Integer
        let text = tokenise("10".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(10)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(10)));

        //Negative Integer
        let text = tokenise("-10".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(-10)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(-10)));

        //Positive Float
        let text = tokenise("1.01".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(1.01)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(1.01)));

        //Negative Float
        let text = tokenise("-1.01".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(-1.01)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(-1.01)));
    }

    #[test]
    fn parse_constant_term() {
        let text = tokenise("constant".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant".into())));

        let text = tokenise("constant_1".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant_1".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant_1".into())));

        let text = tokenise("'file/path'".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("file/path".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("file/path".into())));

        let text = tokenise("'c*o/n\"s-t'".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("c*o/n\"s-t".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("c*o/n\"s-t".into())));
    }

    #[test]
    fn parse_variable_term() {
        let text = tokenise("Var".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("Var".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("Var".into())));

        let text = tokenise("VAR_Under".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under".into())));

        let text = tokenise("VAR10".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR10".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR10".into())));

        let text = tokenise("VAR_Under2".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under2".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under2".into())));
    }

    #[test]
    fn parse_string_term() {
        let text = tokenise("\"A String\"".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A String\"".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A String\"".into())));

        let text = tokenise("\"A \\\"String\"".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A \"String\"".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A \"String\"".into())));

        let text = tokenise("\"A *+-=: String\"".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A *+-=: String\"".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A *+-=: String\"".into())));
    }

    #[test]
    fn parse_atom_term() {
        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let b = Unit::Constant("b".into());

        let text = tokenise("p(X,a)".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                p.clone(),
                vec![Term::Unit(x.clone()), Term::Unit(a.clone())]
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                p.clone(),
                vec![Term::Unit(x.clone()), Term::Unit(a.clone())]
            )
        );

        let text = tokenise("Q(b,Y)".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                q.clone(),
                vec![Term::Unit(b.clone()), Term::Unit(y.clone())]
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                q.clone(),
                vec![Term::Unit(b.clone()), Term::Unit(y.clone())]
            )
        );
    }

    #[test]
    fn parse_list_term() {
        let a = Term::Unit(Unit::Constant("a".into()));
        let b = Term::Unit(Unit::Constant("b".into()));
        let c = Term::Unit(Unit::Constant("c".into()));
        let t = Term::Unit(Unit::Variable("T".into()));
        let p = Unit::Constant("p".into());

        let text = tokenise("[a,b,c]".into()).unwrap();
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

        let text = tokenise("[a,b,c|[]]".into()).unwrap();
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

        let text = tokenise("[a|T]".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::List(vec![a.clone()], Box::new(t.clone())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::List(vec![a.clone()], Box::new(t.clone())));

        let text = tokenise("[a,[b,c]]".into()).unwrap();
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

        let text = tokenise("p([a,[b,c|T]])".into()).unwrap();
        let sub_list = Term::List(vec![b.clone(), c.clone()], Box::new(t.clone()));
        let list = Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![list.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![list]));

        let text = tokenise("[]".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::EmptyList);
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::EmptyList);
    }

    #[test]
    fn parse_set_term() {
        let a = Term::Unit(Unit::Constant("a".into()));
        let b = Term::Unit(Unit::Constant("b".into()));
        let c = Term::Unit(Unit::Constant("c".into()));
        let p = Unit::Constant("p".into());

        let abc = Term::Set(vec![a.clone(), b.clone(), c.clone()]);

        let text = tokenise("{a,b,c}".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, abc.clone());
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("p({a,b,c})".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![abc.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![abc.clone()]));

        let text = tokenise("{a,{b,c}}".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Set(vec![a.clone(), Term::Set(vec![b.clone(), c.clone()])])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Set(vec![a.clone(), Term::Set(vec![b.clone(), c.clone()])])
        );

        let text = tokenise("{a,{}}".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Set(vec![a.clone(), Term::Set(vec![])]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Set(vec![a.clone(), Term::Set(vec![])]));
    }

    #[test]
    fn parse_tuple() {
        let a = Term::Unit(Unit::Constant("a".into()));
        let b = Term::Unit(Unit::Constant("b".into()));
        let c = Term::Unit(Unit::Constant("c".into()));
        let p = Unit::Constant("p".into());

        let abc = Term::Tuple(vec![a.clone(), b.clone(), c.clone()]);
        let bc = Term::Tuple(vec![b.clone(), c.clone()]);

        let text = tokenise("(a,b,c)".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("(a,(b,c))".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Tuple(vec![a.clone(), bc.clone()]));

        //This test fails
        let text = tokenise("(a,())".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Tuple(vec![a.clone(), Term::Tuple(vec![])]));

        let text = tokenise("p((a,b,c))".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Atom(p, vec![abc.clone()]));
    }

    //TODO Improve Error messaging for unclosed structures
    #[test]
    fn unclosed_atom() {
        let mut tokens = TokenStream::new(tokenise("p(X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,(Y)".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,(Y).".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn unclosed_list() {
        let mut tokens = TokenStream::new(tokenise("[X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("[X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("[X,[Y]".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("[X,[Y].".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn unclosed_set() {
        let mut tokens = TokenStream::new(tokenise("{X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("{X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("{X,{Y}".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("{X,{Y}.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn unclosed_tuple() {
        let mut tokens = TokenStream::new(tokenise("(X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("(X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("(X,(Y)".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("(X,(Y).".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn infix_order() {
        let x = Term::Unit(Unit::Variable("X".into()));
        let y = Term::Unit(Unit::Variable("Y".into()));
        let one = Term::Unit(Unit::Int(1));
        let two = Term::Unit(Unit::Int(2));
        let three = Term::Unit(Unit::Int(3));
        let one_and_half = Term::Unit(Unit::Float(1.5));
        let plus = Unit::Constant("+".into());
        let minus = Unit::Constant("-".into());
        let divide = Unit::Constant("/".into());
        let times = Unit::Constant("*".into());
        let power = Unit::Constant("**".into());
        let eqauls = Unit::Constant("=:=".into());

        let text = tokenise("X =:= 1 + 2 / 1.5**3".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                eqauls,
                vec![
                    x.clone(),
                    Term::Atom(
                        plus.clone(),
                        vec![
                            one.clone(),
                            Term::Atom(
                                divide.clone(),
                                vec![
                                    two.clone(),
                                    Term::Atom(
                                        power.clone(),
                                        vec![one_and_half.clone(), three.clone()]
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
        let x = Term::Unit(Unit::Variable("X".into()));
        let y = Term::Unit(Unit::Variable("Y".into()));
        let one = Term::Unit(Unit::Int(1));
        let two = Term::Unit(Unit::Int(2));
        let three = Term::Unit(Unit::Int(3));
        let one_and_half = Term::Unit(Unit::Float(1.5));
        let plus = Unit::Constant("+".into());
        let minus = Unit::Constant("-".into());
        let divide = Unit::Constant("/".into());
        let times = Unit::Constant("*".into());
        let power = Unit::Constant("**".into());
        let equals = Unit::Constant("=:=".into());

        let text = tokenise("X =:= 1 + (2 / 1.5)**3".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Term::Atom(
                equals,
                vec![
                    x,
                    Term::Atom(
                        plus,
                        vec![
                            one,
                            Term::Atom(
                                power,
                                vec![Term::Atom(divide, vec![two, one_and_half]), three]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn tuple_or_grouped_expression() {
        let x = Term::Unit(Unit::Variable("X".into()));
        let y = Term::Unit(Unit::Variable("Y".into()));
        let a = Term::Unit(Unit::Constant("a".into()));
        let one = Term::Unit(Unit::Int(1));
        let two = Term::Unit(Unit::Int(2));
        let three = Term::Unit(Unit::Int(3));
        let one_and_half = Term::Unit(Unit::Float(1.5));
        let plus = Unit::Constant("+".into());
        let minus = Unit::Constant("-".into());
        let divide = Unit::Constant("/".into());
        let times = Unit::Constant("*".into());
        let power = Unit::Constant("**".into());
        let equals = Unit::Constant("=:=".into());

        let text = tokenise("(a,X =:= 1 + (2 / 1.5)**(3,Y))".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Term::Tuple(vec![
                a,
                Term::Atom(
                    equals,
                    vec![
                        x,
                        Term::Atom(
                            plus,
                            vec![
                                one,
                                Term::Atom(
                                    power,
                                    vec![
                                        Term::Atom(divide, vec![two, one_and_half]),
                                        Term::Tuple(vec![three, y])
                                    ]
                                )
                            ]
                        )
                    ]
                )
            ])
        );
    }

    #[test]
    fn parse_rule() {
        let mut token_stream = TokenStream::new(tokenise("gt1(X):-X>1.".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Atom(
            Unit::Constant("gt1".into()),
            vec![Term::Unit(Unit::Variable("X".into()))],
        );
        let body = Term::Atom(
            Unit::Constant(">".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Int(1)),
            ],
        );

        assert_eq!(clause, TreeClause::Rule(vec![head, body]));
        // assert_eq!(token_stream.parse_clause().unwrap(),None);
    }

    #[test]
    fn parse_fact() {
        let mut token_stream = TokenStream::new(tokenise("man(plato).".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Atom(
            Unit::Constant("man".into()),
            vec![Term::Unit(Unit::Constant("plato".into()))],
        );

        assert_eq!(clause, TreeClause::Fact(head));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule() {
        let mut token_stream = TokenStream::new(tokenise("P(X,Y):-Q(X,Y),{P,Q}.".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Atom(
            Unit::Variable("P".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let body = Term::Atom(
            Unit::Variable("Q".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let meta_data = Term::Set(vec![
            Term::Unit(Unit::Variable("P".into())),
            Term::Unit(Unit::Variable("Q".into())),
        ]);

        assert_eq!(clause, TreeClause::MetaRule(vec![head, body, meta_data]));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_directive() {
        let mut token_stream =
            TokenStream::new(tokenise(":-test(a),['file/path'].".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let body = Term::Atom(
            Unit::Constant("test".into()),
            vec![Term::Unit(Unit::Constant("a".into()))],
        );
        let body2 = Term::List(
            vec![Term::Unit(Unit::Constant("file/path".into()))],
            Box::new(Term::EmptyList),
        );

        assert_eq!(clause, TreeClause::Directive(vec![body, body2]));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_all_clauses() {
        let text =
            "gt1(X):-X>1.\nman(plato).\nP(X,Y):-\n\tQ(X,Y),\n\t{P,Q}.\n:-test(a),['file/path']."
                .to_string();
        let mut token_stream = TokenStream::new(tokenise(text).unwrap());
        let mut clauses = token_stream.parse_all().unwrap();

        let head = Term::Atom(
            Unit::Constant("gt1".into()),
            vec![Term::Unit(Unit::Variable("X".into()))],
        );
        let body = Term::Atom(
            Unit::Constant(">".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Int(1)),
            ],
        );
        assert_eq!(clauses[0], TreeClause::Rule(vec![head, body]));

        let head = Term::Atom(
            Unit::Constant("man".into()),
            vec![Term::Unit(Unit::Constant("plato".into()))],
        );
        assert_eq!(clauses[1], TreeClause::Fact(head));

        let head = Term::Atom(
            Unit::Variable("P".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let body = Term::Atom(
            Unit::Variable("Q".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let meta_data = Term::Set(vec![
            Term::Unit(Unit::Variable("P".into())),
            Term::Unit(Unit::Variable("Q".into())),
        ]);
        assert_eq!(clauses[2], TreeClause::MetaRule(vec![head, body, meta_data]));

        let body = Term::Atom(
            Unit::Constant("test".into()),
            vec![Term::Unit(Unit::Constant("a".into()))],
        );
        let body2 = Term::List(
            vec![Term::Unit(Unit::Constant("file/path".into()))],
            Box::new(Term::EmptyList),
        );
        assert_eq!(clauses[3], TreeClause::Directive(vec![body, body2]));
    }
}
