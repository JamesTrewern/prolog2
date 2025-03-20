//TODO Handle sets

use std::{fmt::format, str};

use fsize::fsize;

const INFIX_ORDER: &[&[&str]] = &[
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &["==", "=/=", "/=", "=:=", "is", ">", ">=", "<", "<="],
];

#[derive(Debug, PartialEq, Clone)]
pub enum Unit {
    Constant(String),
    Variable(String),
    Int(isize),
    Float(fsize),
    String(String),
}

impl Unit {
    fn is_atom(token: &str) -> bool {
        token.chars().next().map_or(false, |c| {
            c.is_lowercase() || c == '\'' && token.chars().last().map_or(false, |c| c == '\'')
        })
    }

    fn is_string(token: &str) -> bool {
        token.chars().next().map_or(false, |c| {
            c == '"' && token.chars().last().map_or(false, |c| c == '"')
        })
    }

    //Is variable if begins with _ or uppercase
    fn is_variable(token: &str) -> bool {
        token
            .chars()
            .next()
            .map_or(false, |c| c.is_uppercase() || c == '_')
            && token.chars().all(|c| c.is_alphanumeric() || c == '_')
    }

    fn is_numeric(token: &str) -> bool {
        token.chars().all(|c| c.is_ascii_digit() || c == '.')
    }

    fn is_atom_var(token: &str) -> bool {
        Unit::is_atom(token) || Unit::is_variable(token)
    }

    fn is_unit(token: &str) -> bool {
        Unit::is_numeric(token) || Unit::is_atom_var(token) || Unit::is_string(token)
    }

    pub fn parse_unit(token: &str) -> Option<Self> {
        if Unit::is_variable(token) {
            Some(Unit::Variable(token.into()))
        } else if Unit::is_atom(token) {
            if token.chars().next().unwrap() == '\''{
                Some(Unit::Constant(token[1..token.len()-1].into()))
            }else{
                Some(Unit::Constant(token.into()))
            }
        } else if Unit::is_string(token) {
            Some(Unit::String(token.to_string()))
        } else if let Ok(num) = token.parse::<isize>() {
            Some(Unit::Int(num))
        } else if let Ok(num) = token.parse::<fsize>() {
            Some(Unit::Float(num))
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    Unit(Unit),
    Atom(Unit, Vec<Term>),
    List(Vec<Term>, Box<Term>),
    Tuple(Vec<Term>),
    Set(Vec<Term>),
    EmptyList,
}
#[derive(Debug, PartialEq, Clone)]
pub enum Clause {
    Fact(Term),
    Rule(Term, Vec<Term>),
    MetaRule(Term, Vec<Term>),
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

    fn parse_body_literals(&mut self) -> Result<Vec<Term>,String>{
        let mut body = Vec::new();
        loop {
            body.push(self.parse_expression()?);
            match self.next() {
                Some(",") => continue,
                Some(".") => break,
                Some(token) => return Err(format!("Unexpected token ({token}) after literal, expected either ',' or '.'")),
                None => return Err("Unexpected end of file".into()),
            }
        }
        Ok(body)
    }

    pub(super) fn parse_clause(&mut self) -> Result<Option<Clause>, String> {
        match self.peek() {
            None => return Ok(None),
            Some(":-") => {self.next();return Ok(Some(Clause::Directive(self.parse_body_literals()?)));},
            Some(_) => {
                let head = self.parse_expression()?;
                match self.next() {
                    Some(":-") => {
                        let mut meta_rule = false;
                        // self.next(); // Consume ":-"
                        let mut body = self.parse_body_literals()?;
                        let meta_rule = if let Some(Term::Set(eq_vars)) = body.last(){
                            if eq_vars
                                .iter()
                                .any(|eq_var| !matches!(eq_var, Term::Unit(Unit::Variable(_))))
                            {
                                return Err(format!("Incorrectly formatted existentially quantified variables  {:?}", eq_vars));
                            }
                            true
                        }else{
                            false
                        };
                        if meta_rule {
                            Ok(Some(Clause::MetaRule(head, body)))
                        } else {
                            Ok(Some(Clause::Rule(head, body)))
                        }
                    }
                    Some(".") => Ok(Some(Clause::Fact(head))),
                    Some(token) => Err(format!("Expected \".\" or \":-\", recieved {token}")),
                    None => Err("Unexpected end of file".into()),
                }
            }
        }
    }

    pub(super) fn parse_all(&mut self) -> Result<Vec<Clause>, String> {
        let mut clauses = Vec::<Clause>::new();

        loop {
            println!("{clauses:?}");
            self.print_state();
            match self.parse_clause() {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => return Ok(clauses),
                Err(msg) => return Err(format!("Line {}:  {msg}", self.line)),
            }
        }
    }
}
