use std::fmt::format;

use fsize::fsize;

const INFIX_ORDER: &[&[&str]] = &[
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &["==", "=/=", "/=", "=:=", "is"],
];

pub enum Unit {
    Atom(String),
    Variable(String),
    Int(usize),
    Float(fsize),
}

impl Unit {
    fn is_atom(token: &str) -> bool {
        token.chars().next().map_or(false, |c| {
            c.is_lowercase() || c == '\'' && token.chars().last().map_or(false, |c| c == '\'')
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
        Unit::is_numeric(token) || Unit::is_atom_var(token)
    }

    pub fn parse_unit(token: &str) -> Option<Self> {
        if Unit::is_variable(token){
            Some(Unit::Variable(token.into()))
        }else if Unit::is_atom(token){
            Some(Unit::Atom(token.into()))
        }else{
            None
        }
    }
}

pub enum Term {
    Unit(Unit),
    Compound(Unit, Vec<Term>),
    List(Vec<Term>,Option<Box<Term>>)
}

pub enum Clause {
    Fact(Term),
    Rule(Term, Vec<Term>),
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
        if self.index < self.tokens.len() {
            let token = self.tokens[self.index].as_str();
            self.index += 1;
            while self.tokens[self.index] == "\n" {
                self.index += 1;
                self.line += 1;
            }
            Some(token)
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<&str> {
        self.tokens
            .get(self.index)
            .and_then(|token| Some(token.as_str()))
    }
}

fn is_operator(token: &str) -> bool {
    INFIX_ORDER.iter().any(|group| group.contains(&token))
}

fn infix_order(operator: &str) -> usize {
    INFIX_ORDER
        .iter()
        .position(|ops| ops.contains(&operator)).unwrap()
}

fn resolve_infix(term_stack: &mut Vec<Term>, op_stack: &mut Vec<String>, max_prescendence: usize) {
    while let Some(p) = op_stack.last().map(|operator| infix_order(&operator))
    {
        if p > max_prescendence{
            break
        }
        let op = op_stack.pop().unwrap();
        let right = term_stack.pop().unwrap();
        let left = term_stack.pop().unwrap();
        term_stack.push(Term::Compound(Unit::Atom(op), vec![left,right]));
    }
}

impl TokenStream {
    fn consume_args(&mut self) -> Result<Vec<Term>, String> {
        let mut args = Vec::new();
        while let arg = self.parse_expression()? {
            args.push(arg);
            match self.peek() {
                Some(")"|"|"|"]") => return Ok(args), //TODO end consuming args based on certain conditions dont accept all end tokens
                Some(",") => {
                    self.next();
                }
                Some(token) => return Err(format!("Unexpected token: {token}")),
                None => return Err("Unexpected End of File".into()),
            }
        }
        Ok(args)
    }

    fn parse_term(&mut self) -> Result<Term, String> {
        match self.peek().ok_or("Unexpected end of file")? {
            "{" => todo!("Handle EQ vars"),
            "(" => todo!("Handle Tuples"),
            "[" => {
                self.next();
                let head = self.consume_args()?;
                match self.peek().ok_or("Unexpected end of file")? {
                    "|" => Ok(Term::List(head, Some(Box::new(self.parse_expression()?)))),
                    "]" => Ok(Term::List(head, None)),
                    token => return Err(format!("Unexpected token: {token}"))
                }
            },
            token => {
                match Unit::parse_unit(token) {
                    Some(unit@ (Unit::Atom(_) | Unit::Variable(_))) => {
                        if self.peek() == Some("("){
                            self.next();
                            let args = self.consume_args()?;
                            if self.peek() == Some(")"){
                                self.next();
                                Ok(Term::Compound(unit, args))
                            }else{
                                Err(format!("Unexpected token: {}", self.peek().unwrap_or("")))
                            }
                        }else{
                            Ok(Term::Unit(unit))
                        }
                    },
                    Some(_) => todo!(),
                    None => todo!(),
                }
            }
            token if is_operator(token) => todo!("Operators Aren't handled"),
            _ => Err(format!("Uh oh \"{}\" confused me", self.peek().unwrap())),
        }
    }

    fn parse_expression(&mut self) -> Result<Term,String>{
        let mut op_stack = Vec::<String>::new();
        let mut term_stack = Vec::<Term>::new();

        while self.peek() != Some(","){
            term_stack.push(self.parse_term()?);
            match self.next() {
                Some(token) if is_operator(token) => {
                    op_stack.push(token.into());
                }
                Some(token) => return Err(format!("Unexpected token: {token}")),
                None => return Err("Unexpected End of File".into())
            }
        }

        resolve_infix(&mut term_stack, &mut op_stack, INFIX_ORDER.len());
        term_stack.pop().ok_or("Empty expression".into())
    }

    fn parse_clause(&mut self) -> Result<Option<Clause>, String> {
        match self.peek() {
            None => return Ok(None),
            Some(":-") => todo!("Handle Directive"),
            Some(_) => {
                let head = self.parse_expression()?;
                if self.peek() == Some(":-") {
                    self.next(); // Consume ":-"
                    let mut body = Vec::new();
                    while self.peek() != Some(".") {
                        body.push(self.parse_term()?);
                        if self.peek() == Some(",") {
                            self.next(); // Consume ","
                        }
                    }
                    if self.next() == Some(".") {
                        Ok(Some(Clause::Rule(head, body)))
                    } else {
                        Err("Expected \".\"".into()) // Error:
                    }
                } else if self.next() == Some(".") {
                    Ok(Some(Clause::Fact(head)))
                } else {
                    Err("Expected \".\" or \":-\"".into())
                }
            }
        }
    }
}
