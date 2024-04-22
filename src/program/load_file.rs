use crossterm::terminal::Clear;

use super::{
    clause::{self, Clause, ClauseOwned},
    Program,
};
use crate::heap::Heap;
use std::{collections::HashMap, fs, rc::Rc};

static CONSTRAINT: &'static str = ":<c>-";
static IMPLICATION: &'static str = ":-";

impl Program {
    pub fn load_file(&mut self, path: &str, heap: &mut Heap) {
        heap.query_space = false;
        let mut file = fs::read_to_string(format!("{path}.pl")).expect("Unable to read file");
        remove_comments(&mut file);
        let mut speech: bool = false;
        let mut quote: bool = false;
        let mut i1 = 0;
        for (i2, char) in file.chars().enumerate() {
            if !speech && !quote && char == '.' {
                let segment = file[i1..i2].trim();
                if segment.find(":-") == Some(0) {
                    self.handle_directive(segment);
                } else {
                    let clause = parse_clause(segment, heap);
                    if segment.contains(CONSTRAINT) {
                        self.add_constraint(clause);
                    } else {
                        self.add_clause(clause, heap);
                    }
                }
                i1 = i2 + 1;
            } else {
                match char {
                    '"' => {
                        if !quote {
                            speech = !speech
                        }
                    }
                    '\'' => {
                        if !speech {
                            quote = !quote
                        }
                    }
                    _ => (),
                }
            }
        }
        heap.query_space = true;
        self.clauses.find_flags();
        self.predicates = self.clauses.predicate_map(heap);
    }
}

fn get_uni_vars<'a>(clause: &'a str) -> (usize, Vec<&'a str>) {
    match clause.rfind('\\') {
        Some(i) => {
            if clause[i..].chars().any(|c| c == '"' || c == '\'') {
                (clause.len(), vec![])
            } else {
                (
                    i,
                    clause[i + 1..].split(',').map(|var| var.trim()).collect(),
                )
            }
        }
        None => (clause.len(), vec![]),
    }
}

fn parse_clause(clause: &str, heap: &mut Heap) -> ClauseOwned {
    let (i3, uni_vars) = get_uni_vars(clause);
    let (mut i1, i2) = match clause.find(CONSTRAINT) {
        Some(i) => (i, i + CONSTRAINT.len()),
        None => match clause.find(IMPLICATION) {
            Some(i) => (i, i + IMPLICATION.len()),
            None => {
                //No implication present, build fact
                return Box::new([heap.build_literal(clause, &mut HashMap::new(), &uni_vars)]);
            }
        },
    };
    let head = &clause[..i1];
    let body = &clause[i2..i3];
    i1 = 0;
    let mut in_brackets = (0, 0);
    let mut body_literals: Vec<&str> = vec![];
    for (i2, c) in body.chars().enumerate() {
        match c {
            '(' => {
                in_brackets.0 += 1;
            }
            ')' => {
                if in_brackets.0 == 0 {
                    break;
                }
                in_brackets.0 -= 1;
            }
            '[' => {
                in_brackets.1 += 1;
            }
            ']' => {
                if in_brackets.1 == 0 {
                    break;
                }
                in_brackets.1 -= 1;
            }
            ',' => {
                if in_brackets == (0, 0) {
                    body_literals.push(&body[i1..i2]);
                    i1 = i2 + 1
                }
            }
            _ => (),
        }
        if i2 == body.len() - 1 {
            body_literals.push(body[i1..].trim());
        }
    }
    let mut map: HashMap<String, usize> = HashMap::new();
    let head = heap.build_literal(head, &mut map, &uni_vars);
    let body: Vec<usize> = body_literals
        .iter()
        .map(|text| heap.build_literal(text, &mut map, &uni_vars))
        .collect();
    [&[head], body.as_slice()].concat().into()
}

fn remove_comments(file: &mut String) {
    //Must ingore % if in string
    let mut i = 0;
    let mut comment = false;
    loop {
        let c = match file.chars().nth(i) {
            Some(c) => c,
            None => break,
        };
        if c == '%' {
            let mut i2 = i;
            loop {
                i2 += 1;
                if file.chars().nth(i2) == Some('\n') || file.chars().nth(i2) == None {
                    file.replace_range(i..i2 + 1, "");
                    break;
                }
            }
        } else {
            i += 1;
        }
    }
}
