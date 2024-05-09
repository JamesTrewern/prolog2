use super::{
    clause::*,
    Program,
};
use crate::{clause, heap::Heap};
use std::{collections::HashMap, fs};

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
                    let (clause_type, clause) = Clause::parse_clause(segment, heap);
                    self.add_clause(clause_type, clause);
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
        self.clauses.sort_clauses();
        self.clauses.find_flags();
        self.predicates = self.clauses.predicate_map(heap);
    }
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
