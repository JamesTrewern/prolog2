use std::collections::HashMap;

use super::Heap;
#[derive(Clone)]
enum SubTerm {
    TEXT(String),
    CELL((usize, usize)),
}


impl Heap {
    fn text_var(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        match symbols_map.get(text) {
            Some(ref_addr) => self.set_var(Some(*ref_addr), uni_vars.contains(&text)),
            None => {
                let addr = self.set_var(None, uni_vars.contains(&text));
                symbols_map.insert(text.to_owned(), addr);
                self.symbols.set_var(text, addr);
                addr
            }
        }
    }
    fn text_const(&mut self, text: &str, symbols_map: &mut HashMap<String, usize>) -> usize {
        let id = self.symbols.set_const(text);
        self.set_const(id)
    }
    fn text_singlet(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        if text.chars().next().unwrap().is_uppercase() {
            self.text_var(text, symbols_map, uni_vars)
        } else {
            self.text_const(text, symbols_map)
        }
    }

    fn handle_sub_terms(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> Vec<SubTerm> {
        let mut last_i: usize = 0;
        let mut in_brackets = (0, 0);
        let mut subterms_txt: Vec<&str> = vec![];
        for (i, c) in text.chars().enumerate() {
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
                        subterms_txt.push(&text[last_i..i]);
                        last_i = i + 1
                    }
                }
                _ => (),
            }
        }
        subterms_txt.push(&text[last_i..]);
        subterms_txt
            .iter()
            .map(|sub_term| {
                if complex_term(sub_term) {
                    self.build_heap_term_rec(sub_term, symbols_map, uni_vars)
                } else {
                    SubTerm::TEXT(sub_term.to_string())
                }
            })
            .collect()
    }

    fn text_structure(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        let i1 = text.find('(').unwrap();
        let i2 = text.rfind(')').unwrap();
        let sub_terms = self.handle_sub_terms(&text[i1 + 1..i2], symbols_map, uni_vars);
        let i = self.cells.len();
        self.cells.push((Heap::STR, sub_terms.len()));
        self.text_singlet(&text[..i1], symbols_map, uni_vars);
        for sub_term in sub_terms {
            match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => self.cells.push(cell),
            }
        }
        SubTerm::CELL((Heap::STR_REF, i))
    }

    fn text_list(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        if text == "[]" {
            return SubTerm::CELL((Heap::LIS, Heap::CON));
        }
        let i1 = text.find('[').unwrap() + 1;
        let mut i2 = text.rfind(']').unwrap();
        let mut explicit_tail = false;
        i2 = match text.rfind('|') {
            Some(i) => {
                explicit_tail = true;
                i
            }
            None => i2,
        };
        let subterms = self.handle_sub_terms(&text[i1..i2], symbols_map, uni_vars);
        let tail = if explicit_tail {
            Some(
                self.handle_sub_terms(
                    &text[i2 + 1..text.rfind(']').unwrap()],
                    symbols_map,
                    uni_vars,
                )[0]
                .clone(),
            )
        } else {
            None
        };
        let i = self.cells.len();
        for sub_term in subterms {
            match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => {
                    self.cells.push(cell);
                }
            }
            self.cells.push((Heap::LIS, self.cells.len() + 1))
        }
        self.cells.pop(); //Remove last LIS tag cell
        match tail {
            Some(sub_term) => match sub_term {
                SubTerm::TEXT(text) => {
                    self.text_singlet(&text, symbols_map, uni_vars);
                }
                SubTerm::CELL(cell) => {
                    self.cells.push(cell);
                }
            },
            None => self.cells.push((Heap::LIS, Heap::CON)),
        }
        SubTerm::CELL((Heap::LIS, i))
    }

    fn build_heap_term_rec(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> SubTerm {
        let list_open = match text.find('[') {
            Some(i) => i,
            None => usize::MAX,
        };
        let brackets_open = match text.find('(') {
            Some(i) => i,
            None => usize::MAX,
        };
        if list_open == usize::MAX && brackets_open == usize::MAX {
            panic!("help")
        } else {
            if list_open < brackets_open {
                self.text_list(text, symbols_map, uni_vars)
            } else {
                self.text_structure(text, symbols_map, uni_vars)
            }
        }
    }

    pub fn build_literal(
        &mut self,
        text: &str,
        symbols_map: &mut HashMap<String, usize>,
        uni_vars: &Vec<&str>,
    ) -> usize {
        match self.build_heap_term_rec(text, symbols_map, uni_vars) {
            SubTerm::TEXT(_) => self.cells.len() - 1,
            SubTerm::CELL((Heap::STR, i)) => i,
            SubTerm::CELL((Heap::LIS, i)) => {self.cells.push((Heap::LIS, i)); self.cells.len()-1},
            SubTerm::CELL((Heap::REF| Heap::STR_REF, i)) => {self.deref(i)},
            SubTerm::CELL((tag,i)) => panic!("Unkown LIteral type: ({tag},{i}"),
        }
    }
}

fn complex_term(text: &str) -> bool {
    text.chars().any(|c| c == '(' || c == '[')
}
