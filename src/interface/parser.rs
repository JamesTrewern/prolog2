use std::collections::HashMap;
use super::term::Term;

const DELIMINATORS: &[char] = &[
    '(', ')', ',', '.', ' ', '\n', '\t', '\\', ':', '-', '+', '/', '*', '=', '[', ']', '|', '>', '<',
];
const KNOWN_SYMBOLS: &[&str] = &[":-", "==", "=/=", "/=", "=:=", "**", "<=", ">="];
const INFIX_ORDER: &[&str] = &["**", "*", "/", "+", "-", "==", "=/=", "/=", "=:=", "is"];

pub fn remove_comments(file: &mut String) {
    //Must ingore % if in string
    let mut i = 0;
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

pub fn tokenise(text: &str) -> Vec<&str> {
    let mut tokens = Vec::<&str>::new();
    let mut last_i = 0;
    let mut iterator = text.chars().enumerate();

    'outer: while let Some((i, c)) = iterator.next() {
        if c == '\'' {
            while let Some((i, c)) = iterator.next() {
                if c == '\'' {
                    tokens.push(&text[last_i..=i]);
                    last_i = i + 1;
                    break;
                }
            }
            continue;
        }

        if c == '"' {
            while let Some((i, c)) = iterator.next() {
                if c == '"' {
                    tokens.push(&text[last_i..=i]);
                    last_i = i + 1;
                    break;
                }
            }
            continue;
        }

        if DELIMINATORS.contains(&c) {
            tokens.push(&text[last_i..i]);

            //Check for know symbols which are combinations of deliminators
            for symbol in KNOWN_SYMBOLS {
                if symbol.len() + i >= text.len() {
                    continue;
                }
                if **symbol == text[i..i + symbol.len()] {
                    tokens.push(&text[i..i + symbol.len()]);
                    for _ in 0..symbol.len() - 1 {
                        iterator.next();
                    }
                    last_i = i + symbol.len();
                    continue 'outer;
                }
            }

            tokens.push(&text[i..=i]);
            last_i = i + 1;
        }
    }

    tokens.retain(|token| "" != *token);

    let mut i = 0;
    while tokens.len() > i + 2 {
        i += 1;
        if tokens[i] == "."
            && tokens[i - 1].chars().all(|c| c.is_numeric())
            && tokens[i + 1].chars().all(|c| c.is_numeric())
        {
            let combined_value = [tokens[i - 1], tokens[i], tokens[i + 1]].concat();
            let text_i = text.find(&combined_value).unwrap();
            tokens.remove(i + 1);
            tokens.remove(i);
            tokens.remove(i - 1);
            tokens.insert(i - 1, &text[text_i..text_i + combined_value.len()]);
        }
    }

    tokens.retain(|token| ![" ", "\t", "\r"].contains(token));

    tokens
}

fn infix_order(operator: &str) -> usize {
    INFIX_ORDER.iter().position(|op| *op == operator).unwrap()
}

fn parse_atom(token: &str, uqvars: &Vec<&str>) -> Term {
    match token.parse::<isize>() {
        Ok(num) => Term::INT(num),
        Err(_) => match token.parse::<f64>() {
            Ok(num) => Term::FLT(num),
            Err(_) => {
                if token.chars().next().unwrap().is_uppercase() {
                    if uqvars.contains(&token) {
                        Term::VARUQ(token.into())
                    } else {
                        Term::VAR(token.into())
                    }
                } else {
                    Term::CON(token.into())
                }
            }
        },
    }
}

fn resolve_infix(term_stack: &mut Vec<Term>, op_stack: &mut Vec<Term>, max_prescendence: usize) {
    while !op_stack.is_empty()
        && INFIX_ORDER.contains(&op_stack.last().unwrap().symbol())
        && infix_order(op_stack.last().unwrap().symbol()) <= max_prescendence
    {
        let op = op_stack.pop().unwrap();
        let right = term_stack.pop().unwrap();
        let left = term_stack.pop().unwrap();
        term_stack.push(Term::STR([op, left, right].into()));
    }
}

fn build_str(term_stack: &mut Vec<Term>, op_stack: &mut Vec<Term>) -> Result<(), String> {
    resolve_infix(term_stack, op_stack, INFIX_ORDER.len());
    let mut str_terms = Vec::<Term>::new();
    loop {
        let op = op_stack.pop().unwrap();
        let term = term_stack.pop().unwrap();
        if op.symbol() == "," {
            str_terms.push(term);
        } else {
            str_terms.push(term);
            str_terms.push(op);
            break;
        }
    }
    str_terms = str_terms.into_iter().rev().collect();
    term_stack.push(Term::STR(str_terms.into_boxed_slice()));
    Ok(())
}

fn build_list(term_stack: &mut Vec<Term>, op_stack: &mut Vec<Term>) -> Result<(), String> {
    resolve_infix(term_stack, op_stack, INFIX_ORDER.len());
    let mut lis_terms = Vec::<Term>::new();
    let mut explicit_tail = false;
    loop {
        let op = op_stack.pop().unwrap();
        let term = term_stack.pop().unwrap();
        lis_terms.push(term);
        if op.symbol() == "|" {
            if lis_terms.len() > 1 {
                return Err(format!(
                    "List tail must be at most one term: [..|{}]",
                    lis_terms
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<String>>()
                        .concat()
                ));
            }
            explicit_tail = true;
        } else if op.symbol() == "[" {
            break;
        } else if op.symbol() != "," {
            return Err(format!("Incorrectly formatted list"));
        }
    }
    lis_terms = lis_terms.into_iter().rev().collect();
    term_stack.push(Term::LIS(lis_terms, explicit_tail));
    Ok(())
}

fn get_uq_vars<'a>(tokens: &[&'a str]) -> Result<Vec<&'a str>, String> {
    match tokens.iter().position(|token| *token == "\\") {
        Some(i) => {
            let mut uqvars = Vec::<&str>::new();
            for token in &tokens[i + 1..] {
                if token.chars().next().unwrap().is_uppercase() {
                    uqvars.push(*token);
                } else if *token != "," && *token != "." {
                    return Err(format!(
                        "Universally quantified varibles incorrectly formatted: {}",
                        tokens[i..].concat()
                    ));
                }
            }
            Ok(uqvars)
        }
        None => Ok(Vec::new()),
    }
}

pub fn parse_literals(tokens: &[&str]) -> Result<Vec<Term>, String> {
    let mut term_stack: Vec<Term> = Vec::new();
    let mut op_stack: Vec<Term> = Vec::new();

    let uqvars = get_uq_vars(&tokens)?;

    for token in tokens {
        if ["\\", "."].contains(&token) {
            resolve_infix(&mut term_stack, &mut op_stack, INFIX_ORDER.len());
            break;
        }
        if *token == "(" {
            op_stack.push(term_stack.pop().unwrap());
        } else if [",", ":-", "|"].contains(&token) {
            resolve_infix(&mut term_stack, &mut op_stack, INFIX_ORDER.len());
            op_stack.push(parse_atom(token, &uqvars));
        } else if *token == ")" {
            build_str(&mut term_stack, &mut op_stack)?;
        } else if *token == "[" {
            op_stack.push(parse_atom(token, &uqvars));
        } else if *token == "]" {
            build_list(&mut term_stack, &mut op_stack)?
        } else if INFIX_ORDER.contains(&token) {
            resolve_infix(&mut term_stack, &mut op_stack, infix_order(token));
            op_stack.push(parse_atom(token, &uqvars));
        } else if *token != "\n"{
            term_stack.push(parse_atom(token, &uqvars));
        }
    }
    Ok(term_stack)
}