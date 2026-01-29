use super::term::{Term, TermClause};
use fsize::fsize;
use rayon::vec;
const DELIMINATORS: &[char] = &[
    '(', ')', ',', '.', ' ', '\n', '\t', '\\', ':', '-', '+', '/', '*', '=', '[', ']', '|', '>',
    '<', '{', '}',
];
const KNOWN_SYMBOLS: &[&str] = &[":-", "==", "=/=", "/=", "=:=", "**", "<=", ">="];
const INFIX_ORDER: &[&[&str]] = &[
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &["==", "=/=", "/=", "=:=", "is"],
];

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
    let mut iterator = text.char_indices();

    'outer: while let Some((i, c)) = iterator.next() {
        if c == '\'' {
            while let Some((i, c)) = iterator.next() {
                if c == '\'' {
                    tokens.push(&text[last_i..=i]);
                    last_i = i + 1;
                    break;
                }else if c == '\\'{
                    iterator.next();
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

    i = 0;
    while tokens.len() > i + 1 {
        if tokens[i] == "-" && tokens[i + 1].chars().all(|c| c.is_numeric() || c == '.') {
            let combined_value = [tokens[i], tokens[i + 1]].concat();
            let text_i = text.find(&combined_value).unwrap();
            tokens.remove(i + 1);
            tokens.remove(i);
            tokens.insert(i, &text[text_i..text_i + combined_value.len()]);
        }
        i += 1;
    }

    i = 0;
    while tokens.len() > i + 1 {
        if tokens[i] == "[" && tokens[i + 1] == "]" {
            let combined_value = [tokens[i], tokens[i + 1]].concat();
            let text_i = text.find(&combined_value).unwrap();
            tokens.remove(i + 1);
            tokens.remove(i);
            tokens.insert(i, &text[text_i..text_i + combined_value.len()]);
        }
        i += 1;
    }

    i = 0;
    while tokens.len() > i + 2 {
        if tokens[i] == "-" && tokens[i + 1] == "-" && tokens[i + 2] == ">" {
            tokens.drain(i..i + 3);
            tokens.insert(i, "-->");
        }
        i += 1;
    }

    tokens.retain(|token| ![" ", "\t", "\r"].contains(token));

    tokens
}

fn infix_order(operator: &str) -> usize {
    INFIX_ORDER
        .iter()
        .position(|ops| ops.contains(&operator))
        .unwrap()
}

fn parse_atom(token: &str, uqvars: &Vec<&str>) -> Term {
    if let Ok(num) = token.parse::<isize>() {
        return Term::INT(num);
    }
    if let Ok(num) = token.parse::<fsize>() {
        return Term::FLT(num);
    }

    if token.chars().next().unwrap().is_uppercase() {
        if uqvars.contains(&token) {
            Term::VARUQ(token.into())
        } else {
            Term::VAR(token.into())
        }
    } else {
        if token.chars().next() == Some('\'') && token.chars().last() == Some('\'') {
            Term::CON(token[1..token.len() - 1].into())
        } else {
            Term::CON(token.into())
        }
    }
}

fn resolve_infix(term_stack: &mut Vec<Term>, op_stack: &mut Vec<Term>, max_prescendence: usize) {
    while !op_stack.is_empty()
        && INFIX_ORDER
            .iter()
            .any(|ops| ops.contains(&op_stack.last().unwrap().symbol()))
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
    let op = op_stack.pop().unwrap();
    let mut list_term: Term = if op.symbol() == "|" {
        term_stack.pop().unwrap()
    } else if op.symbol() == "[" {
        let t = Term::LIS(term_stack.pop().unwrap().into(), Term::EMPTY_LIS.into());
        term_stack.push(t);
        return Ok(());
    } else {
        Term::LIS(
            Box::new(term_stack.pop().unwrap()),
            Box::new(Term::EMPTY_LIS),
        )
    };

    loop {
        let op = op_stack.pop().unwrap();

        list_term = Term::LIS(Box::new(term_stack.pop().unwrap()), Box::new(list_term));
        if op.symbol() == "|" {
            return Err(format!(
                "List tail must be at most one term: [..|{list_term}]",
            ));
        } else if op.symbol() == "[" {
            break;
        } else if op.symbol() != "," {
            return Err(format!("Incorrectly formatted list"));
        }
    }
    term_stack.push(list_term);
    Ok(())
}

//TO DO use {X,Y} notation for Univerally Quantified vars
fn get_uq_vars<'a>(tokens: &[&'a str]) -> Result<Option<Vec<&'a str>>, String> {
    match tokens.iter().position(|token| *token == "{") {
        Some(i) => {
            let mut uqvars = Vec::<&str>::new();
            for token in &tokens[i + 1..] {
                if token.chars().next().unwrap().is_uppercase() {
                    uqvars.push(*token);
                } else if *token == "}" {
                    break;
                } else if *token != "," && *token != "." {
                    return Err(format!(
                        "Universally quantified varibles incorrectly formatted: {}",
                        tokens[i..].concat()
                    ));
                }
            }
            Ok(Some(uqvars))
        }
        None => Ok(None),
    }
}

pub fn parse_clause(mut tokens: &[&str]) -> Result<TermClause, String> {    
    if tokens.contains(&"-->") {
        return Ok(parse_dcg(tokens));
    }

    let mut meta = false;
    let uqvars = match get_uq_vars(&tokens)? {
        Some(uqvars) => {
            tokens = &tokens[0..tokens.iter().position(|t| *t == "{").unwrap()];
            meta = true;
            uqvars
        }
        None => Vec::new(),
    };

    let literals = parse_literals(tokens, &uqvars)?;

    Ok(TermClause { literals, meta })
}

pub fn parse_goals(tokens: &[&str]) -> Result<Vec<Term>, String> {
    parse_literals(tokens, &vec![])
}

fn parse_literals(tokens: &[&str], uqvars: &Vec<&str>) -> Result<Vec<Term>, String> {
    let mut term_stack: Vec<Term> = Vec::new();
    let mut op_stack: Vec<Term> = Vec::new();
    for token in tokens {

        if ["{", "."].contains(&token) {
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
        } else if *token == "[]" {
            term_stack.push(Term::EMPTY_LIS);
        } else if INFIX_ORDER.iter().any(|ops| ops.contains(&token)) {
            resolve_infix(&mut term_stack, &mut op_stack, infix_order(token));
            op_stack.push(parse_atom(token, &uqvars));
        } else if *token != "\n" {
            term_stack.push(parse_atom(token, &uqvars));
        }
    }
    resolve_infix(&mut term_stack, &mut op_stack, INFIX_ORDER.len());
    Ok(term_stack)
}

fn parse_dcg(tokens: &[&str]) -> TermClause {
    println!("{tokens:?}");
    let symbol = Term::CON(tokens[0].into());
    if let Some(Term::LIS(terminal, tail)) = parse_literals(&tokens[2..], &vec![]).unwrap().pop() {
        return TermClause {
            literals: [Term::STR(
                [
                    symbol,
                    Term::LIS(terminal, Term::VAR("A".into()).into()),
                    Term::VAR("A".into()),
                ]
                .into(),
            )]
            .into(),
            meta: false,
        };
    } else {
        panic!()
    }

    todo!()
}
