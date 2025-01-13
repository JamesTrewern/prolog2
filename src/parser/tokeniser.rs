use std::str::CharIndices;
use fsize::fsize;

enum ParseError {
    CommentError(String, usize),         //Message, line
    TokeniseError(String, usize, usize), //Message, line, column.
    TermError(String, usize),            //Message, line
}

const DELIMINATORS: &[char] = &[
    '(', ')', ',', '.', ' ', '\n', '\t', '\\', ':', '-', '+', '/', '*', '=', '[', ']', '|', '>',
    '<', '{', '}',
];
const KNOWN_SYMBOLS: &[&str] = &[":-", "==", "=/=", "/=", "=:=", "**", "<=", ">=", "/*", "*/"];
const INFIX_ORDER: &[&[&str]] = &[
    &["**"],
    &["*", "/"],
    &["+", "-"],
    &["==", "=/=", "/=", "=:=", "is"],
];

// --------------------------------------------------------------------------------------
// Tokenise File
// --------------------------------------------------------------------------------------

pub fn remove_comments(file: &mut String) {
    //TODO Must ingore % if in string
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

fn form_empty_list_token(tokens: &mut Vec<String>) {
    let mut i = 0;
    while tokens.len() > i + 2 {
        if tokens[i] == "[" {
            let mut j = i+1;
            loop {
                if tokens[j].chars().all(|c| c.is_whitespace()){
                    j+=1;
                }else if tokens[j] == "]" {
                    tokens.drain(i..j+1);
                    tokens.insert(i, "[]".into());
                    break;
                }else{
                    break
                }
            }
        }
        i += 1;
    }


}

fn walk_string(iterator: &mut CharIndices, mark: char) -> Result<usize, ()> {
    while let Some((i, c)) = iterator.next() {
        if c == mark {
            return Ok(i);
        } else if c == '\\' {
            iterator.next();
        }
    }
    Err(())
}

/* If two numerical tokens are split by a '.' char unify into one token
*/
fn join_decimal_nums(tokens: &mut Vec<String>) {
    let mut i = 0;
    while tokens.len() > i + 2 {
        i += 1;
        if tokens[i] == "."
            && tokens[i - 1].chars().all(|c| c.is_numeric())
            && tokens[i + 1].chars().all(|c| c.is_numeric())
        {
            let combined_value = [
                tokens[i - 1].as_str(),
                tokens[i].as_str(),
                tokens[i + 1].as_str(),
            ]
            .concat();
            tokens.remove(i + 1);
            tokens.remove(i);
            tokens.remove(i - 1);
            tokens.insert(i - 1, combined_value);
        }
    }
}

/* If a substract sign is at the front of number unifiy into one token
*/
fn form_negative_nums(tokens: &mut Vec<String>) {
    let mut i = 0;
    while tokens.len() > i + 2 {
        if tokens[i] == "-" && tokens[i + 1].chars().all(|c| c.is_numeric() || c == '.') {
            let combined_value = [tokens[i].as_str(), tokens[i + 1].as_str()].concat();
            tokens.remove(i + 1);
            tokens.remove(i);
            tokens.insert(i, combined_value);
        }
        i += 1;
    }
}

fn form_known_symbols(tokens: &mut Vec<String>) {
    let mut i = 0;
    while i < tokens.len()-1{
        if DELIMINATORS.contains(&tokens[i].chars().next().unwrap()) {
            for &symbol in KNOWN_SYMBOLS{
                if symbol.len() <= tokens.len()-i{
                    if symbol == tokens[i..i+symbol.len()].concat(){
                        tokens.drain(i..i+symbol.len());
                        tokens.insert(i, symbol.into());
                    }
                }
            }
        }
        i += 1;
    }
}

pub fn tokenise(text: &str) -> Vec<String> {
    let mut tokens = Vec::<String>::new();
    let mut last_i = 0;
    let mut iterator = text.trim().char_indices();

    while let Some((i, c)) = iterator.next() {
        if c == '\'' || c == '"' {
            match walk_string(&mut iterator, c) {
                Ok(i2) => {
                    tokens.push(text[i..i2].into());
                    last_i = i2 + 1
                }
                Err(_) => todo!(),
            }
        }

        if DELIMINATORS.contains(&c) {
            tokens.push(text[last_i..i].into());
            tokens.push(c.into());
            last_i = i + 1;
        }
    }
    tokens.push(text[last_i..].into());
    tokens.retain(|token| "" != *token);

    join_decimal_nums(&mut tokens);
    form_negative_nums(&mut tokens);
    form_known_symbols(&mut tokens);
    form_empty_list_token(&mut tokens);
    tokens.retain(|t1| !["\t", " "].iter().any(|t2| t1 == t2));
    tokens
}
