use fsize::fsize;
use std::str::CharIndices;

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

pub fn remove_comments(mut file: String) -> Result<String, String> {
    //TODO Must ingore % if in string
    let mut i = 0;
    Ok(file)
}

fn form_empty_list_token(tokens: &mut Vec<String>) {
    let mut i = 0;
    while tokens.len() > i + 1 {
        if tokens[i] == "[" {
            let mut j = i + 1;
            let mut new_lines = 0;
            loop {
                match tokens[j].as_str() {
                    " " | "\t" => j += 1,
                    "\n" => {
                        new_lines += 1;
                        j += 1;
                    }
                    "]" => {
                        tokens.drain(i..j + 1);
                        tokens.insert(i, "[]".into());
                        for _ in 0..new_lines {
                            tokens.insert(i + 1, "\n".into());
                        }
                        break;
                    }
                    _ => break,
                }
            }
        }
        i += 1;
    }
}

fn form_empty_set_token(tokens: &mut Vec<String>) {
    let mut i = 0;
    while tokens.len() > i + 1 {
        if tokens[i] == "{" {
            let mut j = i + 1;
            let mut new_lines = 0;
            loop {
                match tokens[j].as_str() {
                    " " | "\t" => j += 1,
                    "\n" => {
                        new_lines += 1;
                        j += 1;
                    }
                    "}" => {
                        tokens.drain(i..j + 1);
                        tokens.insert(i, "{}".into());
                        for _ in 0..new_lines {
                            tokens.insert(i + 1, "\n".into());
                        }
                        break;
                    }
                    _ => break,
                }
            }
        }
        i += 1;
    }
}

fn form_empty_tuple_token(tokens: &mut Vec<String>) {
    let mut i = 0;
    while tokens.len() > i + 1 {
        if tokens[i] == "(" {
            let mut j = i + 1;
            let mut new_lines = 0;
            loop {
                match tokens[j].as_str() {
                    " " | "\t" => j += 1,
                    "\n" => {
                        new_lines += 1;
                        j += 1;
                    }
                    ")" => {
                        tokens.drain(i..j + 1);
                        tokens.insert(i, "()".into());
                        for _ in 0..new_lines {
                            tokens.insert(i + 1, "\n".into());
                        }
                        break;
                    }
                    _ => break,
                }
            }
        }
        i += 1;
    }
}


fn walk_string(characters: &Vec<char>, mut i: usize, mark: char) -> Result<(String,usize), String> {
    //TODO more complex escape character processing
    let mut str = vec![mark];
    while let Some(&c) = characters.get(i) {
        match c {
            c if c == mark => {
                str.push(c);
                return Ok((str.iter().collect(),i+1));
            }
            '\\' => {
                match characters.get(i+1) {
                    Some('n') => str.push('\n'),
                    Some('t') => str.push('\t'),
                    Some('\\') => str.push('\\'), 
                    Some('"') => str.push('"'),
                    Some('\'') => str.push('\''),
                    Some(_) => return Err("'\\' used without proper escape character".into()),
                    None => break
                }
                i+=2
            }  
            _ => {str.push(c);i += 1;},
        }
    }
    Err(format!("Unexpected end of file, missing closing {mark}"))
}

fn walk_multi_line_comment(characters: &Vec<char>, mut i: usize) -> Result<(usize, usize), String> {
    let mut newlines = 0;
    while i <= characters.len() - 2 {
        if characters[i] == '\n' {
            newlines += 1
        }
        if &characters[i..i + 2] == ['*', '/'] {
            return Ok((i + 2, newlines));
        }
        i += 1;
    }
    Err("Unclosed multi line comment".into())
}

fn walk_single_line_comment(characters: &Vec<char>, mut i: usize) -> Result<usize, ()> {
    //TODO more complex escape character processing
    while let Some(&c) = characters.get(i) {
        if c == '\n' {
            return Ok(i+1);
        }
        i += 1;
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
    while tokens.len() > i + 1 {
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
    while i < tokens.len() - 1 {
        if DELIMINATORS.contains(&tokens[i].chars().next().unwrap()) {
            for &symbol in KNOWN_SYMBOLS {
                if symbol.len() <= tokens.len() - i {
                    if symbol == tokens[i..i + symbol.len()].concat() {
                        tokens.drain(i..i + symbol.len());
                        tokens.insert(i, symbol.into());
                    }
                }
            }
        }
        i += 1;
    }
}

pub fn tokenise(text: String) -> Result<Vec<String>, String> {
    let mut tokens = Vec::<String>::new();
    let mut last_i = 0;
    let characters: Vec<char> = text.chars().collect();
    let mut i = 0;

    while i < characters.len() {
        // println!("{tokens:?}");
        let c = characters[i];
        match c {
            '\'' | '"' => {
                let (token,i2) = walk_string(&characters, i+1, c)?;
                tokens.push(token);
                i = i2;
                last_i = i;
            }
            '%' => match walk_single_line_comment(&characters, i+1) {
                Ok(i2) => {
                    i = i2;
                    last_i = i;
                    tokens.push("\n".into());
                }
                Err(_) => {
                    i = characters.len();
                    last_i = i;
                    break;
                }
            },
            '/' => {
                if characters[i + 1] == '*' {
                    let (i2, newlines) = walk_multi_line_comment(&characters, i + 1)?;
                    i = i2;
                    last_i = i;
                    for _ in 0..newlines {
                        tokens.push("\n".into());
                    }
                }else{
                    tokens.push(text[last_i..i].into());
                    tokens.push(c.into());
                    i += 1;
                    last_i = i;
                }
            }
            c if DELIMINATORS.contains(&c) => {
                tokens.push(text[last_i..i].into());
                tokens.push(c.into());
                i += 1;
                last_i = i;
            }
            _ => i += 1,
        }
    }
    tokens.push(text[last_i..].into());
    tokens.retain(|token| "" != *token);
    form_known_symbols(&mut tokens);
    join_decimal_nums(&mut tokens);
    form_negative_nums(&mut tokens);
    form_empty_list_token(&mut tokens);
    form_empty_set_token(&mut tokens);
    form_empty_tuple_token(&mut tokens);
    tokens.retain(|t1| !["\t", " "].iter().any(|t2| t1 == t2));
    Ok(tokens)
}
