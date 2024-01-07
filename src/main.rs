use std::io;

use atoms::Atom;
use heap::Heap;
use program::Program;
use proof::Proof;
use regex::Regex;

mod terms;
mod atoms;
mod clause;
mod program;
mod proof;
mod heap;



//TO DO only add vars to heap if choice is chosen
//Remove terms from heap when no longer needed
//New Clause rules: constraints, head can't be existing predicate
fn main() {
    let mut heap = Heap::new();
    let mut prog = Program::new();
    main_loop(heap,prog);
}

fn parse_goals(input: &mut String, heap: &mut Heap) -> Vec<Atom>{
    let mut goals: Vec<Atom> = vec![];
    let mut buf = String::new();

    input.retain(|c| !c.is_whitespace());

    let mut in_brackets = 0;
    for char in input.chars() {
        match char {
            ',' => {
                if in_brackets == 0 {
                    println!("{}",&buf);
                    goals.push(Atom::parse(&buf,heap,None));
                    buf = String::new();
                    continue;
                }
            }
            ')' => in_brackets -= 1,
            '(' => in_brackets += 1,
            '.' => {
                println!("{}",&buf);
                goals.push(Atom::parse(&buf,heap,None));
                break;
            }
            _ => (),
        }
        buf.push(char);
    }
    return goals;
}

fn main_loop(mut heap:Heap, mut prog: Program){
    let mut buf = String::new(); 
    let re = Regex::new(r"\[(?<file>\w+)\].").unwrap();
    while !buf.contains("quit.") {
        buf.clear();
        let _ = io::stdin().read_line(&mut buf);
        buf = buf.trim().to_string();
        if let Some(caps) = re.captures(&buf){
            let path = caps["file"].to_string() + ".pl";
            prog.parse_file(&path, &mut heap)
        }else{
            let goals = parse_goals(&mut buf, &mut heap);
            let mut proof = Proof::new(goals, &prog, &mut heap);
            proof.start_proof();
        }
    }
}
