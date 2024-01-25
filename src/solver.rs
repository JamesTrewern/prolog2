use crossterm::event::{self, read, KeyCode};

use crate::{
    atoms::{Atom, AtomHandler},
    clause::{Choice, ClauseHandler},
    heap::{Heap, HeapHandler},
    program::Program,
    terms::{Substitution, SubstitutionHandler},
    Config,
};

struct Env {
    goal: Atom,
    bindings: Substitution,
    choices: Vec<Choice>,
    new_clause: bool,
    invent_pred: bool,
    children: usize,
    depth: usize,
}

impl Env {
    pub fn new(goal: Atom, depth: usize) -> Env {
        Env {
            goal,
            bindings: vec![],
            choices: vec![],
            new_clause: false,
            children: 0,
            invent_pred: false,
            depth,
        }
    }
}

fn prove_again() -> bool {
    loop{
        match read().unwrap() {
            event::Event::Key(key) => {
                if key.code == KeyCode::Enter || key.code == KeyCode::Char('.'){
                    return false;
                } else if key.code == KeyCode::Char(';') || key.code == KeyCode::Char(' '){
                    return true;
                }
            },
            _ => ()
        }
    }
}

pub fn start_proof(goals: Vec<Atom>, prog: &mut Program, config: &mut Config, heap: &mut Heap) {
    let mut proof_stack: Vec<Env> = vec![];
    loop {
        if prove(goals.clone(), prog, config, heap, &mut proof_stack) {
            println!("TRUE");
            println!("{}", goals.to_string(heap));
            prog.write_h(heap);
            if !prove_again(){
                break;
            }
        } else {
            println!("FALSE");
            print_stack(&mut proof_stack, heap);
            break;
            // heap.print_heap();
        }
        prog.reset_h();
    }
}

fn prove(
    goals: Vec<Atom>,
    prog: &mut Program,
    config: &mut Config,
    heap: &mut Heap,
    proof_stack: &mut Vec<Env>,
) -> bool {
    for goal in &goals {
        proof_stack.push(Env::new(goal.clone(), 0));
    }

    let mut pointer = 0;

    loop {
        let env = match proof_stack.get_mut(pointer) {
            Some(e) => e,
            None => {
                return true;
            }
        };
        if env.depth == 10 {
            return false;
        }
        println!("[{}]Try: {}", env.depth, env.goal.to_string(heap));
        let mut choices = prog.call(&env.goal, heap, config);
        if choices.is_empty() {
            if config.debug {
                println!("[{}]FAILED: {}", env.depth, env.goal.to_string(heap));
            }
            match retry(proof_stack, pointer, prog, heap, config) {
                Some(p) => pointer = p,
                None => return false,
            }
        } else {
            let choice = choices.pop().unwrap();
            env.choices = choices;
            apply_choice(proof_stack, pointer, prog, heap, choice);
            pointer += 1;
        }
    }
}

fn retry(
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    prog: &mut Program,
    heap: &mut Heap,
    config: &Config,
) -> Option<usize> {
    let children = proof_stack.get(pointer).unwrap().children;
    for _ in 0..children {
        proof_stack.remove(pointer + 1);
    }
    let env = proof_stack.get_mut(pointer).unwrap();
    //Undo Enviroment
    println!(
        "[{pointer}]UNDO: {},{}",
        env.goal.to_string(heap),
        env.bindings.to_string(heap)
    );

    heap.unbind(&env.bindings);

    if env.new_clause == true {
        let c = prog.remove_h_clause(env.invent_pred).unwrap();
        println!("Remove Clause: {}", c.to_string(heap));
        env.new_clause = false;
    }

    //is pointer a choice point
    if env.choices.is_empty() {
        if pointer == 0 {
            return None;
        } else {
            return retry(proof_stack, pointer - 1, prog, heap, config);
        }
    } else {
        if config.debug {
            println!("[{}]RETRY: {}", env.depth, env.goal.to_string(heap));
        }
        let choice = env.choices.pop().unwrap();
        apply_choice(proof_stack, pointer, prog, heap, choice);
        return Some(pointer + 1);
    }
}

fn apply_choice(
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    prog: &mut Program,
    heap: &mut Heap,
    mut choice: Choice,
) -> bool {
    let env = proof_stack.get_mut(pointer).unwrap();
    env.children = choice.goals.len();
    //in goal clause eqs and aqs should be set to unbound ref
    //in new clause only eqs to be set to the same unbonf ref
    let mut eqs = choice.goals.terms();
    eqs.retain(|a| heap[*a].enum_type().contains("Var"));
    let mut subs: Substitution = vec![];
    for a in eqs {
        subs.insert_sub(a, heap.new_term(None))
    }
    choice.goals = choice.goals.apply_sub(&subs);

    if let Some(mut clause) = choice.new_clause {
        clause = clause.apply_sub(&subs.meta(heap));
        clause.aq_to_eq(heap);
        env.new_clause = true;
        //Invented pred?
        let pred_symbol = clause.pred_symbol();
        if let Some(v) = prog.add_h_clause(clause, heap) {
            env.invent_pred = true;
            choice.bindings.insert_sub(pred_symbol, v);
        }
    }
    // println!("Bindings: {}", choice.bindings.to_string(heap));
    heap.bind(&choice.bindings);
    env.bindings = choice.bindings;
    let depth = env.depth + 1;
    for goal in choice.goals.into_iter().rev() {
        proof_stack.insert(pointer + 1, Env::new(goal, depth));
    }
    true
}

fn print_stack(proof_stack: &mut Vec<Env>, heap: &mut Heap) {
    for env in proof_stack {
        println!("[{}]: {}", env.depth, env.goal.to_string(heap));
    }
}
