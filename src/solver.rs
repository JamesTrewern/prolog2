use std::collections::btree_map::Range;

use crate::{
    atoms::Atom,
    clause::Clause,
    heap::Heap,
    program::{Choice, Program},
    terms::Substitution,
};

const MAX_H_SIZE: usize = 2;
const NO_SHARED_PREDICATES: bool = true;
const DEBUG: bool = true;
#[derive(Debug)]
struct Env {
    goal: Atom,
    subs: Option<Substitution>,
    choices: Vec<Choice>,
    new_clause: Option<usize>,
    children: usize,
    depth: usize,
}

impl Env {
    pub fn new(goal: Atom, depth: usize) -> Env {
        Env {
            goal,
            subs: None,
            choices: vec![],
            new_clause: None,
            children: 0,
            depth,
        }
    }
}

pub fn prove(prog: &Program, goals: Vec<Atom>, heap: &mut Heap) {
    let mut proof_stack: Vec<Env> = vec![];
    let mut h: Hypothesis = Hypothesis::new(prog.constraints.clone());

    for goal in &goals {
        proof_stack.push(Env::new(goal.clone(), 0));
    }

    if call(prog, &mut proof_stack, 0, &mut h, heap) {
        println!("\nTRUE");
        h.write_prog(heap);
        //TO DO if next user input in space retry from pointer
    } else {
        println!("\nFALSE");
        print_stack(&mut proof_stack, heap);
    }
    for goal in goals {
        println!("{}", goal.to_string(heap));
    }
}

fn call(
    prog: &Program,
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    h: &mut Hypothesis,
    heap: &mut Heap,
) -> bool {
    let env = match proof_stack.get_mut(pointer) {
        Some(e) => e,
        None => {
            return true;
        }
    };
    if DEBUG {
        println!("[{}]: {}", env.depth, env.goal.to_string(heap));
    }
    let mut choices = prog.match_head_to_goal(&env.goal, heap, false);
    choices.append(&mut h.match_head_to_goal(&env.goal, heap));

    //If H is max length, remove choices that add new clause.
    choices.retain(|choice| filter_choice(prog, h, heap, choice));

    if choices.is_empty() {
        if DEBUG {
            println!("[{}]FAILED: {}", env.depth, env.goal.to_string(heap));
        }
        return retry(prog, proof_stack, pointer, h, heap);
    }

    let mut choice = choices.pop().unwrap();
    env.choices = choices;
    apply_choice(prog, proof_stack, pointer, h, heap, choice);
    call(prog, proof_stack, pointer + 1, h, heap)
}

fn retry(
    prog: &Program,
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    h: &mut Hypothesis,
    heap: &mut Heap,
) -> bool {
    let children = proof_stack.get(pointer).unwrap().children;
    for _ in 0..children {
        proof_stack.remove(pointer + 1);
    }
    let env = proof_stack.get_mut(pointer).unwrap();
    //Undo Enviroment
    if let Some(subs) = &env.subs {
        heap.undo_sub(subs)
    }
    if env.new_clause != None {
        h.clauses.pop();
    }

    //is pointer a choice point
    if env.choices.is_empty() {
        if pointer == 0 {
            return false;
        } else {
            return retry(prog, proof_stack, pointer - 1, h, heap);
        }
    } else {
        if DEBUG {
            println!("[{}]RETRY: {}", env.depth, env.goal.to_string(heap));
        }
        let choice = env.choices.pop().unwrap();
        apply_choice(prog, proof_stack, pointer, h, heap, choice);
        call(prog, proof_stack, pointer + 1, h, heap)
    }
}

fn apply_choice(
    prog: &Program,
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    h: &mut Hypothesis,
    heap: &mut Heap,
    mut choice: Choice,
) -> bool {
    let env = proof_stack.get_mut(pointer).unwrap();
    choice.choose(heap);
    env.children = choice.goals.len();
    heap.apply_sub(&choice.subs);
    env.subs = Some(choice.subs);
    if let Some(clause) = choice.new_clause {
        env.new_clause = Some(h.add_clause(clause, heap));
    }
    let depth = env.depth + 1;

    for goal in choice.goals.into_iter().rev() {
        proof_stack.insert(pointer + 1, Env::new(goal, depth));
    }
    true
}

fn filter_choice(prog: &Program, h: &mut Hypothesis, heap: &mut Heap, choice: &Choice) -> bool {
    if h.max_length() && choice.new_clause != None {
        return false;
    }
    return h.valid_sub(&choice.subs, heap, prog);
}

fn print_stack(proof_stack: &mut Vec<Env>, heap: &mut Heap) {
    for env in proof_stack {
        println!("[{}]: {}", env.depth, env.goal.to_string(heap));
    }
}
struct Hypothesis {
    clauses: Vec<Clause>,
    constraints: Vec<Clause>,
}

impl Hypothesis {
    pub fn new(constraints: Vec<Clause>) -> Hypothesis {
        Hypothesis {
            clauses: vec![],
            constraints,
        }
    }

    pub fn add_clause(&mut self, clause: Clause, heap: &Heap) -> usize {
        println!("New Clause:   {}", clause.to_string(heap));
        self.clauses.push(clause);
        println!("H size:   {}", self.clauses.len());
        return self.clauses.len() - 1;
    }

    pub fn write_prog(&self, heap: &Heap) {
        for clause in self.clauses.iter() {
            println!("{}", clause.to_string(heap));
        }
    }

    pub fn match_head_to_goal(&self, goal: &Atom, heap: &mut Heap) -> Vec<Choice> {
        let mut choices: Vec<Choice> = vec![];
        for clause in &self.clauses {
            match clause.atoms[0].unify(&goal, heap) {
                Some(mut subs) => {
                    println!(
                        "Matched: {}\nSubs:   {}",
                        clause.to_string(heap),
                        subs.to_string(heap)
                    );
                    let goals_clause = clause.body().apply_sub(&subs);

                    let subbed_clause = clause.apply_sub(&subs);
                    //println!("Subbed C: {}", subbed_clause.to_string());
                    if self.constraints.iter().any(|c| {
                        if c.can_unfiy(&subbed_clause, heap) {
                            println!("Denied: {}", subbed_clause.to_string(heap));
                            println!("Contraint: {}", c.to_string(heap));
                            true
                        } else {
                            false
                        }
                    }) {
                        continue;
                    }

                    choices.push(Choice {
                        goals: goals_clause.atoms,
                        subs,
                        new_clause: None,
                    })
                }
                None => (),
            }
        }
        return choices;
    }

    pub fn valid_sub(&self, sub: &Substitution, heap: &mut Heap, prog: &Program) -> bool {
        //TO DO ignore subs with no relevence
        for clause in self.clauses.iter() {
            if !clause.terms().iter().any(|t| sub.subs.contains_key(t)) {
                continue;
            }
            let subbed_clause = clause.apply_sub(sub);
            if self.constraints.iter().any(|c| {
                if c.can_unfiy(&subbed_clause, heap) {
                    true
                } else {
                    false
                }
            }) {
                println!("{}", subbed_clause.to_string(heap));
                return false;
            }
            //TO DO use heap to find end of ref chain if not right enum type
            let head_symbol = heap.get_i(heap.get_term(subbed_clause.atoms[0].terms[0]));
            if prog
                .predicate_symbols
                .contains(&head_symbol)
            {
                return false;
            }
        }
        return true;
    }

    pub fn max_length(&mut self) -> bool {
        self.clauses.len() == MAX_H_SIZE
    }
}
