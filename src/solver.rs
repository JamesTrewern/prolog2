use crate::{
    binding::{Binding, BindingTraits},
    heap::Heap,
    program::{Choice, Clause, ClauseTraits},
    State,
};

struct Env {
    goal: usize, // Pointer to heap literal
    bindings: Binding,
    choices: Vec<Choice>,
    new_clause: bool,
    invent_pred: bool,
    children: usize,
    depth: usize,
}

impl Env {
    pub fn new(goal: usize, depth: usize) -> Env {
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
    todo!()
    // loop{
    //     match read().unwrap() {
    //         event::Event::Key(key) => {
    //             if key.code == KeyCode::Enter || key.code == KeyCode::Char('.'){
    //                 return false;
    //             } else if key.code == KeyCode::Char(';') || key.code == KeyCode::Char(' '){
    //                 return true;
    //             }
    //         },
    //         _ => ()
    //     }
    // }
}

pub fn start_proof(goals: Vec<usize>, state: &mut State) {
    let mut proof_stack: Vec<Env> = vec![];
    loop {
        if prove(goals.clone(), &mut proof_stack, state) {
            println!("TRUE");
            for goal in goals {
                println!("{},", state.heap.term_string(goal))
            }
            state.prog.write_h(&state.heap);
            // if !prove_again() {
            //     break;
            // }
        } else {
            println!("FALSE");
            print_stack(&mut proof_stack, &mut state.heap);
            break;
            // heap.print_heap();
        }
        // prog.reset_h();
        break;
    }
}

fn prove(goals: Vec<usize>, proof_stack: &mut Vec<Env>, state: &mut State) -> bool {
    for goal in &goals {
        proof_stack.push(Env::new(goal.clone(), 0));
    }

    let mut pointer = 0;

    loop {
        let (depth, goal) = match proof_stack.get_mut(pointer) {
            Some(e) => (e.depth, e.goal),
            None => {
                return true;
            }
        };
        if depth == state.config.max_depth {
            match retry(proof_stack, pointer, state) {
                Some(p) => {
                    pointer = p;
                }
                None => return false,
            }
        }
        println!("[{}]Try: {}", depth, state.heap.term_string(goal));
        let mut choices = state.prog.call(goal, &mut state.heap);

        println!("choices: {choices:?}");

        loop {
            if let Some(choice) = choices.pop() {
                if apply_choice(proof_stack, pointer, choice, state) {
                    let env  = proof_stack.get_mut(pointer).unwrap();
                    env.choices = choices;
                    pointer += 1;
                    break;
                }
            } else {
                if state.config.debug {
                    println!("[{}]FAILED: {}", depth, state.heap.term_string(goal));
                }
                match retry(proof_stack, pointer, state) {
                    Some(p) => {
                        pointer = p;
                        break;
                    }
                    None => return false,
                }
            }
        }
    }
}

fn retry(proof_stack: &mut Vec<Env>, pointer: usize, state: &mut State) -> Option<usize> {
    let children = proof_stack.get(pointer).unwrap().children;
    for _ in 0..children {
        proof_stack.remove(pointer + 1);
    }
    let env = proof_stack.get_mut(pointer).unwrap();
    //Undo Enviroment
    println!(
        "[{pointer}]UNDO: {},{}",
        state.heap.term_string(env.goal),
        env.bindings.to_string(&state.heap)
    );

    state.heap.unbind(&env.bindings);

    if env.new_clause == true {
        state.prog.remove_h_clause(env.invent_pred);
        env.new_clause = false;
    }

    //is pointer a choice point
    if env.choices.is_empty() {
        if pointer == 0 {
            return None;
        } else {
            return retry(proof_stack, pointer - 1, state);
        }
    } else {
        if state.config.debug {
            println!("[{}]RETRY: {}", env.depth, state.heap.term_string(env.goal));
        }
        let choice = env.choices.pop().unwrap();
        apply_choice(proof_stack, pointer, choice, state);
        return Some(pointer + 1);
    }
}

fn apply_choice(
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    mut choice: Choice,
    state: &mut State,
) -> bool {
    if let Some((goals, invented_pred)) = choice.choose(state) {
        let env = proof_stack.get_mut(pointer).unwrap();
        env.children = goals.len();
        env.bindings = choice.binding;
        env.new_clause = choice.new_clause;
        env.invent_pred = invented_pred;
        let depth = env.depth + 1;
        for goal in goals {
            proof_stack.insert(pointer + 1, Env::new(goal, depth));
        }
        true
    } else {
        false
    }
}

fn print_stack(proof_stack: &mut Vec<Env>, heap: &mut Heap) {
    for env in proof_stack {
        println!("[{}]: {}", env.depth, heap.term_string(env.goal));
    }
}
