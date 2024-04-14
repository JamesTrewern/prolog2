use crate::{binding::{Binding, BindingTraits}, heap::Heap, program::{program::Choice, Clause, ClauseTraits}, State};


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
                print!("{},",state.heap.term_string(goal))
            }
            state.prog.write_h(&state.heap);
            if !prove_again(){
                break;
            }
        } else {
            println!("FALSE");
            print_stack(&mut proof_stack, &mut state.heap);
            break;
            // heap.print_heap();
        }
        // prog.reset_h();
    }
}

fn prove(
    goals: Vec<usize>,
    proof_stack: &mut Vec<Env>,
    state: &mut State,
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
        println!("[{}]Try: {}", env.depth, state.heap.term_string(env.goal));
        let mut choices = state.prog.call(env.goal, &mut state.heap);
        if choices.is_empty() {
            if state.config.debug {
                println!("[{}]FAILED: {}", env.depth, state.heap.term_string(env.goal));
            }
            match retry(proof_stack, pointer, state) {
                Some(p) => pointer = p,
                None => return false,
            }
        } else {
            let choice = choices.pop().unwrap();
            env.choices = choices;
            apply_choice(proof_stack, pointer, choice, state);
            pointer += 1;
        }
    }
}

fn retry(
    proof_stack: &mut Vec<Env>,
    pointer: usize,
    state: &mut State
) -> Option<usize> {
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
    mut choice: Choice,
    state: &mut State
){
    let env = proof_stack.get_mut(pointer).unwrap();
    let goals = choice.choose(state);
    env.children = goals.len();

    if choice.new_clause {
        let new_clause:Clause = choice.build_clause(state); //Use binding to make new clause
        //Add new clause to program
        //If var symbol invent pred
        //Invented pred?
        let pred_symbol = new_clause.pred_symbol(&state.heap);
        if prog.add_h_clause(clause, heap) {
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
}

fn print_stack(proof_stack: &mut Vec<Env>, heap: &mut Heap) {
    for env in proof_stack {
        println!("[{}]: {}", env.depth, env.goal.to_string(heap));
    }
}
