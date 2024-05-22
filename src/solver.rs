use crate::{
    // clause::*,
    choice::Choice, clause::{ClauseTraits, ClauseType}, unification::*, Heap, State, term::Term
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

pub(crate) struct Proof<'a> {
    proof_stack: Vec<Env>,
    state: &'a mut State,
    original_goals: Box<[Term]>,
    goals: Box<[usize]>,
    pointer: usize
}

impl<'a> Proof<'a> {
    pub fn new(goals: &[usize], state: &'a mut State) -> Proof<'a> {
        let goals: Box<[usize]> = goals.into();
        let original_goals: Box<[Term]> = goals
            .iter()
            .map(|goal_addr| state.heap.get_term_object(*goal_addr))
            .collect();
        let mut proof_stack:Vec<Env> = goals.iter().map(|goal| Env::new(*goal, 0)).collect();

        Proof {
            proof_stack,
            state,
            original_goals,
            goals,
            pointer: 0,
        }
    }
}

impl<'a> Iterator for Proof <'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {

        if self.pointer != 0 {
            match retry(&mut self.proof_stack, self.pointer-1, &mut self.state) {
                Some(p) => {
                    self.pointer = p;
                }
                None => return None,
            }
        }

        if prove(&mut self.pointer, &mut self.proof_stack, &mut self.state) {
            println!("TRUE");
            for goal in self.goals.iter() {
                println!("{},", self.state.heap.term_string(*goal))
            }
            let mut hypothesis = String::new();
            for (_,(_,h_clause)) in self.state.prog.clauses.iter(&[ClauseType::HYPOTHESIS]){
                hypothesis += "\n";
                self.state.heap.create_var_symbols(h_clause.vars(&self.state.heap));
                hypothesis += &h_clause.to_string(&self.state.heap);
            }
            Some(hypothesis)
        } else {
            println!("FALSE");
            print_stack(&mut self.proof_stack, &mut self.state.heap);
            None
            // heap.print_heap();
        }
    }
}

// pub fn start_proof(goals: Vec<usize>, state: &mut State) -> bool {
//     let mut proof_stack: Vec<Env> = vec![];

//     if prove(goals.clone(), &mut proof_stack, state) {
//         println!("TRUE");
//         for goal in goals {
//             println!("{},", state.heap.term_string(goal))
//         }
//         state.prog.write_h(&state.heap);
//         true
//     } else {
//         println!("FALSE");
//         print_stack(&mut proof_stack, &mut state.heap);
//         false
//         // heap.print_heap();
//     }
// }

fn prove(pointer: &mut usize, proof_stack: &mut Vec<Env>, state: &mut State) -> bool {
    loop {
        let (depth, goal) = match proof_stack.get_mut(*pointer) {
            Some(e) => (e.depth, e.goal),
            None => {
                return true;
            }
        };
        if depth == state.config.max_depth {
            match retry(proof_stack, *pointer, state) {
                Some(p) => {
                    *pointer = p;
                }
                None => return false,
            }
        }
        if state.config.debug {
            println!("[{}]Try: {}", depth, state.heap.term_string(goal));
        }
        let mut choices = state.prog.call(goal, &mut state.heap, &mut state.config);

        loop {
            if let Some(choice) = choices.pop() {
                if apply_choice(proof_stack, *pointer, choice, state) {
                    let env = proof_stack.get_mut(*pointer).unwrap();
                    env.choices = choices;
                    *pointer += 1;
                    break;
                }
            } else {
                if state.config.debug {
                    println!("[{}]FAILED: {}", depth, state.heap.term_string(goal));
                }
                match retry(proof_stack, *pointer, state) {
                    Some(p) => {
                        *pointer = p;
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
    if state.config.debug {
        println!(
            "[{pointer}]UNDO: {},{}",
            state.heap.term_string(env.goal),
            env.bindings.to_string(&state.heap)
        );
    }
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
        // state.heap.print_heap();

        let mut i = 1;
        for goal in goals {
            proof_stack.insert(pointer + i, Env::new(goal, depth));
            i += 1;
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
