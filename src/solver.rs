use crate::{
    // clause::*,
    choice::Choice,
    clause::ClauseType,
    term::Term,
    unification::*,
    Heap,
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

pub(crate) struct Proof<'a> {
    proof_stack: Vec<Env>,
    state: &'a mut State,
    goals: Box<[usize]>,
    pointer: usize,
}

impl<'a> Proof<'a> {
    pub fn new(goals: &[usize], state: &'a mut State) -> Proof<'a> {
        let goals: Box<[usize]> = goals.into();
        let proof_stack: Vec<Env> = goals.iter().map(|goal| Env::new(*goal, 0)).collect();

        Proof {
            proof_stack,
            state,
            goals,
            pointer: 0,
        }
    }
}

impl<'a> Iterator for Proof<'a> {
    type Item = Box<[Box<[Term]>]>;

    fn next(&mut self) -> Option<Self::Item> {
        //If not first attempt at proof backtrack to last choice point
        if self.pointer != 0 {
            match retry(&mut self.proof_stack, self.pointer - 1, &mut self.state) {
                Some(p) => {
                    self.pointer = p;
                }
                None => return None,
            }
        }

        if prove(&mut self.pointer, &mut self.proof_stack, &mut self.state) {
            println!("TRUE");

            //Add symbols to hypothesis variables
            self.state.prog.symbolise_hypothesis(&mut self.state.heap);

            //Print goals with query vairables substituted
            for goal in self.goals.iter() {
                println!("{},", self.state.heap.term_string(*goal))
            }

            //For every clause in hypothesis convert into an array non heap terms
            let h: Self::Item = self
                .state
                .prog
                .clauses
                .iter(&[ClauseType::HYPOTHESIS])
                .map(|i| {
                    self.state.prog.clauses[i]
                        .iter()
                        .map(|literal| self.state.heap.get_term_object(*literal))
                        .collect::<Box<[Term]>>()
                })
                .collect();

            Some(h)
        } else {
            println!("FALSE");
            None
        }
    }
}

/**Proof loop
 * By
 */
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
    let n_children = proof_stack[pointer].children;
    let children: Box<[Env]> = proof_stack
        .drain(pointer + 1..=pointer + n_children)
        .rev()
        .collect();
    let env = &mut proof_stack[pointer];

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

    for child in children.into_iter() {
        state.heap.deallocate_above(child.goal);
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
    let (goals, invented_pred) = choice.choose(state);
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
}
