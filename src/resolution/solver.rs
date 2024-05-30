use crate::{
    interface::{state::State, term::Term},
    program::{clause::{self, ClauseType}, program::CallRes},
};

use super::{choice::Choice, unification::Binding};

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
            bindings: Binding::new(),
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

    fn prove(&mut self) -> bool {
        loop {
            let (depth, goal) = match self.proof_stack.get_mut(self.pointer) {
                Some(e) => (e.depth, e.goal),
                None => {
                    return true;
                }
            };
            if depth == self.state.config.max_depth {
                if !self.retry() {
                    return false;
                }
            }
            if self.state.config.debug {
                println!("[{}]Try: {}", depth, self.state.heap.term_string(goal));
            }
            match self
                .state
                .prog
                .call(goal, &mut self.state.heap, &mut self.state.config)
            {
                CallRes::Function(function) => {
                    if function(goal, self.state) {
                        self.pointer += 1
                    } else {
                        if !self.retry() {
                            return false;
                        }
                    }
                }
                CallRes::Clauses(clauses) => {
                    let mut choices: Vec<Choice> = clauses
                        .filter_map(|ci| Choice::build_choice(goal, ci, self.state))
                        .collect();
                    if let Some(choice) = choices.pop() {
                        self.apply_choice(choice);
                        let env = self.proof_stack.get_mut(self.pointer).unwrap();
                        env.choices = choices;
                        self.pointer += 1;
                    } else {
                        if self.state.config.debug {
                            println!("[{}]FAILED: {}", depth, self.state.heap.term_string(goal));
                        }
                        if !self.retry() {
                            return false;
                        }
                    }
                }
            }
        }
    }

    fn retry(&mut self) -> bool {
        let n_children = self.proof_stack[self.pointer].children;
        let children: Box<[Env]> = self
            .proof_stack
            .drain(self.pointer + 1..=self.pointer + n_children)
            .rev()
            .collect();
        let env = &mut self.proof_stack[self.pointer];

        if self.state.config.debug {
            println!(
                "[{}]UNDO: {},{}",
                self.pointer,
                self.state.heap.term_string(env.goal),
                env.bindings.to_string(&self.state.heap)
            );
        }

        self.state.heap.unbind(&env.bindings);
        if env.new_clause == true {
            self.state.prog.remove_h_clause(env.invent_pred);
            env.new_clause = false;
        }

        for child in children.into_iter() {
            self.state.heap.deallocate_above(child.goal);
        }

        //is pointer a choice point
        if env.choices.is_empty() {
            if self.pointer == 0 {
                return false;
            } else {
                self.pointer -= 1;
                return self.retry();
            }
        } else {
            if self.state.config.debug {
                println!(
                    "[{}]RETRY: {}",
                    env.depth,
                    self.state.heap.term_string(env.goal)
                );
            }
            let choice = env.choices.pop().unwrap();
            self.apply_choice(choice);
            self.pointer += 1;
            return true;
        }
    }

    fn apply_choice(&mut self, mut choice: Choice) {
        let (goals, invented_pred) = choice.choose(self.state);
        let env = self.proof_stack.get_mut(self.pointer).unwrap();
        env.children = goals.len();
        env.bindings = choice.binding;
        env.new_clause = choice.clause.clause_type == ClauseType::HO;
        env.invent_pred = invented_pred;
        let depth = env.depth + 1;
        // state.heap.print_heap();

        let mut i = 1;
        for goal in goals {
            self.proof_stack
                .insert(self.pointer + i, Env::new(goal, depth));
            i += 1;
        }
    }
}

impl<'a> Iterator for Proof<'a> {
    type Item = Box<[Box<[Term]>]>;

    fn next(&mut self) -> Option<Self::Item> {
        //If not first attempt at proof backtrack to last choice point
        if self.pointer != 0 {
            self.pointer -= 1;
            if !self.retry() {
                return None;
            }
        }

        if self.prove() {
            println!("\nTRUE");

            //Add symbols to hypothesis variables
            self.state.prog.symbolise_hypothesis(&mut self.state.heap);

            //Print goals with query vairables substituted
            for goal in self.goals.iter() {
                println!("{},", self.state.heap.term_string(*goal))
            }

            println!("Hypothesis: ");
            for clause in self.state.prog.clauses.iter(&[ClauseType::HYPOTHESIS]){
                println!("\t{}", self.state.prog.clauses.get(clause).to_string(&self.state.heap))
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
                        .map(|literal| Term::build_from_heap(*literal, &self.state.heap))
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
