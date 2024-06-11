use crate::{
    interface::{
        state::State,
        term::{Term, TermClause},
    },
    pred_module::PredReturn,
    program::{
        clause::{self, ClauseType},
        program::CallRes,
    },
};

use super::{choice::Choice, unification::Binding};

/**The enviroment stored for each goal.
 * When created each enviroment only needs a goal address and a depth
 * Once the proof stack pointer reaches the enviroment a the goal is called.
 * The rest of the envirmoment information is then created.
 * This allows back tracking to undo the effects of the enviroment
 */
struct Env {
    goal: usize, // Pointer to heap literal
    bindings: Binding,
    choices: Vec<Choice>, //Array of choices which have not been tried
    new_clause: bool,     //Was a new clause created by this enviroment
    invent_pred: bool,    //If there was a new clause was a ne predicate symbol invented
    children: usize,      //How many child goals were created
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
    goal_vars: Box<[usize]>,
    pointer: usize,
}

impl<'a> Proof<'a> {
    pub fn new(goals: &[usize], state: &'a mut State) -> Proof<'a> {
        let goals: Box<[usize]> = goals.into();
        let proof_stack: Vec<Env> = goals.iter().map(|goal| Env::new(*goal, 0)).collect();

        let mut goal_vars = Vec::<usize>::new();

        for goal in goals.iter() {
            goal_vars.append(
                &mut state.heap
                    .term_vars(*goal)
                    .iter()
                    .map(|(_, addr)|*addr)
                    .collect(),
            );
        }

        goal_vars.sort();
        goal_vars.dedup();

        Proof {
            proof_stack,
            state,
            goals,
            goal_vars: goal_vars.into(),
            pointer: 0,
        }
    }

    /**This is the proof loop.
     * It takes the enviroment at the current pointer on the proof stack
     * and dervies new goals, and possibly a new clause for the enviroment goal.
     * These new goals spawn new enviroments.
     * This loop continues until the pointer matches the length of the proof stack
     */
    fn prove(&mut self) -> bool {
        loop {
            let (depth, goal) = match self.proof_stack.get_mut(self.pointer) {
                Some(e) => (e.depth, e.goal),
                None => {
                    return true;
                }
            };
            if depth >= self.state.config.max_depth {
                // if depth >= self.state.config.max_depth + 2{
                //     return false;
                // }
                if !self.retry() {
                    return false;
                }else{
                    continue;
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
                CallRes::Function(function) => match function(goal, self.state) {
                    PredReturn::True => self.pointer += 1,
                    PredReturn::False => {
                        if !self.retry() {
                            return false;
                        }
                    }
                    PredReturn::Binding(binding) => {
                        self.state.heap.bind(&binding);
                        self.proof_stack[self.pointer].bindings = binding;
                        self.pointer += 1
                    }
                },
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

    /**Decrement the poitner and undo enviroment changes until finding a choice point */
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


        // for child in children.into_iter() {
        //     self.state.heap.deallocate_above(child.goal);
        // }

        //is enviroment a choice point
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
            //Use unchosen choice to retry goal
            let choice = env.choices.pop().unwrap();
            self.apply_choice(choice);
            self.pointer += 1;
            return true;
        }
    }

    /**Update enviroment fields with choice
     * Build new goals, and new clause  
     */
    fn apply_choice(&mut self, mut choice: Choice) {
        let (goals, invented_pred) = choice.choose(self.state);
        let env = self.proof_stack.get_mut(self.pointer).unwrap();
        env.children = goals.len();
        env.bindings = choice.binding;
        env.new_clause = choice.clause.clause_type == ClauseType::META;
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

    /** Idenftify loops in resolution and return to last choice point before looping pattern*/
    fn detect_loops(&mut self){
        todo!()
    }

}

impl<'a> Iterator for Proof<'a> {
    type Item = Box<[TermClause]>;

    /**Find the next possible proof tree, return None if there are no more possible proofs */
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

            for var in self.goal_vars.iter(){
                println!("{} = {}", self.state.heap.symbols.get_var(*var).unwrap(), self.state.heap.term_string(*var));
            }

            println!("Hypothesis: ");
            for clause in self.state.prog.clauses.iter([false,false,false,true]) {
                println!(
                    "\t{}",
                    self.state
                        .prog
                        .clauses
                        .get(clause)
                        .to_string(&self.state.heap)
                )
            }

            //For every clause in hypothesis convert into an array non heap terms
            let h: Self::Item = self
                .state
                .prog
                .clauses
                .iter([false,false,false,true])
                .map(|i| {
                    self.state.prog.clauses[i]
                        .iter()
                        .map(|literal| Term::build_from_heap(*literal, &self.state.heap))
                        .collect::<Vec<Term>>()
                })
                .map(|literals| TermClause { literals, meta: false })
                .collect();

            Some(h)
        } else {
            println!("FALSE");
            None
        }
    }
}
