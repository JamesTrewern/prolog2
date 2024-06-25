use crate::{
    heap::{store::Store, symbol_db::SymbolDB},
    interface::{
        config::Config,
        term::{Term, TermClause},
    },
    pred_module::PredReturn,
    program::program::{CallRes, DynamicProgram},
};

use super::proof_stack::{Env, ProofStack};

pub(crate) struct Proof {
    proof_stack: ProofStack,
    goals: Box<[usize]>,
    goal_vars: Box<[usize]>,
    pointer: usize,
    pub store: Store,
    pub prog: DynamicProgram,
    pub config: Config,
}

impl Proof {
    pub fn new(
        goals: &[usize],
        store: Store,
        prog: DynamicProgram,
        config: Option<Config>,
    ) -> Proof {
        let config = match config {
            Some(config) => config,
            None => Config::get_config(),
        };

        let mut goal_vars = Vec::<usize>::new();
        for goal in goals.iter() {
            goal_vars.append(
                &mut store
                    .term_vars(*goal)
                    .iter()
                    .map(|(_, addr)| *addr)
                    .collect(),
            );
        }
        goal_vars.sort();
        goal_vars.dedup();

        Proof {
            proof_stack: ProofStack::new(goals),
            goals: goals.into(),
            goal_vars: goal_vars.into(),
            pointer: 0,
            store: store,
            prog,
            config,
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
            if depth >= self.config.max_depth {
                if !self.retry() {
                    return false;
                } else {
                    continue;
                }
            }
            if self.config.debug {
                println!("[{}]Try: {}", depth, self.store.term_string(goal));
            }
            match self.prog.call(goal, &mut self.store, self.config) {
                CallRes::Function(function) => match function(goal, self) {
                    PredReturn::True => self.pointer += 1,
                    PredReturn::False => {
                        if !self.retry() {
                            return false;
                        }
                    }
                    PredReturn::Binding(binding) => {
                        self.store.bind(&binding);
                        self.proof_stack[self.pointer].bindings = binding;
                        self.pointer += 1
                    }
                },
                CallRes::Clauses(clauses) => {
                    let env = &mut self.proof_stack[self.pointer];
                    env.choices = Some(clauses);
                    if let Some(children) = env.try_choices(&mut self.prog, &mut self.store, self.config) {
                        self.proof_stack.insert(children, self.pointer);
                        self.pointer += 1;
                    } else {
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
        loop {
            let n_children = self.proof_stack[self.pointer].children;
            let _children: Box<[Env]> = self
                .proof_stack
                .drain(self.pointer + 1..=self.pointer + n_children)
                .rev()
                .collect();
            let env = &mut self.proof_stack[self.pointer];

            if self.config.debug {
                println!(
                    "[{}]UNDO: {},{}",
                    self.pointer,
                    self.store.term_string(env.goal),
                    env.bindings.to_string(&self.store)
                );
            }

            self.store.unbind(&env.bindings);
            if env.new_clause == true {
                self.prog.hypothesis.remove_h_clause(env.invent_pred);
                env.new_clause = false;
                env.invent_pred = false;
            }

            //is enviroment a choice point
            if env.choices.is_none() {
                if self.pointer == 0 {
                    return false;
                } else {
                    self.pointer -= 1;
                    continue;
                }
            } else {
                if self.config.debug {
                    println!("[{}]RETRY: {}", env.depth, self.store.term_string(env.goal));
                }
                if let Some(children) = env.try_choices(&mut self.prog, &mut self.store, self.config) {
                    self.proof_stack.insert(children, self.pointer);
                    self.pointer += 1;
                    return true;
                } else {
                    if self.pointer == 0 {
                        return false;
                    }
                    self.pointer -= 1;
                }
            }
        }
    }

    #[allow(dead_code)]
    /** Idenftify loops in resolution and return to last choice point before looping pattern*/
    fn detect_loops(&mut self) {
        todo!()
    }
}

impl Iterator for Proof {
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
            self.prog.hypothesis.symbolise_hypothesis(&mut self.store);

            //Print goals with query vairables substituted
            for goal in self.goals.iter() {
                println!("{},", self.store.term_string(*goal))
            }

            for var in self.goal_vars.iter() {
                println!(
                    "{} = {}",
                    SymbolDB::get_var(*var).unwrap(),
                    self.store.term_string(*var)
                );
            }

            println!("Hypothesis: ");
            for clause in self.prog.hypothesis.iter() {
                println!("\t{}", clause.to_string(&self.store))
            }

            //For every clause in hypothesis convert into an array non heap terms
            let h: Self::Item = self
                .prog
                .hypothesis
                .iter()
                .map(|clause| {
                    clause
                        .iter()
                        .map(|literal| Term::build_from_heap(*literal, &self.store))
                        .collect::<Vec<Term>>()
                })
                .map(|literals| TermClause {
                    literals,
                    meta: false,
                })
                .collect();

            Some(h)
        } else {
            println!("FALSE");
            None
        }
    }
}
