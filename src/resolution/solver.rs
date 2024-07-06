use std::sync::Arc;

use crate::{
    heap::{heap::Heap, store::Store, symbol_db::SymbolDB},
    interface::{
        config::Config,
        state::State,
        term::{Term, TermClause},
    },
    pred_module::PredReturn,
    program::{
        clause_table::ClauseTable, hypothesis::{self, Hypothesis}, program::{CallRes, DynamicProgram, ProgH}
    },
};

use super::proof_stack::{Env, ProofStack};

pub(crate) struct Proof<'a> {
    proof_stack: ProofStack,
    goals: Box<[usize]>,
    goal_vars: Box<[usize]>,
    pointer: usize,
    pub store: Store<'a>,
    pub prog: DynamicProgram<'a>,
    pub config: Config,
    pub state: State,
}

impl<'a> Proof<'a> {
    pub fn new(
        goals: &[usize],
        store: Store<'a>,
        hypothesis: ProgH<'a>,
        config: Option<Config>,
        state: &'a State,
    ) -> Proof<'a> {
        let config = match config {
            Some(config) => config,
            None => *state.config.read().unwrap(),
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
            store,
            prog: DynamicProgram::new(hypothesis, state.program.read().unwrap()),
            config,
            state: state.clone(),
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
                println!("[{}] TRY: {}", depth, self.store.term_string(goal));
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
                    if let Some(children) =
                        env.try_choices(&mut self.prog, &mut self.store, self.config)
                    {
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
                    "[{}] UNDO: {},{}",
                    self.pointer,
                    self.store.term_string(env.goal),
                    env.bindings.to_string(&self.store)
                );
            }

            self.store.unbind(&env.bindings);
            if env.new_clause == true {
                self.prog
                    .hypothesis
                    .remove_h_clause(env.invent_pred, self.config.debug);
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
                    println!(
                        "[{}] RETRY: {}",
                        env.depth,
                        self.store.term_string(env.goal)
                    );
                }
                if let Some(children) =
                    env.try_choices(&mut self.prog, &mut self.store, self.config)
                {
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

impl<'a> Iterator for Proof<'a> {
    type Item = ClauseTable;

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
            //Add symbols to hypothesis variables
            self.prog.hypothesis.normalise_hypothesis(&mut self.store);
            if self.config.debug {
                println!("TRUE");

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
            }

            //For every clause in hypothesis convert into an array non heap terms
            

            Some(self.prog.hypothesis.clauses.clone())
        } else {
            // println!("FALSE");
            None
        }
    }
}
