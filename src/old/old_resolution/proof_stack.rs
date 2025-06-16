use std::{
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
    usize,
};

use crate::{
    heap::{heap::Heap, store::Store},
    interface::config::Config,
    program::{
        clause::{Clause, ClauseType},
        dynamic_program::DynamicProgram,
        program::ProgramIterator,
    },
};

use super::{
    build::{build_clause, build_goals},
    call::match_head,
    unification::Binding,
};

/**The enviroment stored for each goal.
 * When created each enviroment only needs a goal address and a depth
 * Once the proof stack pointer reaches the enviroment a the goal is called.
 * The rest of the envirmoment information is then created.
 * This allows back tracking to undo the effects of the enviroment
 */
pub(super) struct Env {
    pub(super) goal: usize, // Pointer to heap literal
    pub(super) bindings: Binding,
    pub(super) choices: Option<ProgramIterator>, //Array of choices which have not been tried
    pub(super) new_clause: bool,                 //Was a new clause created by this enviroment
    pub(super) invent_pred: bool, //If there was a new clause was a ne predicate symbol invented
    pub(super) children: usize,   //How many child goals were created
    pub(super) depth: usize,
}

impl Env {
    pub fn new(goal: usize, depth: usize) -> Env {
        Env {
            goal,
            bindings: Binding::new(),
            choices: None,
            new_clause: false,
            children: 0,
            invent_pred: false,
            depth,
        }
    }

    pub fn try_choices(
        &mut self,
        prog: &mut DynamicProgram,
        store: &mut Store,
        config: Config,
    ) -> Option<Vec<Env>> {
        //Loop through unchosen choice to retry goal
        if let Some(choices) = &mut self.choices {
            loop {
                if let Some(clause) = choices.next().map(|i| prog.get(i)) {
                    if config.max_depth == self.depth && clause.len() > 1{
                        continue;
                    }
                    let mut arg_regs = [usize::MAX;64];
                    // println!("[{}] Match {}", self.depth, clause.to_string(store));
                    if let Some(mut binding) = match_head(clause[0], self.goal, store,&mut arg_regs) {
                        if config.debug {
                            println!("[{}] Call {}", self.depth, clause.to_string(store));
                        }

                        if prog.check_constraints(&binding, store) {
                            continue;
                        }
                        let goals = build_goals(&clause[1..], store,&mut arg_regs);
                        if clause.clause_type == ClauseType::META {
                            if config.debug {
                                println!("Add Clause: {}", clause.to_string(store));
                            }
                            let literals = ManuallyDrop::new(build_clause(&clause, store,&mut arg_regs));
                            let clause = Clause {
                                literals,
                                clause_type: ClauseType::HYPOTHESIS,
                            };
                            if let Some(invented_pred) = prog.add_h_clause(clause, store)
                            {
                                let (var_pred, _) = store.str_symbol_arity(self.goal);
                                binding.push((var_pred, invented_pred));
                                self.invent_pred = true;
                            }
                            self.new_clause = true;
                        }
                        let child_envs: Vec<Env> = goals
                            .into_iter()
                            .rev()
                            .map(|goal| Env::new(*goal, self.depth + 1))
                            .collect();
                        store.bind(&binding);
                        self.bindings = binding;
                        self.children = child_envs.len();
                        return Some(child_envs);
                    }
                } else {
                    self.choices = None;
                    return None;
                }
            }
        } else {
            None
        }
    }
}

pub(super) struct ProofStack(Vec<Env>);

impl ProofStack {
    pub fn new(goals: &[usize]) -> ProofStack {
        ProofStack(goals.iter().map(|goal| Env::new(*goal, 0)).collect())
    }

    pub fn insert(&mut self, envs: Vec<Env>, index: usize) {
        for env in envs {
            self.0.insert(index + 1, env)
        }
    }
}

impl Deref for ProofStack {
    type Target = Vec<Env>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ProofStack {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
