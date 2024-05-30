use std::mem::ManuallyDrop;
use crate::{interface::state::State, program::clause::{Clause, ClauseType}};
use super::unification::{build_str, unify, Binding};

pub struct Choice {
    pub clause: Clause, // index in program clause bank
    pub binding: Binding,
}

impl Choice {
    pub fn build_choice(goal: usize, clause: usize, state: &mut State) -> Option<Choice> {
        let clause = state.prog.clauses.get(clause);
        if let Some(binding) = unify(clause[0], goal, &state.heap) {
            if !state.prog.check_constraints(&binding, &state.heap) {
                Some(Choice { clause, binding})
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn choose(&mut self, state: &mut State) -> (Vec<usize>, bool) {
        // self.binding.undangle_const(&mut state.heap);
        let goals = self.build_goals(state);
        if state.config.debug {
            println!(
                "Matched with: {}",
                self.clause.to_string(&state.heap)
            );
            println!("Goals: {goals:?}");
        }
        let invented_pred = if self.clause.clause_type == ClauseType::HO {
            let new_clause: Clause = self.build_clause(state); //Use binding to make new clause
            if state.config.debug {
                println!(
                    "New Clause: {}, {:?}, H size: {}",
                    new_clause.to_string(&state.heap),
                    &new_clause[..],
                    state.prog.h_size
                );
            }
            let (pred_symbol, _) = new_clause.symbol_arity(&state.heap);
            match state.prog.add_h_clause(new_clause, &mut state.heap) {
                Some(invented_pred) => {
                    self.binding.push((pred_symbol, invented_pred));
                    true
                }
                None => false,
            }
        } else {
            false
        };

        state.heap.bind(&self.binding);
        if state.config.debug {
            println!(
                "Bindings: {}, {:?}",
                self.binding.to_string(&state.heap),
                self.binding
            );
        }

        (goals, invented_pred)
    }

    fn build_goals(&mut self, state: &mut State) -> Vec<usize> {
        let mut goals: Vec<usize> = vec![];
        for body_literal in &self.clause[1..] {
            goals.push(
                match build_str(&mut self.binding, *body_literal, &mut state.heap, &mut None) {
                    (new_goal, false) => new_goal,
                    _ => *body_literal,
                },
            );
        }
        goals
    }
    fn build_clause(&mut self, state: &mut State) -> Clause {
        let mut uqvar_binding: Option<Binding> = Some(Binding::new());
        let mut new_literals: Box<[usize]> = vec![0; self.clause.len()].into_boxed_slice();
        for i in 0..self.clause.len() {
            new_literals[i] = match build_str(
                &mut self.binding,
                self.clause[i],
                &mut state.heap,
                &mut uqvar_binding,
            ) {
                (new_heap_i, false) => new_heap_i,
                _ => self.clause[i],
            }
        }

        Clause {
            clause_type: ClauseType::HYPOTHESIS,
            literals: ManuallyDrop::new(new_literals),
        }
    }
}
