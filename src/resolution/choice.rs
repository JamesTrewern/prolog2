use std::mem::ManuallyDrop;
use crate::{interface::state::State, program::clause::{Clause, ClauseType}};
use super::unification::{build_str, unify, Binding};

pub struct Choice {
    pub clause: Clause, // index in program clause bank
    pub binding: Binding, //Binding matching env goal to head of clause
}

impl Choice {
    /**Attempt to build choice point from goal and clause
     * @goal: heap address of goal literal
     * @clause: clause table index
     * @state: current state of program, including heap, prog, and config
     */
    pub fn build_choice(goal: usize, clause: usize, state: &mut State) -> Option<Choice> {
        //Get clause object from clause table
        let clause = state.prog.clauses.get(clause);

        //Can a binding be found by unifiy head of clause with goal
        if let Some(binding) = unify(clause[0], goal, &state.heap) {
            //Does this binding unify two variable predicate symbols in H?
            if !state.prog.check_constraints(&binding, &state.heap) {
                Some(Choice { clause, binding})
            } else {
                None
            }
        } else {
            None
        }
    }

    /**Use clause and binding to make new goals, and if higher order create new clause */
    pub fn choose(&mut self, state: &mut State) -> (Vec<usize>, bool) {
        let goals = self.build_goals(state);
        if state.config.debug {
            println!(
                "Matched with: {}",
                self.clause.to_string(&state.heap)
            );
            println!("Goals: {goals:?}");
        }
        //If clause is higher order build a new clause and add to program.
        //If variable predicate symbol in head of new clause, invented_pred is true
        let invented_pred = if self.clause.clause_type == ClauseType::META {
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
                    //If we invent a predicate add a binding from pred_symbol to invented pred
                    self.binding.push((pred_symbol, invented_pred));
                    true
                }
                None => false,
            }
        } else {
            false
        };

        //Apply binding to the heap, update effected ref cells
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

    /**Build goals using binding and clause by applying binding to clause body */
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
    
    /**Build new clause using binding and clause */
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
