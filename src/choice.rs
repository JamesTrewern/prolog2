use crate::{clause::*,unification::*};
use crate::{Heap, State};


#[derive(Debug)]
pub struct Choice {
    pub clause: usize, // index in program clause bank
    pub binding: Binding,
    pub new_clause: bool,
}

impl Choice {
    pub fn choose(&mut self, state: &mut State) -> Option<(Vec<usize>, bool)> {
        // self.binding.undangle_const(&mut state.heap);
        if self.clause == Heap::CON_PTR{
            return Some((vec![],false));
        }
        let goals = self.build_goals(state);
        if state.config.debug{
            println!("Matched with: {}", state.prog.clauses.get(self.clause).1.to_string(&state.heap));
            println!("Goals: {goals:?}");
        }
        let invented_pred = if self.new_clause {
            let new_clause: Box<Clause> = self.build_clause(state); //Use binding to make new clause
            if state.config.debug{
                println!("New Clause: {}, {new_clause:?}, H size: {}", new_clause.to_string(&state.heap), state.prog.h_size);
            }
            let (pred_symbol,_) = new_clause.symbol_arity(&state.heap);
            match state
                .prog
                .add_h_clause(new_clause, &mut state.heap, &state.config)
            {
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
        if state.config.debug{
            println!("Bindings: {}, {:?}", self.binding.to_string(&state.heap), self.binding);
        }

        Some((goals,invented_pred))
        
    }
    pub fn build_goals(&mut self, state: &mut State) -> Vec<usize> {
        let mut goals: Vec<usize> = vec![];
        for body_literal in &state.prog.clauses.get(self.clause).1[1..] {
            goals.push(
                match build_str(&mut self.binding, *body_literal, &mut state.heap, &mut None) {
                    (new_goal, false) => new_goal,
                    _ => *body_literal,
                },
            );
        }
        goals
    }
    pub fn build_clause(&mut self, state: &mut State) -> Box<Clause> {
        let mut uqvar_binding: Option<Binding> = Some(vec![]);
        // let new_clause:Box<[usize]> = Box::new_uninit_slice(src_clause.len());
        // let mut new_clause: Vec<usize> = Vec::with_capacity(self.clause.len());

        let src_clause = state.prog.clauses.get(self.clause).1;
        let mut new_clause: Box<Clause> = vec![0; src_clause.len()].into_boxed_slice();
        for i in 0..src_clause.len() {
            new_clause[i] = match build_str(&mut self.binding, src_clause[i],&mut state.heap, &mut uqvar_binding) {
                (new_heap_i, false) => new_heap_i,
                _ => src_clause[i],
            }
        }

        new_clause.into()
    }
}