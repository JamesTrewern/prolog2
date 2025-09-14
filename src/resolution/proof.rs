use std::sync::Arc;

use crate::{
    heap::{heap::Heap, query_heap::QueryHeap, symbol_db::SymbolDB},
    predicate_modules::{PredReturn, PredicateFunction},
    program::{
        clause::Clause,
        hypothesis::Hypothesis,
        predicate_table::{self, Predicate, PredicateTable},
    },
    resolution::{
        build::{build, re_build_bound_arg_terms},
        unification::unify,
    },
    Config,
};

pub type Binding = (usize, usize);

pub(super) struct Env {
    pub(super) goal: usize, // Pointer to heap literal
    pub(super) bindings: Box<[Binding]>,
    pub(super) choices: Vec<Clause>, //Array of choices which have not been tried
    pred_function: Option<PredicateFunction>,
    got_choices: bool,
    pub(super) new_clause: bool, //Was a new clause created by this enviroment
    pub(super) invent_pred: bool, //If there was a new clause was a new predicate symbol invented
    pub(super) children: usize,  //How many child goals were created
    pub(super) depth: usize,
}

impl Env {
    pub fn new(goal: usize, depth: usize) -> Self {
        Env {
            goal,
            bindings: Box::new([]),
            choices: Vec::new(),
            pred_function: None,
            got_choices: false,
            new_clause: false,
            invent_pred: false,
            children: 0,
            depth,
        }
    }

    pub fn get_choices(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        predicate_table: &PredicateTable,
    ) {
        if !self.got_choices {
            self.got_choices = true;
            let (symbol, arity) = heap.str_symbol_arity(self.goal);
            //TODO recognise when predicate is in hypothesis
            if symbol == 0 {
                self.choices = predicate_table.get_body_clauses(arity);
                if let Some(clauses) = predicate_table.get_variable_predicates(arity){
                    self.choices.extend(clauses);
                }
                self.choices
                    .append(&mut hypothesis.get_predicate((symbol, arity)));
            } else {
                match predicate_table.get_predicate((symbol, arity)) {
                    Some(Predicate::Clauses(clauses)) => {
                        self.choices = hypothesis.get_predicate((symbol, arity));
                        self.choices.extend_from_slice(&clauses);
                    }
                    Some(Predicate::Function(pred_function)) => {
                        self.pred_function = Some(pred_function)
                    }
                    None => {
                        self.choices = hypothesis.get_predicate((symbol, arity));
                        if let Some(clauses) = predicate_table.get_variable_predicates(arity){
                            self.choices.extend(clauses);
                        }
                    }
                }
            };
        }
    }

    pub fn undo_try(&mut self, hypothesis: &mut Hypothesis, heap: &mut QueryHeap, h_clauses: &mut usize, invented_preds: &mut usize) -> usize {
        if self.new_clause {
            hypothesis.drop_clause();
            *h_clauses -= 1;
            self.new_clause = false;
            if self.invent_pred{
                *invented_preds -= 1;
                self.invent_pred = false;
            }
        }
        heap.unbind(&self.bindings);
        self.children
    }

    pub fn try_choices(
        &mut self,
        heap: &mut QueryHeap,
        hypothesis: &mut Hypothesis,
        allow_new_clause: bool,
        allow_new_pred: bool,
        config: Config,
    ) -> Option<Vec<Env>> {
        if self.depth > config.max_depth{
            return None;
        }
        // println!("Call[{}|{}]: {}", self.depth, self.choices.len(), heap.term_string(self.goal));
        if let Some(pred_function) = self.pred_function {
            match pred_function(heap, hypothesis, self.goal) {
                PredReturn::True => return Some(Vec::new()),
                PredReturn::False => return None,
                PredReturn::Binding(bindings) => {
                    self.bindings = bindings.into_boxed_slice();
                    heap.bind(&self.bindings);
                }
            }
        }
        while let Some(clause) = self.choices.pop() {
            // println!("Try[{}]: {}", self.depth, clause.to_string(heap));

            let head = clause.head();

            if clause.meta() {
                if !allow_new_clause {
                    continue;
                } else if !allow_new_pred && heap.str_symbol_arity(head).0 == 0 {
                    continue;
                }
            }

            if let Some(mut substitution) = unify(heap, head, self.goal) {
                //If a ref is bound to a complex term containing args then it must be rebuilt in the query heap
                re_build_bound_arg_terms(heap, &mut substitution);
                //Create new goals
                let new_goals: Vec<usize> = clause
                    .body()
                    .iter()
                    .map(|&body_literal| build(heap, &mut substitution, None, body_literal))
                    .collect();

                // println!("{new_goals:?}");
                //If meta clause we must create a new clause with the substitution
                if clause.meta() {
                    self.new_clause = true;
                    //If both the goal and clause are variable predicates we invent a predicate
                    if heap.str_symbol_arity(head).0 == 0 && heap.str_symbol_arity(self.goal).0 == 0
                    {
                        self.invent_pred = true;
                        let pred_symbol = SymbolDB::set_const(format!("pred_{}", hypothesis.len()));
                        let pred_addr = heap.set_const(pred_symbol);
                        //If the head is a variable predicate this will always be Arg0
                        substitution.set_arg(0, pred_addr);
                    }
                    let new_clause_literals: Vec<usize> = clause
                        .iter()
                        .map(|literal| build(heap, &mut substitution, clause.meta_vars, *literal))
                        .collect();
                    hypothesis.push_clause(Clause::new(new_clause_literals, None), heap);
                }
                self.bindings = substitution.get_bindings();
                heap.bind(&self.bindings);
                //Convert goals to new enviroments and return
                return Some(
                    new_goals
                        .into_iter()
                        .map(|goal| Env::new(goal, self.depth + 1))
                        .collect(),
                );
            }
        }
        None
    }
}

pub struct Proof<'a> {
    stack: Vec<Env>,
    pointer: usize,
    goal_count: u8, //How many goals were in initial query
    pub hypothesis: Hypothesis,
    pub heap: QueryHeap<'a>,
    h_clauses: usize,
    invented_preds: usize,
}

impl<'a> Proof<'a> {
    pub fn new(heap: QueryHeap<'a>, goals: &[usize], config: Config) -> Self {
        let goal_count = goals.len() as u8;
        let hypothesis = Hypothesis::new();
        let stack = goals.iter().map(|goal| Env::new(*goal, 0)).collect();
        Proof {
            stack,
            pointer: 0,
            hypothesis,
            heap,
            goal_count,
            h_clauses: 0,
            invented_preds: 0,
        }
    }

    pub fn prove(&mut self, predicate_table: Arc<PredicateTable>, config: Config) -> bool {
        //A previous proof has already been found, back track to find a new one.
        if self.pointer == self.stack.len() {
            self.pointer -= 1;
            self.stack[self.pointer].undo_try(&mut self.hypothesis, &mut self.heap, &mut self.h_clauses, &mut self.invented_preds);
        }

        //Once the pointer exceeds the last enviroment all goals have been proven
        while self.pointer < self.stack.len() {
            //If this enviroment is new, choices will be aquired, otherwise nothing happens
            self.stack[self.pointer].get_choices(
                &mut self.heap,
                &mut self.hypothesis,
                &predicate_table,
            );

            match self.stack[self.pointer].try_choices(
                &mut self.heap,
                &mut self.hypothesis,
                self.h_clauses < config.max_clause,
                self.invented_preds < config.max_pred,
                config,
            ) {
                Some(new_goals) => {
                    if self.stack[self.pointer].new_clause {
                        self.h_clauses += 1;
                    }
                    if self.stack[self.pointer].invent_pred {
                        self.invented_preds += 1;
                    }
                    self.pointer += 1;
                    for new_goal in new_goals {
                        self.stack.insert(self.pointer, new_goal);
                    }
                }
                //If this goal fails the proof stack is backtracked
                None => {
                    //If the first goal fails this proof has failed
                    if self.pointer == 0 {
                        return false;
                    }
                    self.pointer -= 1;
                    //Undo bindings and creation of clauses
                    let children =
                        self.stack[self.pointer].undo_try(&mut self.hypothesis, &mut self.heap, &mut self.h_clauses, &mut self.invented_preds);
                    //Remove child goals from proof stack
                    self.stack
                        .drain((self.pointer + 1)..(self.pointer + 1 + children));
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {}
