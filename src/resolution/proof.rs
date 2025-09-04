use crate::{
    heap::{heap::Heap, query_heap::QueryHeap, symbol_db::SymbolDB},
    program::{
        clause::Clause,
        hypothesis::Hypothesis,
        predicate_function::PredicateFunction,
        predicate_table::{Predicate, PredicateTable},
    },
    resolution::{
        build::{build, re_build_bound_arg_terms},
        unification::unify,
    },
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
                    None => self.choices = hypothesis.get_predicate((symbol, arity)),
                }
            };
        }
    }

    pub fn undo_try(&mut self, hypothesis: &mut Hypothesis, heap: &mut QueryHeap) -> usize {
        if self.new_clause {
            hypothesis.drop_clause();
            self.new_clause = false;
            self.invent_pred = false;
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
    ) -> Option<Vec<Env>> {
        if let Some(pred_function) = self.pred_function {
            match pred_function(heap, hypothesis, self.goal) {
                crate::program::predicate_function::PredReturn::True => return Some(Vec::new()),
                crate::program::predicate_function::PredReturn::False => return None,
                crate::program::predicate_function::PredReturn::Binding(bindings) => {
                    self.bindings = bindings.into_boxed_slice();
                    heap.bind(&self.bindings);
                }
            }
        }
        while let Some(clause) = self.choices.pop() {
            if !allow_new_clause && clause.meta() {
                break;
            }
            let head = clause.head();
            if !allow_new_pred && heap.str_symbol_arity(head).0 == 0 {
                break;
            }

            if let Some(mut substitution) = unify(heap, self.goal, head) {
                //If a ref is bound to a complex term containing args then it must be rebuilt in the query heap
                re_build_bound_arg_terms(heap, &mut substitution);
                //Create new goals
                let new_goals: Vec<usize> = clause
                    .body()
                    .iter()
                    .map(|&body_literal| build(heap, &mut substitution, None, body_literal))
                    .collect();
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
    predicate_table: &'a mut PredicateTable,
    goal_count: u8, //How many goals were in initial query
    pub hypothesis: Hypothesis,
    pub heap: QueryHeap<'a>,
}

impl<'a> Proof<'a> {
    pub fn new(heap: QueryHeap<'a>, goals: &[usize], predicate_table: &'a mut PredicateTable) -> Self {
        let goal_count = goals.len() as u8;
        let hypothesis = Hypothesis::new();
        let stack = goals.iter().map(|goal| Env::new(*goal, 0)).collect();
        Proof {
            stack,
            pointer: 0,
            predicate_table,
            hypothesis,
            heap,
            goal_count,
        }
    }

    pub fn prove(&mut self) -> bool {
        //A previous proof has already been found, back track to find a new one.
        if self.pointer == self.stack.len() {
            self.pointer -= 1;
            self.stack[self.pointer].undo_try(&mut self.hypothesis, &mut self.heap);
        }

        //Once the pointer exceeds the last enviroment all goals have been proven
        while self.pointer < self.stack.len() {
            //If this enviroment is new, choices will be aquired, otherwise nothing happens
            self.stack[self.pointer].get_choices(
                &mut self.heap,
                &mut self.hypothesis,
                &self.predicate_table,
            );

            match self.stack[self.pointer].try_choices(
                &mut self.heap,
                &mut self.hypothesis,
                true,
                true,
            ) {
                Some(new_goals) => {
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
                        self.stack[self.pointer].undo_try(&mut self.hypothesis, &mut self.heap);
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
mod tests {
}
