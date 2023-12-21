use std::collections::HashMap;

use crate::{
    atoms::Atom,
    program::{Choice, Program},
    terms::{Substitution, Term},
};
const MAX_HEAP_SIZE: usize = 1000;
struct Node {
    goal: Atom,
    substitution: Substitution,
    children: Vec<usize>,
}

impl Node {
    pub fn new(goal: Atom) -> Node {
        Node {
            goal,
            substitution: Substitution::new(),
            children: vec![],
        }
    }
}

fn goal_to_heap(goal: &mut Atom, heap: &mut Vec<Term>) {
    let ids = goal.eqvars_to_quvars(&(heap.len() - 1));
    for i in ids {
        heap.insert(i, Term::QUVar(i))
    }
}

struct Proof<'a> {
    heap: Vec<Term>,
    prog: &'a Program,
    node_id_counter: usize,
    nodes: HashMap<usize, Node>,
    choice_points: HashMap<usize, Vec<Choice>>,
}

impl<'a> Proof<'a> {
    pub fn new(mut goals: Vec<Atom>, prog: &Program) -> Proof {
        let mut heap: Vec<Term> = Vec::with_capacity(MAX_HEAP_SIZE);
        for goal in &mut goals {
            goal_to_heap(goal, &mut heap);
        }

        let mut node_id_counter = 1;
        let mut nodes: HashMap<usize, Node> = HashMap::new();
        nodes.insert(0, Node::new(Atom { terms: vec![] }));
        for goal in goals {
            nodes.insert(node_id_counter, Node::new(goal));
            nodes.get_mut(&0).unwrap().children.push(node_id_counter);
            node_id_counter += 1
        }
        Proof {
            heap,
            prog,
            node_id_counter,
            nodes,
            choice_points: HashMap::new(),
        }
    }

    //Proof Tree Operations
    //----------------------------------------------------------------------------------
    fn children(&self, n_id: usize) -> Vec<usize> {
        let mut res = vec![n_id];
        for child_id in self.nodes.get(&n_id).unwrap().children.iter() {
            res.append(&mut self.children(*child_id));
        }
        return res;
    }

    fn add_child_node(&mut self, n_id: usize, child_node: Node) {
        self.nodes
            .get_mut(&n_id)
            .unwrap()
            .children
            .push(self.node_id_counter);
        self.nodes.insert(self.node_id_counter, child_node);
        self.node_id_counter += 1;
    }

    fn delete_node(&mut self, n_id: usize) {
        for child in self.nodes.get(&n_id).unwrap().children.clone() {
            self.delete_node(child);
        }
        self.nodes.remove(&n_id);
        self.choice_points.remove(&n_id);
    }

    //----------------------------------------------------------------------------------

    pub fn start_proof(&mut self) {}

    fn simplify_heap_goal(&self, goal: &Atom) -> Atom {
        let mut g = goal.clone();
        for term in &mut g.terms {
            if let Term::QUVar(i) = term {
                let mut prev_i = *i;
                loop {
                    match &self.heap[prev_i] {
                        Term::QUVar(new_i) => {
                            if prev_i == *new_i {
                                *term = Term::QUVar(*new_i);
                            } else {
                                prev_i = *new_i;
                            }
                        }
                        v => {
                            *term = v.clone();
                            break;
                        }
                    }
                }
            }
        }
        return g;
    }

    fn prove(&mut self, n_id: usize, depth: u8) -> bool {
        let goal = self.simplify_heap_goal(&self.nodes[&n_id].goal);
        let mut choices = self.prog.match_head_to_goal(&goal, &mut self.heap, false);

        for _ in 0..choices.len() {
            let choice = choices.remove(0);
            if self.prove_choice(n_id, choice, depth) {
                self.choice_points.insert(n_id, choices);
                return true;
            }
        }
        return false;
    }

    fn prove_choice(&mut self, n_id: usize, mut choice: Choice, depth: u8) -> bool {
        choice.subs.filter();
        self.nodes.get_mut(&n_id).unwrap().substitution = choice.subs.clone();
        self.apply_sub(choice.subs);
        return false;
    }

    fn apply_sub(&mut self, subs: Substitution) {
        for (k, v) in subs.subs {
            if let Term::QUVar(i) = k {
                self.heap[i] = v;
            }
        }
    }
    fn undo_sub(&mut self, subs: Substitution) {
        for k in subs.subs.keys() {
            if let Term::QUVar(i) = k {
                self.heap[*i] = Term::QUVar(*i);
            }
        }
    }
}
