use crate::{
    atoms::Atom,
    clause::Clause,
    program::{Choice, Program},
    terms::{Substitution, Term},
};
use std::{
    clone,
    collections::{HashMap, HashSet},
};

pub const ROOT_ID: u32 = 0;
const MAX_CLAUSE: usize = 2;

//TO DO
//  Rather than return option subs return bool. and gather subs and apply using the children method
//  Store revert and retry changes in a more effecient manner
// Consider Var table to prevent having multiple copies of large terms

struct Node {
    original_goal: Atom,
    goal: Atom,
    substitution: Substitution,
    children: Vec<u32>,
}

impl Node {
    pub fn new(goal: Atom) -> Node {
        Node {
            original_goal: goal.clone(),
            goal,
            substitution: Substitution::new(),
            children: vec![],
        }
    }

    pub fn apply_sub(&mut self, subs: &Substitution) {
        self.goal = self.goal.apply_subs(&subs);
    }

    pub fn reset_goal(&mut self) {
        self.goal = self.original_goal.clone();
        self.children.clear();
    }
}

pub struct Proof<'a> {
    top_goal: Atom,
    nodes: HashMap<u32, Node>,
    choice_points: HashMap<u32, Vec<Choice>>,
    hypothesis: Hypothesis,
    node_id_counter: u32,
    var_id_counter: u32,
    prog: &'a Program,
}

impl<'a> Proof<'a> {
    fn tree_to_vec_depth(&self, n_id: &u32) -> Vec<Vec<u32>> {
        let res = vec![vec![*n_id]];
        let child_res: Vec<Vec<Vec<u32>>> = self
            .nodes
            .get(n_id)
            .unwrap()
            .children
            .iter()
            .map(|c_id| self.tree_to_vec_depth(c_id))
            .collect();
        return res;
    }

    pub fn new(goal: Atom, prog: &Program) -> Proof {
        let mut var_id_counter: u32 = 0;
        let mut root_goal = goal.clone();
        root_goal.eqvars_to_quvars(&mut var_id_counter);
        let mut root = Node::new(root_goal);
        let mut nodes: HashMap<u32, Node> = HashMap::new();
        nodes.insert(ROOT_ID, root);
        return Proof {
            top_goal: goal,
            nodes,
            choice_points: HashMap::new(),
            hypothesis: Hypothesis::new(prog.constraints.clone()),
            node_id_counter: ROOT_ID + 1,
            var_id_counter,
            prog,
        };
    }

    fn children(&self, n_id: u32) -> Vec<u32> {
        let mut res = vec![n_id];
        for child_id in self.nodes.get(&n_id).unwrap().children.iter() {
            res.append(&mut self.children(*child_id));
        }
        return res;
    }

    fn add_child_node(&mut self, n_id: u32, child_node: Node) {
        self.nodes
            .get_mut(&n_id)
            .unwrap()
            .children
            .push(self.node_id_counter);
        self.nodes.insert(self.node_id_counter, child_node);
        self.node_id_counter += 1;
    }

    fn delete_node(&mut self, n_id: u32) {
        for child in self.nodes.get(&n_id).unwrap().children.clone() {
            self.delete_node(child);
        }
        self.nodes.remove(&n_id);
        self.choice_points.remove(&n_id);
    }

    pub fn apply_sub(&mut self, n_id: u32, subs: &Substitution) {
        self.nodes.get_mut(&n_id).unwrap().apply_sub(subs);
        for child_id in self.nodes.get(&n_id).unwrap().children.clone() {
            self.apply_sub(child_id, subs)
        }
        self.hypothesis.apply_sub(n_id, subs);
    }

    pub fn reset_goal(&mut self, n_id: &u32) {
        for child_id in &self.nodes.get(&n_id).unwrap().children.clone() {
            self.delete_node(*child_id);
        }
        self.nodes.get_mut(n_id).unwrap().reset_goal();
        self.hypothesis.undo_sub(n_id);
    }

    pub fn start_proof(&mut self) {
        match self.prove(ROOT_ID, 0) {
            Some(_) => {
                let sub = self
                    .top_goal
                    .unify(&self.nodes.get(&ROOT_ID).unwrap().goal)
                    .unwrap();
                //println!("{}", sub.to_string());
                //self.hypothesis.current.write_prog()
            }
            None => {println!("{:?}",self.choice_points);println!("False");},
        };
    }

    fn prove_choice(&mut self, n_id: u32, choice: Choice, depth: u32) -> Option<Substitution> {
        let mut node = self.nodes.get_mut(&n_id).unwrap();
        match choice.new_clause {
            Some(h_clause) => {
                if self.hypothesis.current.clauses.len() == MAX_CLAUSE {
                    return None;
                }
                self.hypothesis.add_clause(h_clause, &n_id)
            }
            _ => (),
        }
        node.apply_sub(&choice.subs);
        node.substitution = choice.subs.clone();
        for goal in choice.goals {
            self.add_child_node(n_id, Node::new(goal));
        }
        let mut proven = true;
        let mut cumulative_subs = choice.subs.clone();
        for goal_id in self.nodes.get(&n_id).unwrap().children.clone() {
            match self.prove(goal_id, depth + 1) {
                Some(subs) => {
                    self.apply_sub(n_id, &subs);
                    self.hypothesis.apply_sub(n_id, &subs);
                    cumulative_subs += subs;
                }
                None => {
                    proven = false;
                    break;
                }
            };
        }
        if proven == false {
            //Is there a choice point in children
            let mut children = self.children(n_id);
            while let Some(child_id) = children.pop() {
                let path = self.path(&n_id, &child_id).unwrap();
                if self.choice_points.contains_key(&child_id) {
                    for choice_point in self.choice_points.remove(&child_id).unwrap() {
                        match self.retry(path.clone(), choice_point) {
                            Some(mut subs) => {
                                self.apply_sub(n_id, &subs);
                                subs += choice.subs.clone();
                                return Some(subs);
                            }
                            None => (),
                        }
                    }
                }
            }
            return None;
        } else {
            return Some(cumulative_subs);
        }
    }

    pub fn prove(&mut self, n_id: u32, depth: u32) -> Option<Substitution> {
        if depth == 4 {
            return None;
        }
        let goal = &self.nodes.get(&n_id).unwrap().goal;
        println!("[{}]: Goal: {}", depth, goal.to_string());
        let mut choices =
            self.hypothesis
                .current
                .match_head_to_goal(&goal, &mut self.var_id_counter, true);
        choices.append(
            &mut self
                .prog
                .match_head_to_goal(&goal, &mut self.var_id_counter, false),
        );

        for _ in 0..choices.len() {
            let choice = choices.remove(0);
            match self.prove_choice(n_id, choice, depth) {
                Some(subs) => {
                    self.choice_points.insert(n_id, choices);
                    return Some(subs);
                }
                None => {
                    self.reset_goal(&n_id);
                }
            };
        }
        return None;
    }

    fn path(&self, n1_id: &u32, n2_id: &u32) -> Option<Vec<u32>> {
        if *n1_id == *n2_id {
            return Some(vec![*n1_id]);
        }
        for child_id in self.nodes.get(n1_id).unwrap().children.iter() {
            match self.path(child_id, n2_id) {
                Some(mut sub_path) => {
                    sub_path.push(*n1_id);
                    return Some(sub_path);
                }
                None => (),
            }
        }
        return None;
    }

    fn retry(&mut self, mut path: Vec<u32>, choice: Choice) -> Option<Substitution> {
        let n_id = path.pop().unwrap();
        if path.len() == 0 {
            return self.prove_choice(n_id, choice, 0);
        }
        let children = self.nodes.get(&n_id).unwrap().children.clone();
        let i = children
            .iter()
            .position(|c_id| c_id == path.last().unwrap())
            .unwrap();
        for child_id in &children[i..] {
            self.reset_goal(child_id);
        }
        self.apply_sub(n_id, &self.collect_subs(&n_id)); //gather subs from nodes left of path and apply to the reset goals
        match self.retry(path, choice) {
            Some(mut subs) => {
                self.apply_sub(n_id, &subs);
                for child_id in &children[i..] {
                    subs += match self.prove(*child_id, 0) {
                        Some(v) => v,
                        None => return None,
                    };
                }
                Some(subs)
            }
            None => None,
        }
    }

    fn collect_subs(&self, n_id: &u32) -> Substitution {
        let mut subs = self.nodes.get(n_id).unwrap().substitution.clone();
        subs.filter();
        for child_id in self.nodes.get(n_id).unwrap().children.iter() {
            subs += self.collect_subs(child_id);
        }
        return subs;
    }
}

struct Hypothesis {
    terms: HashSet<Term>,
    current: Program,
    changes: HashMap<u32, Vec<(Option<Clause>, Clause)>>,
}

impl Hypothesis {
    pub fn new(constraints: Vec<Clause>) -> Hypothesis {
        Hypothesis {
            terms: HashSet::new(),
            current: Program {
                clauses: vec![],
                constraints,
            },
            changes: HashMap::new(),
        }
    }

    pub fn add_clause(&mut self, clause: Clause, n_id: &u32) {
        println!("New Clause:   {}", clause.to_string());
        for atom in &clause.atoms {
            for term in &atom.terms {
                self.terms.insert(term.clone());
            }
        }
        self.current.clauses.push(clause.clone());
        self.changes.insert(*n_id, vec![(None, clause)]);
        println!("H size:   {}", self.current.clauses.len());
    }

    pub fn apply_sub(&mut self, n_id: u32, subs: &Substitution) {
        if !self.terms.iter().any(|t| subs.subs.contains_key(t)) {
            return;
        }
        for i in 0..self.current.clauses.len() {
            let old = &self.current.clauses[i];
            let new = old.apply_sub(subs);
            let mut changes: Vec<(Option<Clause>, Clause)> = vec![];
            if *old != new {
                changes.push((Some(old.clone()), new.clone()));
                self.current.clauses[i] = new;
            }
            self.changes.insert(n_id, changes);
        }
    }
    pub fn undo_sub(&mut self, n_id: &u32) {
        let changes = match self.changes.remove(&n_id) {
            Some(v) => v,
            None => return,
        };
        for (new, old) in changes {
            for i in 0..self.current.clauses.len() {
                if self.current.clauses[i] == old {
                    match new {
                        Some(clause) => {
                            self.current.clauses[i] = clause;
                            break;
                        }
                        None => {
                            self.current.clauses.remove(i);
                        }
                    }
                }
            }
        }
    }
}
