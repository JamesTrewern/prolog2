use std::collections::HashMap;

use crate::{
    atoms::Atom,
    clause::Clause,
    heap::{self, Heap},
    program::{Choice, Program},
    terms::{Substitution, Term},
};

const MAX_H_SIZE: usize = 3;
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

pub struct Proof<'a> {
    heap: &'a mut Heap,
    prog: &'a Program,
    node_id_counter: usize,
    nodes: HashMap<usize, Node>,
    choice_points: Vec<(usize, Choice)>,
    hypothesis: Hypothesis,
}

impl<'a> Proof<'a> {
    pub fn new(mut goals: Vec<Atom>, prog: &'a Program, heap: &'a mut Heap) -> Proof<'a> {
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
            choice_points: vec![],
            hypothesis: Hypothesis::new(prog.constraints.clone()),
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
        let node = self.nodes.remove(&n_id).unwrap();
        self.heap.undo_sub(node.substitution);
        self.choice_points.retain(|(c_id, _)| *c_id != n_id);
        self.hypothesis.remove_clause(n_id);
    }

    fn path(&self, n1_id: &usize, n2_id: &usize) -> Option<Vec<usize>> {
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

    //----------------------------------------------------------------------------------

    pub fn start_proof(&mut self) {
        let mut proven = true;
        for child_id in &self.nodes[&0].children.clone() {
            if !self.prove(child_id.clone(), 0) {
                proven = false;
                break;
            }
        }
        if !proven {
            proven = self.retry_from(0, 0);
        }
        if proven {
            println!("\n\nTRUE\n");
        } else {
            println!("\n\nFALSE\n");
        }
        self.hypothesis.write_prog(self.heap);
        //println!("{:?}", self.heap);
    }

    fn prove(&mut self, n_id: usize, depth: u8) -> bool {
        if depth == 5 {
            return false;
        }
        let goal = &self.nodes[&n_id].goal;
        println!("\n[{}]: Goal: {}", depth, goal.to_string(&self.heap));

        let mut choices = self.hypothesis.match_head_to_goal(goal, self.heap);
        if self.heap.get_term(goal.terms[0]).enum_type() == "Ref" {
            let mut prog_match = self.prog.match_head_to_goal(&goal, &mut self.heap, false);
            prog_match.retain(|choice| self.hypothesis.valid_sub(&choice.subs, self.heap));
            choices.append(&mut prog_match);
        } else {
            choices.append(&mut self.prog.match_head_to_goal(&goal, &mut self.heap, false));
        }
        for _ in 0..choices.len() {
            let choice = choices.remove(0);
            if self.prove_choice(n_id, choice, depth) {
                choices
                    .into_iter()
                    .map(|choice| self.choice_points.push((n_id, choice)));
                return true;
            } else {
                self.reset_node(n_id);
            }
        }

        return false;
    }

    fn prove_choice(&mut self, n_id: usize, mut choice: Choice, depth: u8) -> bool {
        choice.choose(self.heap);
        if let Some(new_clause) = choice.new_clause {
            if !self.hypothesis.add_clause(new_clause, n_id, &self.heap) {
                return false;
            }
        }
        if !self.hypothesis.valid_sub(&choice.subs, self.heap) {
            println!("{}", choice.subs.to_string(self.heap));
            return false;
        }
        choice.subs.filter(self.heap);
        self.nodes.get_mut(&n_id).unwrap().substitution = choice.subs.clone();
        self.heap.apply_sub(choice.subs);

        let len = choice.goals.len();
        for goal in choice.goals {
            self.add_child_node(n_id, Node::new(goal));
        }
        let mut proven = true;
        for i in 0..len {
            if !self.prove(self.nodes[&n_id].children[i], depth + 1) {
                proven = false;
                break;
            }
        }
        if proven == false {
            return self.retry_from(n_id, depth);
        }

        return proven;
    }

    // fn retry_from(&mut self, n_id: usize, depth: u8) -> bool{
    //     let mut children = self.children(n_id);
    //     while let Some(child_id) = children.pop() {
    //         if self.choice_points.contains_key(&child_id) {
    //             let path = self.path(&n_id, &child_id).unwrap();
    //             //TO DO maybe save remaining choice points for future
    //             for choice in self.choice_points.remove(&child_id).unwrap() {
    //                 if self.retry(path.clone(), choice, depth) {
    //                     return true;
    //                 }
    //             }
    //         }
    //     }
    //     return false;
    // }

    fn retry_from(&mut self, n_id: usize, depth: u8) -> bool {
        if self.choice_points.is_empty() {
            return false;
        }
        let mut i = self.choice_points.len() - 1;
        loop {
            let choice = &self.choice_points[i];

            if let Some(path) = self.path(&n_id, &choice.0) {
                let (_, choice) = self.choice_points.remove(i);
                if self.retry(path, choice, depth) {
                    return true;
                }
            };
            if i == 0 {
                break;
            }
            i -= 1;
        }
        return false;
    }

    fn retry(&mut self, mut path: Vec<usize>, choice: Choice, depth: u8) -> bool {
        let n_id = path.pop().unwrap();
        if path.len() == 0 {
            return self.prove_choice(n_id, choice, depth);
        }
        let children = self.nodes.get(&n_id).unwrap().children.clone();
        let i = children
            .iter()
            .position(|c_id| c_id == path.last().unwrap())
            .unwrap();
        for child_id in &children[i..] {
            self.reset_node(*child_id);
        }
        return self.retry(path, choice, depth + 1);
    }

    fn reset_node(&mut self, n_id: usize) {
        while let Some(child_id) = self.nodes.get_mut(&n_id).unwrap().children.pop() {
            self.delete_node(child_id);
        }
        self.hypothesis.remove_clause(n_id);
    }
}

struct Hypothesis {
    clauses: Vec<(usize, Clause)>,
    constraints: Vec<Clause>,
}

impl Hypothesis {
    pub fn new(constraints: Vec<Clause>) -> Hypothesis {
        Hypothesis {
            clauses: vec![],
            constraints,
        }
    }

    pub fn add_clause(&mut self, clause: Clause, n_id: usize, heap: &Heap) -> bool {
        if self.clauses.len() == MAX_H_SIZE {
            return false;
        }
        println!("New Clause:   {}", clause.to_string(heap));
        self.clauses.push((n_id, clause.clone()));
        println!("H size:   {}", self.clauses.len());
        return true;
    }

    pub fn remove_clause(&mut self, n_id: usize) {
        //TO DO store revelvent nodes and don't call if no clause introduced
        for i in 0..self.clauses.len() {
            if self.clauses[i].0 == n_id {
                self.clauses.remove(i);
            }
        }
    }

    pub fn write_prog(&self, heap: &Heap) {
        for (_, clause) in self.clauses.iter() {
            println!("{}", clause.to_string(heap));
        }
    }

    pub fn match_head_to_goal(&self, goal: &Atom, heap: &mut Heap) -> Vec<Choice> {
        let mut choices: Vec<Choice> = vec![];
        for (_, clause) in &self.clauses {
            match clause.atoms[0].unify(&goal, heap) {
                Some(mut subs) => {
                    println!(
                        "Matched: {}\nSubs:   {}",
                        clause.to_string(heap),
                        subs.to_string(heap)
                    );
                    let goals_clause = clause.body().apply_sub(&subs);

                    let subbed_clause = clause.apply_sub(&subs);
                    //println!("Subbed C: {}", subbed_clause.to_string());
                    if self.constraints.iter().any(|c| {
                        if c.can_unfiy(&subbed_clause, heap) {
                            println!("Denied: {}", subbed_clause.to_string(heap));
                            println!("Contraint: {}", c.to_string(heap));
                            true
                        } else {
                            false
                        }
                    }) {
                        continue;
                    }

                    choices.push(Choice {
                        goals: goals_clause.atoms,
                        subs,
                        new_clause: None,
                    })
                }
                None => (),
            }
        }
        return choices;
    }

    pub fn valid_sub(&self, sub: &Substitution, heap: &mut Heap) -> bool {
        for (_, clause) in self.clauses.iter() {
            if !clause.terms().iter().any(|t| sub.subs.contains_key(t)) {
                continue;
            }
            let subbed_clause = clause.apply_sub(sub);
            if self.constraints.iter().any(|c| {
                if c.can_unfiy(&subbed_clause, heap) {
                    true
                } else {
                    false
                }
            }) {
                println!("{}", subbed_clause.to_string(heap));
                return false;
            }
        }
        return true;
    }
}
