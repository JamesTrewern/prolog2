use std::{collections::HashMap, mem};

use super::{
    build_tree::TreeClause,
    term::{Term, Unit},
};
use crate::{heap::{
    heap::{Cell, Heap, Tag, EMPTY_LIS}, query_heap::QueryHeap, symbol_db::SymbolDB
}, program::{clause::{self, Clause}, predicate_table::{self, PredicateTable}}, resolution::proof::Proof};

pub fn build_clause(literals: Vec<Term>, meta_vars: Option<Vec<String>>, heap: &mut impl Heap, query: bool) -> Clause{
    let mut var_values = HashMap::new();

    let literals: Vec<usize> = literals
        .into_iter()
        .map(|term| term.encode(heap, &mut var_values, query))
        .collect();

    let meta_vars = meta_vars.map(|vars| {
        vars.into_iter()
            .map(|var| *var_values.get(&var).unwrap())
            .collect::<Vec<usize>>()
    });

    Clause::new(literals, meta_vars)
}

pub fn execute_directive(directive: Vec<Term>, predicate_table: &mut PredicateTable) -> Result<(),String>{
    let mut heap = QueryHeap::new(None)?;
    let goals = build_clause(directive, None, &mut heap, true);
    //TODO Find Variables in goals to report bindings once solved
    let proof = Proof::new(heap, &goals, predicate_table);

    Ok(())
}

pub(crate) fn execute_tree(syntax_tree: Vec<TreeClause>, heap: &mut impl Heap, pred_table: &mut PredicateTable) {
    for clause in syntax_tree {
        match clause {
            TreeClause::Fact(term) => {
                let clause = build_clause(vec![term], None, heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table.add_clause_to_predicate(clause, symbol_arity).unwrap();
            },
            TreeClause::Rule(terms) => {
                let clause = build_clause(terms, None, heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table.add_clause_to_predicate(clause, symbol_arity).unwrap();
            },
            TreeClause::MetaRule(mut terms) => {
                let meta_vars = if let Term::Set(set_terms) = terms.pop().unwrap(){
                    let mut meta_vars = Vec::new();
                    for set_term in set_terms{
                        if let Term::Unit(Unit::Variable(symbol)) = set_term{
                            meta_vars.push(symbol);
                        }else{
                            panic!("meta variable set should only contain variables")
                        }
                    }
                    meta_vars
                }else{
                    panic!("Last literal in meta_rule wasn't a set")
                };
                let clause = build_clause(terms, Some(meta_vars), heap, false);
                let symbol_arity = heap.str_symbol_arity(clause[0]);
                pred_table.add_clause_to_predicate(clause, symbol_arity).unwrap();

            },
            TreeClause::Directive(terms) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests{
    use crate::{heap::{heap::{Cell, Heap, Tag}, symbol_db::SymbolDB}, parser::execute_tree::execute_tree, program::predicate_table::{Predicate, PredicateTable}};

    use super::super::{build_tree::{TokenStream, TreeClause}, tokeniser::tokenise};

    #[test]
    fn facts(){
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(a,b).q(c).".into()).unwrap()).parse_all().unwrap();

        let [p,q,a,b,c] = ["p","q","a","b","c"].map(|s|SymbolDB::set_const(s.into()));
        
        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p,2)).unwrap(){
            let fact = clauses[0];
            assert_eq!(&heap[fact[0]..fact[0]+4],&[
                (Tag::Func, 3),
                (Tag::Con, p),
                (Tag::Con, a),
                (Tag::Con, b),
            ]);
        }else{
            panic!()
        }

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((q,1)).unwrap(){
            let fact = clauses[0];
            assert_eq!(&heap[fact[0]..fact[0]+3],&[
                (Tag::Func, 2),
                (Tag::Con, q),
                (Tag::Con, c),
            ]);
        }else{
            panic!()
        }
        
    }

    #[test]
    fn rules(){
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(X,Y):-q(X,a),q(Y,b). q(X):-r(X). q(X):-p(X).".into()).unwrap()).parse_all().unwrap();

        let [p,q,r,a,b] = ["p","q","r","a","b",].map(|s|SymbolDB::set_const(s.into()));
        
        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p,2)).unwrap(){
            let rule = clauses[0];
            assert_eq!(&heap[rule[0]..rule[0]+4],&[
                (Tag::Func, 3),
                (Tag::Con, p),
                (Tag::Arg, 0),
                (Tag::Arg, 1),
            ]);
            assert_eq!(&heap[rule[1]..rule[1]+4],&[
                (Tag::Func, 3),
                (Tag::Con, q),
                (Tag::Arg, 0),
                (Tag::Con, a),
            ]);
            assert_eq!(&heap[rule[2]..rule[2]+4],&[
                (Tag::Func, 3),
                (Tag::Con, q),
                (Tag::Arg, 1),
                (Tag::Con, b),
            ]);
        }else{
            panic!()
        }

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((q,1)).unwrap(){
            let rule = clauses[0];
            assert_eq!(&heap[rule[0]..rule[0]+3],&[
                (Tag::Func, 2),
                (Tag::Con, q),
                (Tag::Arg, 0),
            ]);
            assert_eq!(&heap[rule[1]..rule[1]+3],&[
                (Tag::Func, 2),
                (Tag::Con, r),
                (Tag::Arg, 0),
            ]);

            let rule = clauses[1];
            assert_eq!(&heap[rule[0]..rule[0]+3],&[
                (Tag::Func, 2),
                (Tag::Con, q),
                (Tag::Arg, 0),
            ]);
            assert_eq!(&heap[rule[1]..rule[1]+3],&[
                (Tag::Func, 2),
                (Tag::Con, p),
                (Tag::Arg, 0),
            ]);
        }else{
            panic!()
        }
    }

    #[test]
    fn meta_rules(){
        let mut heap = Vec::<Cell>::new();
        let mut pred_table = PredicateTable::new();
        let facts = TokenStream::new(tokenise("p(X,Y):-Q(X,a),R(Y,b),{Q,R}.".into()).unwrap()).parse_all().unwrap();

        let [p,q,r,a,b] = ["p","q","r","a","b",].map(|s|SymbolDB::set_const(s.into()));
        
        execute_tree(facts, &mut heap, &mut pred_table);

        if let Predicate::Clauses(clauses) = pred_table.get_predicate((p,2)).unwrap(){
            let meta_rule = clauses[0];
            assert_eq!(&heap[meta_rule[0]..meta_rule[0]+4],&[
                (Tag::Func, 3),
                (Tag::Con, p),
                (Tag::Arg, 0),
                (Tag::Arg, 1),
            ]);
            assert_eq!(&heap[meta_rule[1]..meta_rule[1]+4],&[
                (Tag::Func, 3),
                (Tag::Arg, 2),
                (Tag::Arg, 0),
                (Tag::Con, a),
            ]);
            assert_eq!(&heap[meta_rule[2]..meta_rule[2]+4],&[
                (Tag::Func, 3),
                (Tag::Arg, 3),
                (Tag::Arg, 1),
                (Tag::Con, b),
            ]);
            assert!(meta_rule.meta_var(2).unwrap());
            assert!(meta_rule.meta_var(3).unwrap());
        }else{
            panic!()
        }
    }
}