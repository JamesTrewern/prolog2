use crate::heap::heap::Heap;
use std::{alloc::GlobalAlloc, cmp::Ordering, ops::{Deref, Range}, sync::Arc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause{
    literals: Arc<[usize]>,
    meta_vars: Option<u128>
}

impl Clause {
    fn meta_vars_to_bit_flags(meta_vars: Vec<usize>) -> u128{
        let mut bit_flags: u128 = 0;
        for meta_var in meta_vars{
            if meta_var > 127{
                panic!("Cant have more than 128 variables in meta clause")
            }
            bit_flags = bit_flags | 1 << meta_var
        }
        bit_flags
    }

    pub fn new(literals: Vec<usize>, meta_vars: Option<Vec<usize>>) -> Self{
        Clause { literals: literals.into(), meta_vars: meta_vars.map(Self::meta_vars_to_bit_flags)}
    }

    pub fn head(&self) -> usize{
        self.literals[0]
    }

    pub fn cmp(&self, other: &Self, heap: &impl Heap) -> Ordering{
        let symbol_arity_1 = heap.str_symbol_arity(self.head());
        let symbol_arity_2 = heap.str_symbol_arity(other.head());
        symbol_arity_1.cmp(&symbol_arity_2)
    }

    pub fn meta(&self) -> bool{
        self.meta_vars.is_some()
    }

    pub fn meta_var(&self, arg_id: usize) -> Result<bool,&'static str>{
        let meta_vars = self.meta_vars.ok_or("Clause is not a meta clause")?;
        Ok(meta_vars & (1 << arg_id) != 0)
    }
}

impl Deref for Clause{
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.literals
    }
}

#[derive(PartialEq,Debug)]
pub struct ClauseTable (Vec<Clause>);

impl ClauseTable {
    pub fn new() -> ClauseTable {
        ClauseTable(vec![])
    }

    pub fn get(&self, i: usize) -> Option<Clause> {
        self.0.get(i).map(|clause| clause.clone())
    }

    pub fn insert(&mut self, clause: Clause, heap: &impl Heap) -> usize{
        let mut i: usize = 0;
        while let Some(other_clause) = self.0.get(i){
            if clause.cmp(other_clause, heap) == Ordering::Less{
                break;
            }else{
                i+=1;
            }
        }
        self.0.insert(i, clause);
        i
    }

    pub fn remove_clauses(&mut self, range: Range<usize>) {
        self.0.drain(range);
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::{max, min};

    use crate::heap::{
        heap::{Cell, Tag},
        symbol_db::SymbolDB,
    };

    use super::{Clause, ClauseTable};

    fn setup() -> (Vec<Cell>,ClauseTable) {
        let p = SymbolDB::set_const("p".into());
        let q = SymbolDB::set_const("q".into());

        let l = max(p, q);
        let h = min(p, q);

        let heap = vec![
            //Arg/1 @ 0
            (Tag::Func, 3),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
            (Tag::Arg, 1),
            //ARG/2 @ 4
            (Tag::Func, 4),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
            (Tag::Arg, 1),
            (Tag::Arg, 1),
            //L/1 @ 9
            (Tag::Func, 2),
            (Tag::Con, l),
            (Tag::Arg, 0),
            //L/2 @ 12
            (Tag::Func, 3),
            (Tag::Con, l),
            (Tag::Arg, 0),
            (Tag::Arg, 0),
            //H/1 @ 16
            (Tag::Func, 2),
            (Tag::Con, h),
            (Tag::Arg, 0),
            //H/2 @ 19
            (Tag::Func, 3),
            (Tag::Con, h),
            (Tag::Arg, 0),
            (Tag::Arg, 0),
        ];

        let clause_table = ClauseTable(vec![
            Clause::new(vec![0], Some(vec![])),
            Clause::new(vec![4], Some(vec![])),
            Clause::new(vec![9], None),
            Clause::new(vec![12], None),
            Clause::new(vec![16], None),
            Clause::new(vec![19], None),
        ]);

        (heap, clause_table)
    }

    #[test]
    fn get() {
        let (heap,clause_table) = setup();

        assert_eq!(clause_table.get(0), Some(Clause{ literals: [0].into(), meta_vars: Some(0) }));

        assert_eq!(clause_table.get(3), Some(Clause{literals: [12].into(), meta_vars: None}));

        assert_eq!(clause_table.get(5), Some(Clause{literals: [19].into(), meta_vars: None}));

        assert_eq!(clause_table.get(6), None);
    }

    #[test]
    fn insert(){
        let (mut heap,mut clause_table) = setup();
        let symbol = SymbolDB::set_const("clause_table_insert".into());
        let p = SymbolDB::set_const("p".into());

        let literals_1 = vec![heap.len(), heap.len()+4];
        heap.append(&mut vec![
            (Tag::Func, 3),
            (Tag::Con, symbol),
            (Tag::Arg, 0),
            (Tag::Arg,1),
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Arg, 0)
        ]);
        let i1 = clause_table.insert(Clause { literals: literals_1.clone().into(), meta_vars: None }, &heap);


        let literals_2 = vec![heap.len(),heap.len()+1];
        heap.append(&mut vec![
            (Tag::Con, symbol),
            (Tag::Func, 2),
            (Tag::Con, symbol),
            (Tag::Arg, 0)
        ]);
        let i2 = clause_table.insert(Clause { literals: literals_2.clone().into(), meta_vars: None }, &heap);

        let literals_3 = vec![heap.len()];
        heap.append(&mut vec![
            (Tag::Func, 2),
            (Tag::Arg, 0),
            (Tag::Arg, 1)
        ]);
        let i3 = clause_table.insert(Clause { literals: literals_3.clone().into(), meta_vars: Some(0) }, &heap);

        assert_eq!(clause_table.get(i3).unwrap(), Clause{ literals: literals_3.into(), meta_vars: Some(0) });
        assert_eq!(clause_table.get(i2+1).unwrap(), Clause{ literals: literals_2.into(), meta_vars: None });
        assert_eq!(clause_table.get(i1+2).unwrap(), Clause{ literals: literals_1.into(), meta_vars: None });
    }

    #[test]
    fn remove_clauses(){
        let (heap,mut clause_table) = setup();

        clause_table.remove_clauses(0..2);

        assert_eq!(clause_table, ClauseTable(vec![
            Clause{ literals: vec![9].into(), meta_vars: None },
            Clause{ literals: vec![12].into(), meta_vars: None },
            Clause{ literals: vec![16].into(), meta_vars: None },
            Clause{ literals: vec![19].into(), meta_vars: None },
        ]));
    }

    #[test]
    fn bit_flags(){
        let clause = Clause::new(vec![0], Some(vec![0,5,10,127]));

        assert_eq!(clause.meta_var(0), Ok(true));
        assert_eq!(clause.meta_var(1), Ok(false));
        assert_eq!(clause.meta_var(5), Ok(true));
        assert_eq!(clause.meta_var(10), Ok(true));
        assert_eq!(clause.meta_var(127), Ok(true));
        assert_eq!(Clause::new(vec![1], None).meta_var(1), Err("Clause is not a meta clause"));
    }
}
