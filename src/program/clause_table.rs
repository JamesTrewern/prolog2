use crate::heap::heap::Heap;
use std::{cmp::Ordering, ops::Range};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseMetaData {
    Clause((usize, usize)),     // Literals range
    Meta((usize, usize), u128), // Literals range, Existential variables bitflags
}

impl ClauseMetaData {
    pub fn literals(&self) -> Range<usize> {
        match self {
            ClauseMetaData::Clause(range) => range.0..range.1,
            ClauseMetaData::Meta(range, _) => range.0..range.1,
        }
    }

    pub fn head(&self) -> usize {
        match self {
            ClauseMetaData::Clause(range) => range.0,
            ClauseMetaData::Meta(range, _) => range.0,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            ClauseMetaData::Clause(range) => range.1 - range.0,
            ClauseMetaData::Meta(range, _) => range.1 - range.0,
        }
    }

    //Increment literals index range start and end by step
    pub fn shift_indexes(&mut self, step: isize) {
        let range = match self {
            ClauseMetaData::Clause(range) => range,
            ClauseMetaData::Meta(range, _) => range,
        };

        *range = (
            (range.0 as isize + step) as usize,
            (range.1 as isize + step) as usize,
        );
    }
}

pub struct ClauseTable {
    clauses: Vec<ClauseMetaData>,
    literal_addrs: Vec<usize>, //Heap addresses of clause literals
}

/**Given 2 clauses returns order between them
 * @c1: 1st clause
 * @c2: 2nd clause
 * @literals: The clause table's list of literal addresses
 * @heap: The heap
 */
fn order_clauses(
    c1: &ClauseMetaData,
    c2: &ClauseMetaData,
    literals: &[usize],
    heap: &impl Heap,
) -> Ordering {
    let symbol_arity1 = heap.str_symbol_arity(literals[c1.head()]);
    let symbol_arity2 = heap.str_symbol_arity(literals[c2.head()]);
    symbol_arity1.cmp(&symbol_arity2)
}

impl ClauseTable {
    pub fn new() -> ClauseTable {
        ClauseTable {
            clauses: vec![],
            literal_addrs: vec![],
        }
    }

    pub fn get(&self, i: usize) -> Option<ClauseMetaData> {
        self.clauses.get(i).map(|&clause| clause)
    }

    pub fn get_literals(&self, range: Range<usize>) -> &[usize] {
        &self.literal_addrs[range]
    }

    pub fn insert(&mut self, literals: Vec<usize>, meta_vars: Option<u128>, heap: &impl Heap) -> usize{
        //Find insertion point
        let mut i = 0;
        let mut total_len = 0;
        while let Some(c2) = self.get(i) {
            let symbol_arity1 = heap.str_symbol_arity(literals[0]);
            let symbol_arity2 = heap.str_symbol_arity(self.literal_addrs[c2.head()]);

            if symbol_arity1.cmp(&symbol_arity2) == Ordering::Less {
                break;
            } else {
                total_len += c2.len();
                i += 1;
            }
        }

        //Insert Clause
        let literals_range = (total_len, total_len + literals.len());
        let new_clause = match meta_vars {
            Some(meta_vars) => ClauseMetaData::Meta(literals_range, meta_vars),
            None => ClauseMetaData::Clause(literals_range),
        };
        self.clauses.insert(i, new_clause);
        self.literal_addrs.splice(total_len..total_len, literals);
        let insert_index = i;

        //Update following clauses
        i += 1;
        while let Some(clause) = self.clauses.get_mut(i) {
            clause.shift_indexes(new_clause.len() as isize);
            i+=1;
        }
        insert_index
    }

    // pub fn remove(&mut self, i: usize) {
    //     let clause = self.clauses.remove(i);
    //     let step = - (clause.len() as isize);
    //     self.litteral_addrs.drain(clause.literals());
    //     for clause in &mut self.clauses[i..]{
    //         clause.shift_indexes(step);
    //     }
    // }

    pub fn remove_clauses(&mut self, is: Range<usize>) {
        let lb = self.clauses[is.start].head();
        let clauses = self.clauses.drain(is);
        let total_len = clauses.fold(0, |acc, clause| acc + clause.len());
        let ub = lb + total_len;

        self.literal_addrs.drain(lb..ub);

        for clause in &mut self.clauses[lb..] {
            clause.shift_indexes(-(total_len as isize));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::{max, min};

    use crate::heap::{
        heap::{Cell, Tag},
        symbol_db::SymbolDB,
    };

    use super::{ClauseMetaData, ClauseTable};

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

        let clause_table = ClauseTable {
            clauses: vec![
                ClauseMetaData::Meta((0, 1), 0),
                ClauseMetaData::Meta((1, 2), 0),
                ClauseMetaData::Clause((2, 3)),
                ClauseMetaData::Clause((3, 4)),
                ClauseMetaData::Clause((4, 5)),
                ClauseMetaData::Clause((5, 6)),
            ],
            literal_addrs: vec![0, 4, 9, 12, 16, 19],
        };

        (heap, clause_table)
    }

    #[test]
    fn get() {
        let (heap,clause_table) = setup();

        assert_eq!(clause_table.get(0).unwrap(), ClauseMetaData::Meta((0,1), 0));
        assert_eq!(clause_table.get_literals(clause_table.get(0).unwrap().literals()), [0]);

        assert_eq!(clause_table.get(3).unwrap(), ClauseMetaData::Clause((3,4)));
        assert_eq!(clause_table.get_literals(clause_table.get(3).unwrap().literals()), [12]);

        assert_eq!(clause_table.get(5).unwrap(), ClauseMetaData::Clause((5,6)));
        assert_eq!(clause_table.get_literals(clause_table.get(5).unwrap().literals()), [19]);

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
        let i1 = clause_table.insert(literals_1.clone(), None, &heap);


        let literals_2 = vec![heap.len(),heap.len()+1];
        heap.append(&mut vec![
            (Tag::Con, symbol),
            (Tag::Func, 2),
            (Tag::Con, symbol),
            (Tag::Arg, 0)
        ]);
        let i2 = clause_table.insert(literals_2.clone(), None, &heap);

        let literals_3 = vec![heap.len()];
        heap.append(&mut vec![
            (Tag::Func, 2),
            (Tag::Arg, 0),
            (Tag::Arg, 1)
        ]);
        let i3 = clause_table.insert(literals_3.clone(), Some(0), &heap);

        assert_eq!(clause_table.literal_addrs, [literals_3[0],0, 4, 9, 12, 16, 19, literals_2[0], literals_2[1], literals_1[0],literals_1[1]]);

        assert_eq!(clause_table.get(i3).unwrap(), ClauseMetaData::Meta((0,1), 0));
        assert_eq!(clause_table.get_literals(clause_table.get(i3).unwrap().literals()), literals_3);

        assert_eq!(clause_table.get(i2+1).unwrap(), ClauseMetaData::Clause((7,9)));
        assert_eq!(clause_table.get_literals(clause_table.get(i2+1).unwrap().literals()), literals_2);

        assert_eq!(clause_table.get(i1+2).unwrap(), ClauseMetaData::Clause((9,11)));
        assert_eq!(clause_table.get_literals(clause_table.get(i1+2).unwrap().literals()), literals_1);
    }

    #[test]
    fn remove_clauses(){
        let (heap,mut clause_table) = setup();

        clause_table.remove_clauses(0..2);

        assert_eq!(clause_table.literal_addrs,[9, 12, 16, 19]);
        assert_eq!(clause_table.clauses,[
            ClauseMetaData::Clause((0, 1)),
            ClauseMetaData::Clause((1, 2)),
            ClauseMetaData::Clause((2, 3)),
            ClauseMetaData::Clause((3, 4)),
        ]);
    }
}
