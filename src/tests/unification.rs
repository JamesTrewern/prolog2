use std::collections::HashMap;

use crate::{binding, heap::Heap, unification::unify};

fn unify_test_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("P(X,Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (1,Heap::CON_PTR),
            (2,Heap::CON_PTR+1),
            (3,Heap::CON_PTR+2),
        ])
    }
}