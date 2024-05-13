use std::collections::HashMap;

use crate::{heap::Heap, unification::*};
#[test]
fn unify_struct_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("P(X,Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (1,5),
            (2,6),
            (3,7),
        ])
    }
}
#[test]
fn unify_struct_2(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("P(q(X),Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(q(x),y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (4,11),
            (2,9),
            (6,13),
        ])
    }
}

#[test]
fn unify_struct_3(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,x)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,6),
        ])
    }
}
#[test]
fn unify_struct_4(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,Y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,6),
            (7,6)
        ])
    }
}

#[test]
fn unify_struct_5(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn unify_struct_6(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("q(X,X)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p(x,y)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn unify_list_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("[X,X]", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("[x,y]", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn unify_list_2(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("[q(X),Y]", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("[q(x),y]", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,10),
            (5,13),
        ])
    }
}

#[test]
fn unify_list_3(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("[X,y|T]", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("[x,Y|T]", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    heap.print_heap();
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (0,5),
            (7,2),
            (3,8)
        ])
    }
}

#[test]
fn unify_list_4(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("[q(X),Y|T]", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("[q(x),y|T]", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,10),
            (5,13),
            (6,14),
        ])
    }
}

#[test]
fn unify_list_struct_1(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([x,y|T],z)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([x,y],Z)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (3,11),
            (15,7),
        ])
    }
}

#[test]
fn unify_list_struct_2(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([x,y],z)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([],Z)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
// TO DO implement reading this syntax for edge cases, for now this is not important
fn unify_list_struct_3(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([q(X),Y|[]])", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([q(x),y])", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_ne!(binding,None);
    if let Some(binding) = binding{
        assert_eq!(binding[..], [
            (2,12),
            (5,15),
        ])
    }
}

#[test]
fn unify_list_struct_4(){
    let mut heap = Heap::new(50);
    let str1 = heap.build_literal("p([q(X),Y],Y)", &mut HashMap::new(), &vec![]);
    let str2 = heap.build_literal("p([q(x),y],z)", &mut HashMap::new(), &vec![]);
    let binding: Option<Vec<(usize, usize)>> = unify(str1, str2, &heap);
    assert_eq!(binding,None);
}

#[test]
fn build_goal_1(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p(X,Y)", &mut HashMap::new(), &vec![]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    let mut binding: Binding = vec![(literal+2,term_list+2),(literal+3,term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[new_goal+2]);
    assert_eq!(heap[term_list+3],heap[new_goal+3]);

}

#[test]
fn build_goal_2(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p(q(X,Y))", &mut HashMap::new(), &vec![]);
    heap.query_space = true;
    let sub_str = heap[literal+2].1;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    
    let mut binding: Binding = vec![(sub_str+2,term_list+2),(sub_str+3,term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);
    let sub_str = heap[new_goal+2].1;
    heap.print_heap();
    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[sub_str+2]);
    assert_eq!(heap[term_list+3],heap[sub_str+3]);

}

#[test]
fn build_goal_3(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p(X,Y)", &mut HashMap::new(), &vec!["X","Y"]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    let mut binding: Binding = vec![(literal+2,term_list+2),(literal+3,term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[new_goal+2]);
    assert_eq!(heap[term_list+3],heap[new_goal+3]);

}

#[test]
fn build_goal_4(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p(X,y)", &mut HashMap::new(), &vec!["X"]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    let mut binding: Binding = vec![(literal+2,term_list+2)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[new_goal+2]);
    assert_eq!(heap[term_list+3],heap[new_goal+3]);

}

#[test]
fn build_goal_5(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p([X,Y])", &mut HashMap::new(), &vec![]);
    heap.query_space = true;
    let list: usize = heap[literal+2].1;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    
    let mut binding: Binding = vec![(list,term_list+2),(list+2,term_list+3)];

    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    let list:usize = heap[new_goal+2].1;
    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[list]);
    assert_eq!(heap[term_list+3],heap[list+2]);
}

#[test]
fn build_goal_6(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p([X],[X,Y])", &mut HashMap::new(), &vec![]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    
    let (lis1,lis2) = (heap[literal+2].1,heap[literal+3].1);

    let mut binding: Binding = vec![(lis1,term_list+2),(lis2+2,term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    let (lis1,lis2) = (heap[new_goal+2].1,heap[new_goal+3].1);

    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[lis1]);
    assert_eq!(heap[term_list+2],heap[lis2]);
    assert_eq!(heap[term_list+3],heap[lis2+2]);
}

#[test]
fn build_goal_7(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p(q(X,Y),[X,Y])", &mut HashMap::new(), &vec![]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(x,y)", &mut HashMap::new(), &vec![]);
    
    let sub_str= heap[literal+2].1;

    let mut binding: Binding = vec![(sub_str+2,term_list+2),(sub_str+3,term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    let (sub_str,lis) = (heap[new_goal+2].1,heap[new_goal+3].1);

    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[lis]);
    assert_eq!(heap[term_list+3],heap[lis+2]);
    assert_eq!(heap[term_list+2],heap[sub_str+2]);
    assert_eq!(heap[term_list+3],heap[sub_str+3]);
}

#[test]
fn build_goal_8(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("p(x,[y,z])", &mut HashMap::new(), &vec![]);
    heap.query_space = true;
    let mut binding: Binding = vec![];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut None);

    assert!(constant);
    assert_eq!(literal, new_goal);

}

#[test]
fn build_clause_literal_1(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("Q(X)", &mut HashMap::new(), &vec!["X"]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(p,x)", &mut HashMap::new(), &vec![]);
    let mut binding: Binding = vec![(literal+1,term_list+2),(literal+2, term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut Some(vec![]));

    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[new_goal+1]);
    assert_ne!(heap[term_list+3],heap[new_goal+2])
}

#[test]
fn build_clause_literal_2(){
    let mut heap = Heap::new(50);
    heap.query_space = false;
    let literal = heap.build_literal("Q(X,R(Y))", &mut HashMap::new(), &vec!["X"]);
    heap.query_space = true;
    let term_list = heap.build_literal("tl(p,x)", &mut HashMap::new(), &vec![]);


    let mut binding: Binding = vec![(literal+1,term_list+2),(literal+2, term_list+3)];
    let (new_goal, constant) = build_str(&mut binding, literal, &mut heap, &mut Some(vec![]));
    let sub_str = heap[new_goal+3].1;


    assert!(!constant);
    assert_eq!(heap[term_list+2],heap[new_goal+1]);
    assert_ne!(heap[term_list+3],heap[new_goal+2]);
    assert_ne!(heap[literal+3],heap[new_goal+3]);
    assert_eq!(heap[sub_str+1],(Heap::REF, sub_str+1));
    assert_eq!(heap[sub_str+2],(Heap::REF, sub_str+2));


}