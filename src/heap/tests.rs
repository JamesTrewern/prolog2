mod symbol_db {
    use super::super::{heap::CON_PTR, symbol_db::SymbolDB};

    #[test]
    //Check required symbols are preloaded
    fn known_symbols() {
        SymbolDB::new();
        assert_eq!(&*SymbolDB::get_const(CON_PTR), "false");
        assert_eq!(&*SymbolDB::get_const(CON_PTR + 1), "true");
    }

    #[test]
    fn insert_constant_symbol() {
        SymbolDB::new();

        let id = SymbolDB::set_const("a".into());

        assert_eq!(&*SymbolDB::get_const(id), "a");
        assert_eq!(SymbolDB::set_const("a".into()), id);
    }

    #[test]
    fn insert_variable_symbol() {
        SymbolDB::new();

        SymbolDB::set_var("X".into(), 100, 0);
        SymbolDB::set_var("Y".into(), 200, 1);
        SymbolDB::set_var("Z".into(), 200, 2);

        assert_eq!(*SymbolDB::get_var(100, 0).unwrap(), *"X");
        assert_eq!(*SymbolDB::get_var(200, 1).unwrap(), *"Y");
        assert_eq!(*SymbolDB::get_var(200, 2).unwrap(), *"Z");
    }

    #[test]
    fn insert_string() {
        SymbolDB::new();
        let idx = SymbolDB::set_string("some string".into());
        assert_eq!(*SymbolDB::get_string(idx), *"some string");
    }
}

mod heap {
    use crate::heap::heap::Tag;

    use super::super::{
        heap::{Cell, Heap, EMPTY_LIS},
        symbol_db::SymbolDB,
    };



    #[test]
    fn encode_argument_variable() {
        let mut heap = Vec::<Cell>::new();

        let addr1 = heap.set_arg(0);
        let addr2 = heap.set_arg(1);

        SymbolDB::set_var("X".into(), addr1, 0);
        SymbolDB::set_var("Y".into(), addr2, 0);

        assert_eq!(heap.term_string(addr1), "X");
        assert_eq!(heap.term_string(addr2), "Y");
    }

    #[test]
    fn encode_ref_variable() {
        let mut heap = Vec::<Cell>::new();

        let addr1 = heap.set_ref(None);
        let addr2 = heap.set_ref(Some(addr1));

        SymbolDB::set_var("X".into(), addr1, 0);

        assert_eq!(heap.term_string(addr1), "X");
        assert_eq!(heap.term_string(addr2), "X");
    }

    #[test]
    fn encode_constant() {
        let mut heap = Vec::<Cell>::new();

        let a = SymbolDB::set_const("a".into());
        let b = SymbolDB::set_const("b".into());

        let addr1 = heap.set_const(a);
        let addr2 = heap.set_const(b);

        assert_eq!(heap.term_string(addr1), "a");
        assert_eq!(heap.term_string(addr2), "b");
    }

    #[test]
    fn encode_functor() {
        let p = SymbolDB::set_const("p".into());
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Arg, 0),
            (Tag::Con, a),
        ];
        assert_eq!(heap.term_string(0), "p(Arg_0,a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "p(f(Ref_7),a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "p((f,Ref_7),a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Str, 5),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "p({f,Ref_7},a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Lis, 5),
            (Tag::Con, a),
            (Tag::Con, f),
            (Tag::Lis, 7),
            (Tag::Ref, 7),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "p([f,Ref_7],a)");
    }

    #[test]
    fn encode_tuple() {
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let heap: Vec<Cell> = vec![(Tag::Str, 1), (Tag::Tup, 2), (Tag::Arg, 0), (Tag::Con, a)];
        assert_eq!(heap.term_string(0), "(Arg_0,a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "(f(Ref_6),a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "((f,Ref_6),a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "({f,Ref_6},a)");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Tup, 2),
            (Tag::Lis, 4),
            (Tag::Con, a),
            (Tag::Con, f),
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "([f,Ref_6],a)");
    }

    #[test]
    fn encode_list() {

        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let heap: Vec<Cell> = vec![
            (Tag::Lis, 1),
            (Tag::Arg, 0),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "[Arg_0,a]");

        let heap: Vec<Cell> = vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "[f(Ref_7),a]");

        let heap: Vec<Cell> = vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "[(f,Ref_7),a]");

        let heap: Vec<Cell> = vec![
            (Tag::Lis, 1),
            (Tag::Str, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "[{f,Ref_7},a]");

        let heap: Vec<Cell> = vec![
            (Tag::Lis, 1),
            (Tag::Lis, 5),
            (Tag::Lis, 3),
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Con, f),
            (Tag::Lis, 7),
            (Tag::Ref, 7),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "[[f,Ref_7],a]");
    }

    #[test]
    fn encode_set() {
        
        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let heap: Vec<Cell> = vec![(Tag::Str, 1), (Tag::Set, 2), (Tag::Arg, 0), (Tag::Con, a)];
        assert_eq!(heap.term_string(0), "{Arg_0,a}");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Func, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "{f(Ref_6),a}");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "{(f,Ref_6),a}");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Str, 4),
            (Tag::Con, a),
            (Tag::Set, 2),
            (Tag::Con, f),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "{{f,Ref_6},a}");

        let heap: Vec<Cell> = vec![
            (Tag::Str, 1),
            (Tag::Set, 2),
            (Tag::Lis, 4),
            (Tag::Con, a),
            (Tag::Con, f),
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "{[f,Ref_6],a}");
    }

    #[test]
    fn dereference() {

        let f = SymbolDB::set_const("f".into());
        let a = SymbolDB::set_const("a".into());

        let heap: Vec<Cell> = vec![(Tag::Ref, 1), (Tag::Ref, 2), (Tag::Ref, 3), (Tag::Ref, 3)];
        assert_eq!(heap.term_string(0), "Ref_3");

        let heap: Vec<Cell> = vec![(Tag::Ref, 1), (Tag::Ref, 2), (Tag::Ref, 3), (Tag::Arg, 0)];
        assert_eq!(heap.term_string(0), "Arg_0");

        let heap: Vec<Cell> = vec![(Tag::Ref, 1), (Tag::Ref, 2), (Tag::Ref, 3), (Tag::Con, a)];
        assert_eq!(heap.term_string(0), "a");

        let heap: Vec<Cell> = vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Func, 3),
            (Tag::Con, f),
            (Tag::Con, a),
            (Tag::Ref, 7),
        ];
        assert_eq!(heap.term_string(0), "f(a,Ref_7)");

        let heap: Vec<Cell> = vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Tup, 2),
            (Tag::Con, a),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "(a,Ref_6)");

        let heap: Vec<Cell> = vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Str, 4),
            (Tag::Set, 2),
            (Tag::Con, a),
            (Tag::Ref, 6),
        ];
        assert_eq!(heap.term_string(0), "{a,Ref_6}");

        let heap: Vec<Cell> = vec![
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Ref, 3),
            (Tag::Lis, 4),
            (Tag::Con, a),
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            EMPTY_LIS,
        ];
        assert_eq!(heap.term_string(0), "[a,Ref_6]");
    }
}
