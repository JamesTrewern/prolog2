mod build {
    use crate::heap::{
        store::{Store, Tag},
        symbol_db::SymbolDB,
    };

    use super::super::build::build;

    /**P(X,Y) {Y}*/
    #[test]
    fn build_clause_literal() {
        let p = SymbolDB::set_const("p");
        let x = SymbolDB::set_const("x");
        let y = SymbolDB::set_const("y");
        // P(X,Y) {Y}
        let mut store = Store::from_slice(&[
            (Tag::Func, 3),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
            (Tag::ArgA, 2),
            (Tag::Con, p),
            (Tag::Con, x),
            (Tag::Con, y),
        ]);

        store.arg_regs[0] = 4;
        store.arg_regs[1] = 5;
        store.arg_regs[2] = 6;

        let new_goal = build(0, &mut store, true);

        assert_eq!(
            &store.cells[new_goal..],
            &[(Tag::Func, 3), (Tag::Con, p), (Tag::Con, x), (Tag::Arg, 2)]
        )
    }

    #[test]
    fn build_clause_literal_with_substr() {
        let p = SymbolDB::set_const("p");
        let x = SymbolDB::set_const("x");
        let q = SymbolDB::set_const("q");
        let y = SymbolDB::set_const("y");
        // P(X,Q(Y)) {Y}
        let mut store = Store::from_slice(&[
            (Tag::Func, 2),
            (Tag::Arg, 0),
            (Tag::ArgA, 1),
            (Tag::Func, 3),
            (Tag::Arg, 2),
            (Tag::Arg, 3),
            (Tag::Str, 0),
            (Tag::Con, p),
            (Tag::Con, x),
            (Tag::Con, q),
            (Tag::Con, y),
        ]);

        store.arg_regs[2] = 7;
        store.arg_regs[3] = 8;
        store.arg_regs[0] = 9;
        store.arg_regs[1] = 10;

        let new_goal = build(3, &mut store, true);

        assert_eq!(
            &store.cells[new_goal - 3..],
            &[
                (Tag::Func, 2),
                (Tag::Con, q),
                (Tag::Arg, 1),
                (Tag::Func, 3),
                (Tag::Con, p),
                (Tag::Con, x),
                (Tag::Str, new_goal - 3)
            ]
        )
    }

    #[test]
    fn build_goal_with_sub_str() {
        let p = SymbolDB::set_const("p");
        let x = SymbolDB::set_const("x");
        let q = SymbolDB::set_const("q");
        let y = SymbolDB::set_const("y");

        // p(q(X,Y))
        let mut store = Store::from_slice(&[
            (Tag::Func, 3),
            (Tag::Con, q),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Str, 0),
            (Tag::Con, x),
            (Tag::Con, y),
        ]);

        store.arg_regs[0] = 7;
        store.arg_regs[1] = 8;

        let new_goal = build(4, &mut store, false);
        assert_eq!(
            &store.cells[new_goal - 4..],
            &[
                (Tag::Func, 3),
                (Tag::Con, q),
                (Tag::Con, x),
                (Tag::Con, y),
                (Tag::Func, 2),
                (Tag::Con, p),
                (Tag::Str, new_goal - 4),
            ]
        )
    }
}

mod call {
    use super::super::call::match_head;
    use crate::heap::{
        store::{Store, Tag},
        symbol_db::SymbolDB,
    };

    /**head = p(a,B)
     * goal = p(A,b)
     */
    #[test]
    fn call_arg_and_ref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let mut store = Store::from_slice(&[
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Arg, 0),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Ref, 6),
            (Tag::Con, b),
        ]);
        let binding = match_head(0, 4, &mut store).unwrap();
        assert_eq!(binding[0], (6, 2));
        assert_eq!(store.arg_regs[0], 7);
    }

    /** p(A,B)
     *  p(X,Y)
     */
    #[test]
    fn call_with_refs() {
        let p = SymbolDB::set_const("p");
        let mut store = Store::from_slice(&[
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Ref, 6),
            (Tag::Ref, 7),
        ]);

        let binding = match_head(0, 4, &mut store).unwrap();
        assert_eq!(&binding[..], &[]);
        assert_eq!(&store.arg_regs[..2], &[6, 7]);
    }

    /** P(A,B) {A,B}
     *  p(X,Y)
     */
    #[test]
    fn call_meta_arguments_with_refs() {
        let p = SymbolDB::set_const("p");
        let mut store = Store::from_slice(&[
            (Tag::Func, 3),
            (Tag::Arg, 0),
            (Tag::ArgA, 1),
            (Tag::ArgA, 2),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Ref, 6),
            (Tag::Ref, 7),
        ]);
        let binding = match_head(0, 4, &mut store).unwrap();
        assert_eq!(&binding[..], &[]);
        assert_eq!(&store.arg_regs[..3], &[5, 6, 7]);
    }

    /**P(A,B) {A,B}
     * p(a,b)
     */
    #[test]
    fn unfify_const_with_meta_arguments() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let mut store = Store::from_slice(&[
            (Tag::Func, 3),
            (Tag::Arg, 0),
            (Tag::ArgA, 1),
            (Tag::ArgA, 2),
            (Tag::Func, 3),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Con, b),
        ]);

        let binding = match_head(0, 4, &mut store).unwrap();
        assert_eq!(&binding[..], &[]);
        assert_eq!(&store.arg_regs[..3], &[5, 6, 7]);
    }
}

mod unification {
    use super::super::unification::{unify, Binding};
    use crate::heap::store::{Store, Tag};

    #[test]
    fn unfify_const_structs() {
        let p = Store::CON_PTR;
        let a = Store::CON_PTR + 1;
        let b = Store::CON_PTR + 2;
        let store = Store::from_slice(&[
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Con, b),
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Con, b),
        ]);

        let mut binding = Binding::new();
        unify(0, 4, &store, &mut binding);
        assert_eq!(&binding[..], &[]);
    }

    #[test]
    fn unfify_const_with_var_list() {
        let a = Store::CON_PTR;
        let b = Store::CON_PTR + 1;
        let store = Store::from_slice(&[
            (Tag::Lis, 1),
            (Tag::Con, a),
            (Tag::Lis, 3),
            (Tag::Con, b),
            Store::EMPTY_LIS,
            (Tag::Lis, 6),
            (Tag::Ref, 6),
            (Tag::Lis, 8),
            (Tag::Ref, 8),
            (Tag::Ref, 9),
        ]);

        let mut binding = Binding::new();
        unify(0, 5, &store, &mut binding);
        assert_eq!(&binding[..], &[(6, 1), (8, 3), (9, 4)]);
    }

    #[test]
    fn unfify_const_lists() {
        let a = Store::CON_PTR;
        let b = Store::CON_PTR + 1;
        let store = Store::from_slice(&[
            (Tag::Lis, 1),
            (Tag::Con, a),
            (Tag::Lis, 3),
            (Tag::Con, b),
            Store::EMPTY_LIS,
            (Tag::Lis, 6),
            (Tag::Con, a),
            (Tag::Lis, 8),
            (Tag::Con, b),
            Store::EMPTY_LIS,
        ]);

        let mut binding = Binding::new();
        unify(0, 5, &store, &mut binding);
        assert_eq!(&binding[..], &[]);
    }

    #[test]
    fn unfify_const_with_meta_list() {
        let a = Store::CON_PTR;
        let b = Store::CON_PTR + 1;
        let store = Store::from_slice(&[
            (Tag::Lis, 1),
            (Tag::Con, a),
            (Tag::Lis, 3),
            (Tag::Con, b),
            Store::EMPTY_LIS,
            (Tag::Lis, 6),
            (Tag::ArgA, 6),
            (Tag::Lis, 8),
            (Tag::ArgA, 8),
            (Tag::ArgA, 9),
        ]);

        let mut binding = Binding::new();
        unify(0, 5, &store, &mut binding);
        assert_eq!(&binding[..], &[(6, 1), (8, 3), (9, 4)]);
    }

    #[test]
    fn unify_ref_to_con_with_con() {
        let p = Store::CON_PTR;
        let a = Store::CON_PTR + 1;
        let b = Store::CON_PTR + 2;
        let store = Store::from_slice(&[
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Con, b),
            (Tag::Con, p),
            (Tag::Func, 2),
            (Tag::Ref, 4),
            (Tag::Con, a),
            (Tag::Ref, 8),
        ]);

        let mut binding = Binding::new();
        unify(0, 5, &store, &mut binding);

        assert_eq!(&binding[..], &[(8, 3)]);
    }
}
