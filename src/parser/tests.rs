use super::{
    syntax_tree::{Clause, Term, TokenStream, Unit},
    tokeniser::tokenise,
};

mod tokenizer {
    use crate::parser::tokeniser::{remove_comments, tokenise};

    #[test]
    fn single_line_comments() {
        let mut file =
            "\n%simple predicate\np(x,y):-%The head\nq(x),%body 1\nr(y).%body 2".to_string();

        let tokens = tokenise(file).unwrap();

        assert_eq!(
            tokens,
            [
                "\n", "\n", "p", "(", "x", ",", "y", ")", ":-", "\n", "q", "(", "x", ")", ",",
                "\n", "r", "(", "y", ")", "."
            ]
        );
    }

    #[test]
    fn multi_line_comments() {
        let mut file = "/* This is a\nmutli\nline\ncomment */\np(x,y):-q(x,y).".to_string();

        let tokens = tokenise(file).unwrap();

        assert_eq!(
            tokens,
            [
                "\n", "\n", "\n", "\n", "p", "(", "x", ",", "y", ")", ":-", "q", "(", "x", ",",
                "y", ")", "."
            ]
        )
    }

    #[test]
    fn unclosed_multi_line_comments() {
        let file = "p(x,y):-q(x,y)
        /* a comment
        on two lines
        fact(a,b)."
            .to_string();

        match tokenise(file) {
            Ok(tokens) => panic!("Should have thrown error\nTokens: {tokens:?}"),
            Err(message) => assert_eq!(message, "Unclosed multi line comment"),
        }
    }

    #[test]
    fn unclosed_strings() {
        let mut file = "\"a string".to_string();

        match tokenise(file) {
            Ok(tokens) => panic!("Should have thrown error\nTokens: {tokens:?}"),
            Err(message) => assert_eq!(message, "Unexpected end of file, missing closing \""),
        }

        let mut file = "'a string".to_string();

        match tokenise(file) {
            Ok(tokens) => panic!("Should have thrown error\nTokens: {tokens:?}"),
            Err(message) => assert_eq!(message, "Unexpected end of file, missing closing '"),
        }
    }

    #[test]
    fn string_tokenisation() {
        assert_eq!(tokenise("\"a.b\'/c\"".into()).unwrap(), ["\"a.b'/c\""]);
        assert_eq!(tokenise("'a.b\"/c'".into()).unwrap(), ["'a.b\"/c'"]);

        assert_eq!(
            tokenise("p(\"a.b\'/c\").".into()).unwrap(),
            ["p", "(", "\"a.b'/c\"", ")", "."]
        );
    }

    #[test]
    fn string_escape_characters() {
        assert_eq!(tokenise("\"a\\\"b\"".into()).unwrap(), ["\"a\"b\""]);

        assert_eq!(tokenise("'a\\'b'".into()).unwrap(), ["'a'b'"]);

        assert_eq!(
            tokenise("\" \\n \\t \\\\ \"".into()).unwrap(),
            ["\" \n \t \\ \""]
        );
    }

    #[test]
    fn float_tokenisation() {
        assert_eq!(tokenise("123.123".into()).unwrap(), ["123.123"]);
        assert_eq!(
            tokenise("123.123.123".into()).unwrap(),
            ["123.123", ".", "123"]
        );
        assert_eq!(tokenise("123 . 123".into()).unwrap(), ["123", ".", "123"]);
    }

    #[test]
    fn negative_number_tokenisation() {
        assert_eq!(tokenise("-123 - 123".into()).unwrap(), ["-123", "-", "123"]);
        assert_eq!(tokenise("-123.123".into()).unwrap(), ["-123.123"]);
        assert_eq!(tokenise("- 123.123".into()).unwrap(), ["-", "123.123"]);
        assert_eq!(tokenise("-123 . 123".into()).unwrap(), ["-123", ".", "123"]);
    }

    #[test]
    fn list_tokenisation() {
        assert_eq!(
            tokenise("[123,abc, VAR]".into()).unwrap(),
            ["[", "123", ",", "abc", ",", "VAR", "]"]
        );
        assert_eq!(
            tokenise("[123,abc, VAR|T]".into()).unwrap(),
            ["[", "123", ",", "abc", ",", "VAR", "|", "T", "]"]
        );
        assert_eq!(
            tokenise("[123,abc, VAR | T]".into()).unwrap(),
            ["[", "123", ",", "abc", ",", "VAR", "|", "T", "]"]
        );
    }

    #[test]
    fn empty_list_token() {
        assert_eq!(tokenise("[]".into()).unwrap(), ["[]"]);
        assert_eq!(tokenise("[ ]".into()).unwrap(), ["[]"]);
        assert_eq!(tokenise("[\n]".into()).unwrap(), ["[]", "\n"]);
        assert_eq!(tokenise("[\n\n]".into()).unwrap(), ["[]", "\n", "\n"]);
        assert_eq!(tokenise("[\t]".into()).unwrap(), ["[]"]);
        assert_eq!(tokenise("[  \n\t\n ]".into()).unwrap(), ["[]", "\n", "\n"]);
    }

    #[test]
    fn empty_set_token() {
        assert_eq!(tokenise("{}".into()).unwrap(), ["{}"]);
        assert_eq!(tokenise("{ }".into()).unwrap(), ["{}"]);
        assert_eq!(tokenise("{\n}".into()).unwrap(), ["{}", "\n"]);
        assert_eq!(tokenise("{\n\n}".into()).unwrap(), ["{}", "\n", "\n"]);
        assert_eq!(tokenise("{\t}".into()).unwrap(), ["{}"]);
        assert_eq!(tokenise("{  \n\t\n }".into()).unwrap(), ["{}", "\n", "\n"]);
    }

    #[test]
    fn known_symbol_formation() {
        assert_eq!(tokenise(":-".into()).unwrap(), [":-"]);
        assert_eq!(tokenise(": -".into()).unwrap(), [":", "-"]);

        assert_eq!(tokenise("==".into()).unwrap(), ["=="]);
        assert_eq!(tokenise("= =".into()).unwrap(), ["=", "="]);

        assert_eq!(tokenise("=/=".into()).unwrap(), ["=/="]);
        assert_eq!(tokenise("= / =".into()).unwrap(), ["=", "/", "="]);

        assert_eq!(tokenise("/=".into()).unwrap(), ["/="]);
        assert_eq!(tokenise("/ =".into()).unwrap(), ["/", "="]);

        assert_eq!(tokenise("=:=".into()).unwrap(), ["=:="]);
        assert_eq!(tokenise("=  : =".into()).unwrap(), ["=", ":", "="]);

        assert_eq!(tokenise("**".into()).unwrap(), ["**"]);
        assert_eq!(tokenise("* *".into()).unwrap(), ["*", "*",]);

        assert_eq!(tokenise("<=".into()).unwrap(), ["<="]);
        assert_eq!(tokenise("< =".into()).unwrap(), ["<", "=",]);

        assert_eq!(tokenise(">=".into()).unwrap(), [">="]);
        assert_eq!(tokenise("> =".into()).unwrap(), [">", "=",]);

        assert_eq!(tokenise("<=".into()).unwrap(), ["<="]);
        assert_eq!(tokenise("< =".into()).unwrap(), ["<", "=",]);
    }

    #[test]
    fn tokenise_multiple_clauses() {
        let text = " p(a,[b,c|[\t]]).
        p(X,Y):- Q(X,Y), {Q}.
        :- [\"file/name\"], test.
        "
        .to_string();

        assert_eq!(
            tokenise(text).unwrap(),
            [
                "p",
                "(",
                "a",
                ",",
                "[",
                "b",
                ",",
                "c",
                "|",
                "[]",
                "]",
                ")",
                ".",
                "\n",
                "p",
                "(",
                "X",
                ",",
                "Y",
                ")",
                ":-",
                "Q",
                "(",
                "X",
                ",",
                "Y",
                ")",
                ",",
                "{",
                "Q",
                "}",
                ".",
                "\n",
                ":-",
                "[",
                "\"file/name\"",
                "]",
                ",",
                "test",
                ".",
                "\n"
            ]
        );
    }
}

mod syntax_tree {
    use crate::program::clause;

    use super::super::{
        syntax_tree::{Clause, Term, TokenStream, Unit},
        tokeniser::tokenise,
    };
    #[test]
    fn parse_number_term() {
        //Positive Integer
        let text = tokenise("10".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(10)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(10)));

        //Negative Integer
        let text = tokenise("-10".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(-10)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Int(-10)));

        //Positive Float
        let text = tokenise("1.01".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(1.01)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(1.01)));

        //Negative Float
        let text = tokenise("-1.01".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(-1.01)));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Float(-1.01)));
    }

    #[test]
    fn parse_constant_term() {
        let text = tokenise("constant".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant".into())));

        let text = tokenise("constant_1".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant_1".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("constant_1".into())));

        let text = tokenise("'file/path'".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("file/path".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("file/path".into())));

        let text = tokenise("'c*o/n\"s-t'".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("c*o/n\"s-t".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Constant("c*o/n\"s-t".into())));
    }

    #[test]
    fn parse_variable_term() {
        let text = tokenise("Var".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("Var".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("Var".into())));

        let text = tokenise("VAR_Under".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under".into())));

        let text = tokenise("VAR10".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR10".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR10".into())));

        let text = tokenise("VAR_Under2".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under2".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::Variable("VAR_Under2".into())));
    }

    #[test]
    fn parse_string_term() {
        let text = tokenise("\"A String\"".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A String\"".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A String\"".into())));

        let text = tokenise("\"A \\\"String\"".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A \"String\"".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A \"String\"".into())));

        let text = tokenise("\"A *+-=: String\"".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A *+-=: String\"".into())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Unit(Unit::String("\"A *+-=: String\"".into())));
    }

    #[test]
    fn parse_atom_term() {
        let p = Unit::Constant("p".into());
        let q = Unit::Variable("Q".into());
        let x = Unit::Variable("X".into());
        let y = Unit::Variable("Y".into());
        let a = Unit::Constant("a".into());
        let b = Unit::Constant("b".into());

        let text = tokenise("p(X,a)".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                p.clone(),
                vec![Term::Unit(x.clone()), Term::Unit(a.clone())]
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                p.clone(),
                vec![Term::Unit(x.clone()), Term::Unit(a.clone())]
            )
        );

        let text = tokenise("Q(b,Y)".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                q.clone(),
                vec![Term::Unit(b.clone()), Term::Unit(y.clone())]
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                q.clone(),
                vec![Term::Unit(b.clone()), Term::Unit(y.clone())]
            )
        );
    }

    #[test]
    fn parse_list_term() {
        let a = Term::Unit(Unit::Constant("a".into()));
        let b = Term::Unit(Unit::Constant("b".into()));
        let c = Term::Unit(Unit::Constant("c".into()));
        let t = Term::Unit(Unit::Variable("T".into()));
        let p = Unit::Constant("p".into());

        let text = tokenise("[a,b,c]".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );

        let text = tokenise("[a,b,c|[]]".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::List(
                vec![a.clone(), b.clone(), c.clone()],
                Box::new(Term::EmptyList)
            )
        );

        let text = tokenise("[a|T]".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::List(vec![a.clone()], Box::new(t.clone())));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::List(vec![a.clone()], Box::new(t.clone())));

        let text = tokenise("[a,[b,c]]".into()).unwrap();
        let sub_list = Term::List(vec![b.clone(), c.clone()], Box::new(Term::EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList))
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList))
        );

        let text = tokenise("p([a,[b,c|T]])".into()).unwrap();
        let sub_list = Term::List(vec![b.clone(), c.clone()], Box::new(t.clone()));
        let list = Term::List(vec![a.clone(), sub_list.clone()], Box::new(Term::EmptyList));
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![list.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![list]));

        let text = tokenise("[]".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::EmptyList);
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::EmptyList);
    }

    #[test]
    fn parse_set_term() {
        let a = Term::Unit(Unit::Constant("a".into()));
        let b = Term::Unit(Unit::Constant("b".into()));
        let c = Term::Unit(Unit::Constant("c".into()));
        let p = Unit::Constant("p".into());

        let abc = Term::Set(vec![a.clone(), b.clone(), c.clone()]);

        let text = tokenise("{a,b,c}".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, abc.clone());
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("p({a,b,c})".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![abc.clone()]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Atom(p.clone(), vec![abc.clone()]));

        let text = tokenise("{a,{b,c}}".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(
            term,
            Term::Set(vec![a.clone(), Term::Set(vec![b.clone(), c.clone()])])
        );
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Set(vec![a.clone(), Term::Set(vec![b.clone(), c.clone()])])
        );

        let text = tokenise("{a,{}}".into()).unwrap();
        let term = TokenStream::new(text.clone()).parse_term().unwrap();
        assert_eq!(term, Term::Set(vec![a.clone(), Term::Set(vec![])]));
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Set(vec![a.clone(), Term::Set(vec![])]));
    }

    #[test]
    fn parse_tuple() {
        let a = Term::Unit(Unit::Constant("a".into()));
        let b = Term::Unit(Unit::Constant("b".into()));
        let c = Term::Unit(Unit::Constant("c".into()));
        let p = Unit::Constant("p".into());

        let abc = Term::Tuple(vec![a.clone(), b.clone(), c.clone()]);
        let bc = Term::Tuple(vec![b.clone(), c.clone()]);

        let text = tokenise("(a,b,c)".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, abc.clone());

        let text = tokenise("(a,(b,c))".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Tuple(vec![a.clone(), bc.clone()]));

        //This test fails
        let text = tokenise("(a,())".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Tuple(vec![a.clone(), Term::Tuple(vec![])]));

        let text = tokenise("p((a,b,c))".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(term, Term::Atom(p, vec![abc.clone()]));
    }

    //TODO Improve Error messaging for unclosed structures
    #[test]
    fn unclosed_atom() {
        let mut tokens = TokenStream::new(tokenise("p(X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,(Y)".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("p(X,(Y).".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn unclosed_list() {
        let mut tokens = TokenStream::new(tokenise("[X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("[X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("[X,[Y]".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("[X,[Y].".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn unclosed_set() {
        let mut tokens = TokenStream::new(tokenise("{X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("{X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("{X,{Y}".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("{X,{Y}.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn unclosed_tuple() {
        let mut tokens = TokenStream::new(tokenise("(X,Y".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("(X,Y.".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }

        let mut tokens = TokenStream::new(tokenise("(X,(Y)".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected End of File"),
        }

        let mut tokens = TokenStream::new(tokenise("(X,(Y).".into()).unwrap());
        match tokens.parse_expression() {
            Ok(_) => panic!("Should have thrown error"),
            Err(message) => assert_eq!(message, "Unexpected token in arguments: ."),
        }
    }

    #[test]
    fn infix_order() {
        let x = Term::Unit(Unit::Variable("X".into()));
        let y = Term::Unit(Unit::Variable("Y".into()));
        let one = Term::Unit(Unit::Int(1));
        let two = Term::Unit(Unit::Int(2));
        let three = Term::Unit(Unit::Int(3));
        let one_and_half = Term::Unit(Unit::Float(1.5));
        let plus = Unit::Constant("+".into());
        let minus = Unit::Constant("-".into());
        let divide = Unit::Constant("/".into());
        let times = Unit::Constant("*".into());
        let power = Unit::Constant("**".into());
        let eqauls = Unit::Constant("=:=".into());

        let text = tokenise("X =:= 1 + 2 / 1.5**3".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();
        assert_eq!(
            term,
            Term::Atom(
                eqauls,
                vec![
                    x.clone(),
                    Term::Atom(
                        plus.clone(),
                        vec![
                            one.clone(),
                            Term::Atom(
                                divide.clone(),
                                vec![
                                    two.clone(),
                                    Term::Atom(
                                        power.clone(),
                                        vec![one_and_half.clone(), three.clone()]
                                    )
                                ]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn grouped_expression() {
        let x = Term::Unit(Unit::Variable("X".into()));
        let y = Term::Unit(Unit::Variable("Y".into()));
        let one = Term::Unit(Unit::Int(1));
        let two = Term::Unit(Unit::Int(2));
        let three = Term::Unit(Unit::Int(3));
        let one_and_half = Term::Unit(Unit::Float(1.5));
        let plus = Unit::Constant("+".into());
        let minus = Unit::Constant("-".into());
        let divide = Unit::Constant("/".into());
        let times = Unit::Constant("*".into());
        let power = Unit::Constant("**".into());
        let equals = Unit::Constant("=:=".into());

        let text = tokenise("X =:= 1 + (2 / 1.5)**3".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Term::Atom(
                equals,
                vec![
                    x,
                    Term::Atom(
                        plus,
                        vec![
                            one,
                            Term::Atom(
                                power,
                                vec![Term::Atom(divide, vec![two, one_and_half]), three]
                            )
                        ]
                    )
                ]
            )
        );
    }

    #[test]
    fn tuple_or_grouped_expression() {
        let x = Term::Unit(Unit::Variable("X".into()));
        let y = Term::Unit(Unit::Variable("Y".into()));
        let a = Term::Unit(Unit::Constant("a".into()));
        let one = Term::Unit(Unit::Int(1));
        let two = Term::Unit(Unit::Int(2));
        let three = Term::Unit(Unit::Int(3));
        let one_and_half = Term::Unit(Unit::Float(1.5));
        let plus = Unit::Constant("+".into());
        let minus = Unit::Constant("-".into());
        let divide = Unit::Constant("/".into());
        let times = Unit::Constant("*".into());
        let power = Unit::Constant("**".into());
        let equals = Unit::Constant("=:=".into());

        let text = tokenise("(a,X =:= 1 + (2 / 1.5)**(3,Y))".into()).unwrap();
        let term = TokenStream::new(text).parse_expression().unwrap();

        assert_eq!(
            term,
            Term::Tuple(vec![
                a,
                Term::Atom(
                    equals,
                    vec![
                        x,
                        Term::Atom(
                            plus,
                            vec![
                                one,
                                Term::Atom(
                                    power,
                                    vec![
                                        Term::Atom(divide, vec![two, one_and_half]),
                                        Term::Tuple(vec![three, y])
                                    ]
                                )
                            ]
                        )
                    ]
                )
            ])
        );
    }

    #[test]
    fn parse_rule() {
        let mut token_stream = TokenStream::new(tokenise("gt1(X):-X>1.".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Atom(
            Unit::Constant("gt1".into()),
            vec![Term::Unit(Unit::Variable("X".into()))],
        );
        let body = Term::Atom(
            Unit::Constant(">".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Int(1)),
            ],
        );

        assert_eq!(clause, Clause::Rule(head, vec![body]));
        // assert_eq!(token_stream.parse_clause().unwrap(),None);
    }

    #[test]
    fn parse_fact() {
        let mut token_stream = TokenStream::new(tokenise("man(plato).".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Atom(
            Unit::Constant("man".into()),
            vec![Term::Unit(Unit::Constant("plato".into()))],
        );

        assert_eq!(clause, Clause::Fact(head));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_meta_rule() {
        let mut token_stream = TokenStream::new(tokenise("P(X,Y):-Q(X,Y),{P,Q}.".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let head = Term::Atom(
            Unit::Variable("P".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let body = Term::Atom(
            Unit::Variable("Q".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let meta_data = Term::Set(vec![
            Term::Unit(Unit::Variable("P".into())),
            Term::Unit(Unit::Variable("Q".into())),
        ]);

        assert_eq!(clause, Clause::MetaRule(head, vec![body, meta_data]));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_directive() {
        let mut token_stream =
            TokenStream::new(tokenise(":-test(a),['file/path'].".into()).unwrap());
        let clause = token_stream.parse_clause().unwrap().unwrap();
        let body = Term::Atom(
            Unit::Constant("test".into()),
            vec![Term::Unit(Unit::Constant("a".into()))],
        );
        let body2 = Term::List(
            vec![Term::Unit(Unit::Constant("file/path".into()))],
            Box::new(Term::EmptyList),
        );

        assert_eq!(clause, Clause::Directive(vec![body, body2]));
        assert_eq!(token_stream.parse_clause().unwrap(), None);
    }

    #[test]
    fn parse_all_clauses(){
        let text = "gt1(X):-X>1.\nman(plato).\nP(X,Y):-\n\tQ(X,Y),\n\t{P,Q}.\n:-test(a),['file/path'].".to_string();
        let mut token_stream = TokenStream::new(tokenise(text).unwrap());
        let mut clauses = token_stream.parse_all().unwrap();

        let head = Term::Atom(
            Unit::Constant("gt1".into()),
            vec![Term::Unit(Unit::Variable("X".into()))],
        );
        let body = Term::Atom(
            Unit::Constant(">".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Int(1)),
            ],
        );
        assert_eq!(clauses[0], Clause::Rule(head, vec![body]));


        let head = Term::Atom(
            Unit::Constant("man".into()),
            vec![Term::Unit(Unit::Constant("plato".into()))],
        );
        assert_eq!(clauses[1], Clause::Fact(head));


        let head = Term::Atom(
            Unit::Variable("P".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let body = Term::Atom(
            Unit::Variable("Q".into()),
            vec![
                Term::Unit(Unit::Variable("X".into())),
                Term::Unit(Unit::Variable("Y".into())),
            ],
        );
        let meta_data = Term::Set(vec![
            Term::Unit(Unit::Variable("P".into())),
            Term::Unit(Unit::Variable("Q".into())),
        ]);
        assert_eq!(clauses[2], Clause::MetaRule(head, vec![body, meta_data]));


        let body = Term::Atom(
            Unit::Constant("test".into()),
            vec![Term::Unit(Unit::Constant("a".into()))],
        );
        let body2 = Term::List(
            vec![Term::Unit(Unit::Constant("file/path".into()))],
            Box::new(Term::EmptyList),
        );
        assert_eq!(clauses[3], Clause::Directive(vec![body, body2]));
    }
}
