use super::tokeniser::tokenise;



#[test]
fn tokenise_decimal_number(){
    let res = tokenise("123 . 123.123.123");
    assert_eq!(res,["123",".","123.123",".","123"]);
}

#[test]
fn tokenise_clause_fact_and_directive(){
    let res = tokenise("p(X,Y):- q(X,Y).\nq(a,b).\n:-p(a,b).");
    assert_eq!(res,["p","(","X",",","Y",")",":-","q","(","X",",","Y",")",".","\n","q","(","a",",","b",")",".","\n",":-","p","(","a",",","b",")","."])
}

#[test]
fn tokenise_fact_with_list(){
    let res = tokenise("p([a,b,c]).");
    assert_eq!(res,["p","(","[","a",",","b",",","c","]",")","."]);
}

#[test]
fn tokenise_fact_with_list_with_explicit_tail(){
    let res = tokenise("p([a,b,c|T]).");
    assert_eq!(res,["p","(","[","a",",","b",",","c","|","T","]",")","."]);
}

#[test]
fn tokenise_fact_with_empty_list_1(){
    let res = tokenise("p(a,[]).");
    assert_eq!(res,["p","(","a",",","[]",")","."]);
}

#[test]
fn tokenise_fact_with_empty_list_2(){
    let res = tokenise("p(a,[ ]).");
    assert_eq!(res,["p","(","a",",","[]",")","."]);
}

#[test]
fn tokenise_fact_with_empty_list_3(){
    let res = tokenise("p(a,[ \n\t]).");
    assert_eq!(res,["p","(","a",",","[]",")","."]);
}

#[test]
fn tokenise_known_symbols(){
    assert_eq!(tokenise(": -"), [":","-"]);
    assert_eq!(tokenise(":-"), [":-"]);
    assert_eq!(tokenise("= : ="), ["=", ":", "="]);
    assert_eq!(tokenise("=:="), ["=:="]);
}