//TO DO 
// aq to eq function
// Term string value to be pointers to heap attribute of all strings

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Term {
    Number(f64),
    Constant(Box<str>),
    REF(usize),      //Query Variable
    EQVar(Box<str>), //Existentialy Quantified Variable
    AQVar(Box<str>), //Universally Quantified Variable
}

impl Term {
    pub fn to_string(&self) -> String {
        match self {
            Term::Constant(symbol) => symbol.to_string(),
            Term::EQVar(symbol) => symbol.to_string(),
            Term::REF(id) => "_".to_string() + &id.to_string(),
            Term::AQVar(symbol) => "∀'".to_string() + &symbol.to_string(),
            Term::Number(value) => value.to_string(),
        }
    }
    pub fn unify<'a>(&'a self, other: &'a Term) -> Option<(&'a Term, &'a Term)> {
        if self == other{ return Some((self, other));}
        if let &Term::Constant(value1) = &self {
            if let &Term::Constant(value2) = &other {
                if value1 != value2 {
                    return None;
                }
            }
        }
        let order1 = self.order();
        let order2 = other.order();
        if order1 == 0 && order2 == 0{
            return None;
        }
        match order1 > order2 {
            true => Some((self, other)),
            false => Some((other, self)),
        }
    }

    pub fn enum_type(&self) -> &str {
        match self {
            Term::Constant(_) => "Constant",
            Term::REF(_) => "Ref",
            Term::EQVar(_) => "EQVar",
            Term::AQVar(_) => "AQVar",
            Term::Number(_) => "Num",
        }
    }

    pub fn order(&self) -> usize{
        match self {
            Term::Number(_) => 0,
            Term::Constant(_) => 0,
            Term::REF(_) => 1,
            Term::EQVar(_) => 2,
            Term::AQVar(_) => 3,
            
        }
    }
}
