use self::VarBind::{Addr, Var};

const VAR_MASK: usize = 1 << (usize::BITS - 1);
const UNBOUND_VALUE: usize = usize::MAX;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VarBind {
    Var(usize),
    Addr(usize),
}
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VarReg(pub(super) usize);

impl Default for VarReg {
    fn default() -> Self {
        Self(UNBOUND_VALUE)
    }
}

impl VarReg {
    pub const UNBOUND: Self = Self(UNBOUND_VALUE);

    pub fn bound(&self) -> bool {
        self.0 != UNBOUND_VALUE
    }
    pub fn var(&self) -> bool {
        self.bound() && self.0 & VAR_MASK != 0
    }
    pub fn addr(&self) -> bool {
        self.bound() && self.0 & VAR_MASK == 0
    }
    // pub fn bind_type(&self) -> Option<VarBind> {
    //     if self.bound() {
    //         if self.0 & VAR_MASK == 0 {
    //             Some(Addr)
    //         } else {
    //             Some(Var)
    //         }
    //     } else {
    //         None
    //     }
    // }
    pub fn value(&self) -> usize {
        self.0 & !VAR_MASK
    }
    pub fn get_bind(&self) -> Option<VarBind> {
        if *self != Self::UNBOUND {
            if self.addr() {
                Some(Addr(self.0))
            } else {
                Some(Var(self.value()))
            }
        } else {
            None
        }
    }
    pub fn bind(&mut self, binding: VarBind) {
        debug_assert!(*self == Self::UNBOUND, "Should not overwrite existing binding");
        *self = binding.into();
    }

    pub fn unbind(&mut self) {
        debug_assert!(self.bound(), "Can't unbind unbound");
        self.0 = UNBOUND_VALUE
    }
}

impl From<VarBind> for VarReg {
    fn from(binding: VarBind) -> Self {
        match binding {
            Var(value) => Self(value | VAR_MASK),
            Addr(value) => Self(value),
        }
    }
}

impl TryInto<VarBind> for VarReg {
    type Error = ();

    fn try_into(self) -> Result<VarBind, Self::Error> {
        if self != Self::UNBOUND {
            if self.var() {
                Ok(Var(self.value()))
            } else {
                Ok(Addr(self.0))
            }
        } else {
            Err(())
        }
    }
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use crate::heap::{
        varbind::VAR_MASK,
        VarBind::{self, Addr, Var},
    };

    use super::{VarReg, UNBOUND_VALUE};

    #[test]
    fn bound() {
        let var_reg = VarReg(UNBOUND_VALUE);
        assert!(!var_reg.bound());
        let var_reg = VarReg(0 | VAR_MASK);
        assert!(var_reg.bound());
        let var_reg = VarReg(0);
        assert!(var_reg.bound());
    }

    #[test]
    fn addr() {
        let var_reg = VarReg(UNBOUND_VALUE);
        assert!(!var_reg.addr());
        let var_reg = VarReg(10 | VAR_MASK);
        assert!(!var_reg.addr());
        let var_reg = VarReg(10);
        assert!(var_reg.addr());
    }

    #[test]
    fn var() {
        let var_reg = VarReg(UNBOUND_VALUE);
        assert!(!var_reg.var());
        let var_reg = VarReg(10 | VAR_MASK);
        assert!(var_reg.var());
        let var_reg = VarReg(10);
        assert!(!var_reg.var());
    }

    #[test]
    fn from_var_bind() {
        let var_reg: VarReg = Var(5).into();
        assert_eq!(var_reg.0, 5 | VAR_MASK);
        assert!(var_reg.bound());
        assert!(var_reg.var());

        let var_reg: VarReg = Addr(5).into();
        assert_eq!(var_reg.0, 5);
        assert!(var_reg.bound());
        assert!(var_reg.addr());
    }

    #[test]
    fn bind(){
        let mut var_reg = VarReg::UNBOUND;
        var_reg.bind(Var(0));
        assert_eq!(var_reg.0,0|VAR_MASK);
        assert!(var_reg.bound());
        assert!(var_reg.var());
        assert!(!var_reg.addr());
        assert_eq!(var_reg.get_bind(),Some(Var(0)));

        let mut var_reg = VarReg::UNBOUND;
        var_reg.bind(Var(5));
        assert_eq!(var_reg.0,5|VAR_MASK);
        assert!(var_reg.bound());
        assert!(var_reg.var());
        assert!(!var_reg.addr());
        assert_eq!(var_reg.get_bind(),Some(Var(5)));

        let mut var_reg = VarReg::UNBOUND;
        var_reg.bind(Addr(0));
        assert_eq!(var_reg.0,0);
        assert!(var_reg.bound());
        assert!(!var_reg.var());
        assert!(var_reg.addr());
        assert_eq!(var_reg.get_bind(),Some(Addr(0)));

        let mut var_reg = VarReg::UNBOUND;
        var_reg.bind(Addr(5));
        assert_eq!(var_reg.0,5);
        assert!(var_reg.bound());
        assert!(!var_reg.var());
        assert!(var_reg.addr());
        assert_eq!(var_reg.get_bind(),Some(Addr(5)));
    }

    #[test]
    #[should_panic]
    fn bind_already_bound_addr(){
        let mut var_reg = VarReg(10);
        var_reg.bind(Var(10));
    }

    #[test]
    #[should_panic]
    fn bind_already_bound_var(){
        let mut var_reg = VarReg(10 | VAR_MASK);
        var_reg.bind(Addr(10));
    }

    #[test]
    fn get_bind() {
        let var_reg = VarReg(5);
        assert_eq!(var_reg.get_bind(), Some(Addr(5)));
        let res: Result<VarBind, ()> = var_reg.try_into();
        assert_eq!(res, Ok(Addr(5)));

        let var_reg = VarReg(5 | VAR_MASK);
        assert_eq!(var_reg.get_bind(), Some(Var(5)));
        let res: Result<VarBind, ()> = var_reg.try_into();
        assert_eq!(res, Ok(Var(5)));

        let var_reg = VarReg::UNBOUND;
        assert_eq!(var_reg.get_bind(), None);
        let res: Result<VarBind, ()> = var_reg.try_into();
        assert_eq!(res, Err(()));
    }
}
