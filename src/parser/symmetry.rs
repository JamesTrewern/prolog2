//! Finds the symmetries of a meta rule: the reorderings of its body
//! literals that give the same clause. Works on the parsed terms, before
//! anything is compiled.

use super::term::Term::{self, *};

/// A meta rule as parsed: head then body, with its declared meta variables.
pub(crate) struct Rule<'a> {
    pub literals: &'a [Term],
    pub meta_vars: &'a [String],
    pub namespaced: &'a [(String, String)],
}

impl Rule<'_> {
    /// What a variable is declared as: meta or not, and its namespace. A
    /// renaming only pairs variables of the same kind. Whether a meta
    /// variable is constrained is left out, as that only matters during the
    /// proof.
    fn kind(&self, var: &str) -> (bool, Option<&str>) {
        (
            self.meta_vars.iter().any(|v| v == var),
            self.namespaced
                .iter()
                .find(|(v, _)| v == var)
                .map(|(_, namespace)| namespace.as_str()),
        )
    }

    /// The meta variables in slot order: the order `build_clause` numbers
    /// them in, which is the order of a `MetaSub`'s bindings.
    pub(super) fn slots(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for literal in self.literals {
            literal.extract_vars(&mut vars);
        }
        vars.retain(|var| self.meta_vars.contains(var));
        vars
    }
}

struct Search<'a> {
    rule: &'a Rule<'a>,
    /// Each variable met so far with the variable it becomes.
    renaming: Vec<(&'a str, &'a str)>,
    /// The body literals already taken as the image of an earlier one.
    taken: Vec<usize>,
    /// The renaming of every reordering found.
    found: Vec<Vec<(&'a str, &'a str)>>,
}

impl<'a> Search<'a> {
    /// Pair `x` with `y`, keeping the renaming one to one.
    fn bind(&mut self, x: &'a str, y: &'a str) -> bool {
        for &(from, to) in &self.renaming {
            if from == x || to == y {
                return from == x && to == y;
            }
        }
        if self.rule.kind(x) != self.rule.kind(y) {
            return false;
        }
        self.renaming.push((x, y));
        true
    }

    /// Extend the renaming so that `x` becomes `y`. On failure the renaming
    /// is left part extended, for the caller to cut back.
    fn rename(&mut self, x: &'a Term, y: &'a Term) -> bool {
        match (x, y) {
            (Variable(x), Variable(y)) => self.bind(x, y),
            (Str(kind_x, xs), Str(kind_y, ys)) => kind_x == kind_y && self.rename_all(xs, ys),
            (List(xs, x_tail), List(ys, y_tail)) => {
                self.rename_all(xs, ys) && self.rename(x_tail, y_tail)
            }
            _ => x == y,
        }
    }

    fn rename_all(&mut self, xs: &'a [Term], ys: &'a [Term]) -> bool {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.rename(x, y))
    }

    /// Place body literal `i`, and those after it, on body literals not yet
    /// taken.
    fn place(&mut self, i: usize) {
        let body = &self.rule.literals[1..];
        if i == body.len() {
            self.found.push(self.renaming.clone());
            return;
        }
        for j in 0..body.len() {
            if self.taken.contains(&j) {
                continue;
            }
            let checkpoint = self.renaming.len();
            if self.rename(&body[i], &body[j]) {
                self.taken.push(j);
                self.place(i + 1);
                self.taken.pop();
            }
            self.renaming.truncate(checkpoint);
        }
    }
}

/// The symmetries of a meta rule: each reordering of its body that gives
/// the same clause, as a permutation of the meta variable slots.
///
/// For a permutation `p`, bindings `subs` and the bindings `permuted` with
/// `permuted[i] = subs[p[i]]` give the same clause. The identity is left
/// out.
///
/// A reordering counts when the variables can be renamed one to one, each
/// onto a variable of the same kind, so that every body literal becomes the
/// one in its new place. Head variables keep their names.
pub(crate) fn symmetries(rule: &Rule) -> Vec<Vec<u8>> {
    let mut search = Search {
        rule,
        renaming: Vec::new(),
        taken: Vec::new(),
        found: Vec::new(),
    };
    // Renaming the head onto itself fixes its variables.
    let head = &rule.literals[0];
    if search.rename(head, head) {
        search.place(0);
    }

    let slots = rule.slots();
    let mut permutations: Vec<Vec<u8>> = Vec::new();
    for renaming in search.found {
        let permutation: Vec<u8> = slots
            .iter()
            .map(|slot| {
                // A meta variable the renaming never met stays where it is.
                let target = renaming
                    .iter()
                    .find(|(from, _)| from == slot)
                    .map_or(slot.as_str(), |(_, to)| to);
                slots.iter().position(|slot| slot == target).unwrap() as u8
            })
            .collect();
        let identity = permutation
            .iter()
            .enumerate()
            .all(|(i, &p)| i == p as usize);
        if !identity && !permutations.contains(&permutation) {
            permutations.push(permutation);
        }
    }
    permutations
}

#[cfg(test)]
mod tests {
    use super::{symmetries, Rule};
    use crate::parser::{
        build_tree::TreeClause,
        execute_tree::{extract_meta_rule_vars, strip_namespaces},
        term::Term,
        tokenise, TokenStream,
    };

    struct Parsed {
        literals: Vec<Term>,
        meta_vars: Vec<String>,
        namespaced: Vec<(String, String)>,
    }

    impl Parsed {
        fn rule(&self) -> Rule<'_> {
            Rule {
                literals: &self.literals,
                meta_vars: &self.meta_vars,
                namespaced: &self.namespaced,
            }
        }
    }

    fn parse(code: &str) -> Parsed {
        let clause = TokenStream::new(tokenise(code).unwrap())
            .parse_clause()
            .unwrap()
            .unwrap();
        let TreeClause::MetaRule(mut literals) = clause else {
            panic!("`{code}` is not a meta rule");
        };
        let mut namespaced = Vec::new();
        for declaration in literals.iter_mut().rev().take(2) {
            namespaced.append(&mut strip_namespaces(declaration));
        }
        let (meta_vars, _) = extract_meta_rule_vars(&mut literals).unwrap();
        Parsed {
            literals,
            meta_vars,
            namespaced,
        }
    }

    fn symmetries_of(code: &str) -> Vec<Vec<u8>> {
        symmetries(&parse(code).rule())
    }

    #[test]
    fn identity_and_chain_have_none() {
        assert!(symmetries_of("P(X,Y):-Q(X,Y),{P,Q}.").is_empty());
        assert!(symmetries_of("P(X,Y):-Q(X,Z),R(Z,Y),{P,Q,R}.").is_empty());
    }

    /// The literals unify, but only by merging head variables.
    #[test]
    fn head_variables_stay_put() {
        assert!(symmetries_of("P(X,Y):-Q(X),R(Y),{P,Q,R}.").is_empty());
    }

    /// `Q(X,Z)` and `R(Z,X)` unify by binding `Z` to `X`, which is not a
    /// renaming.
    #[test]
    fn variables_are_renamed_not_merged() {
        assert!(symmetries_of("P(X):-Q(X,Z),R(Z,X),{P,Q,R}.").is_empty());
    }

    #[test]
    fn two_literals_alike_swap() {
        // Slots: P, Q, R.
        assert_eq!(symmetries_of("P(X):-Q(X),R(X),{P,Q,R}."), [[0, 2, 1]]);
    }

    #[test]
    fn the_swap_carries_the_constants_with_it() {
        // Slots: P, C, A, D, B, Q.
        assert_eq!(
            symmetries_of("P(X,Y,Z):-C(Z,A),D(Z,B),Q(X,Y),{P,Q,C,D,A,B}."),
            [[0, 3, 4, 1, 2, 5]]
        );
    }

    /// `Q` swaps with `R` only if `S` swaps with `T` too.
    #[test]
    fn a_joint_swap_is_one_symmetry() {
        // Slots: P, Q, R, S, T.
        assert_eq!(
            symmetries_of("P(X):-Q(X,A),R(X,B),S(A),T(B),{P,Q,R,S,T}."),
            [[0, 2, 1, 4, 3]]
        );
    }

    #[test]
    fn three_literals_alike_give_every_reordering() {
        assert_eq!(symmetries_of("P(X):-Q(X),R(X),S(X),{P,Q,R,S}.").len(), 5);
    }

    #[test]
    fn a_constant_predicate_breaks_the_symmetry() {
        assert!(symmetries_of("P(X):-q(X),R(X),{P,R}.").is_empty());
    }

    /// Being constrained matters to the proof, not to whether two sets of
    /// bindings give the same clause.
    #[test]
    fn constrained_and_unconstrained_variables_swap() {
        assert_eq!(symmetries_of("P(X):-Q(X),R(X),{P,Q},[R]."), [[0, 2, 1]]);
    }

    #[test]
    fn a_namespaced_variable_swaps_only_within_its_namespace() {
        assert!(symmetries_of("P(X):-Q(X),R(X),{P,Q:cmp,R}.").is_empty());
        assert_eq!(
            symmetries_of("P(X):-Q(X),R(X),{P,Q:cmp,R:cmp}."),
            [[0, 2, 1]]
        );
    }

    /// A meta variable never swaps with a first order one.
    #[test]
    fn meta_and_first_order_variables_do_not_swap() {
        assert!(symmetries_of("P(X):-q(X,A),q(X,B),{P,A}.").is_empty());
    }
}
