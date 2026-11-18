//! Why a positive example cannot be entailed within the negative noise
//! threshold.
//!
//! For a run that [noise handling](super::noise) finds it cannot rescue:
//! some positive is entailed by no sub hypothesis that entails no negative,
//! though sub hypotheses entailing negatives do entail it, and removing the
//! examples at fault would take more than the noise bounds allow.
//! [`report_positive`] gives, for such a positive, the negatives that come
//! with it, and example hypotheses from several angles:
//!
//! - what sets its covers apart: [`Lone`] covers, entailing it and as few
//!   other positives as possible, preferring ones with a literal nothing
//!   else has;
//! - what they have in common with the rest: a [`Pair`] of a cover and a
//!   hypothesis entailing no negative and, as nearly as any does, the same
//!   positives without it; preferring pairs that share literals;
//! - which invented predicates its covers have to themselves, lack, or
//!   share with the hypotheses entailing no negative: [`Definitions`];
//! - what entailing it costs a whole program: [`Greedy`] covers of the
//!   other positives, without it and with it;
//! - conclusions drawn from those, with the literals on either side of
//!   the [`Boundary`] between its covers and the clean hypotheses.
//!
//! Throughout, the hypotheses a positive's covers are set against are
//! those within the bound, called clean here: with a bound of none, the
//! hypotheses entailing no negative.
//!
//! The [`NoiseReport`] renders as plain text for the terminal and as
//! Markdown for a file.

use std::{
    cmp::Reverse,
    collections::{hash_map::Entry, HashMap, HashSet},
    sync::atomic::{AtomicU32, Ordering},
};

use rayon::prelude::*;
use smallvec::SmallVec;

use super::{
    coverage::{covered_by, ExampleSet, HProfile, Profiled},
    noise::Conflict,
    utils::SearchCtx,
};
use crate::{
    heap::{Heap, QueryHeap, Tag::Arg},
    program::HypothesisTrait,
    resolution::{build, Substitution},
};

/// Sub sections, of one example each, in the unique properties section and
/// in the similarity comparisons section of a positive's report.
const EXAMPLES: usize = 2;
/// Width of the lines ruled between the report's sections.
const RULE_WIDTH: usize = 80;
/// Predicates given in each sub section of the predicate definitions
/// section of a positive's report.
const PRED_EXAMPLES: usize = 2;
/// Literals given on each side of the boundary in the conclusions.
const BOUNDARY_LITERALS: usize = 3;
/// Covers tried against the clean hypotheses, per set of other positives.
const COVERS_PER_SET: usize = 4;

/// A hypothesis proving a noisy positive, picked to show what sets its
/// covers apart.
#[derive(Debug)]
pub(super) struct Lone<B> {
    pub(super) h: u32,
    pub(super) coverage: B,
    pub(super) neg_coverage: B,
    /// Its literals that no hypothesis not proving the positive has.
    pub(super) unique: Vec<String>,
}

/// A hypothesis proving a noisy positive, and the nearest there is to one
/// proving the same positives apart from it and no negative.
#[derive(Debug)]
pub(super) struct Pair<B> {
    pub(super) with: u32,
    /// The negatives `with` proves.
    pub(super) neg_coverage: B,
    /// The positives `with` proves besides the noisy one.
    pub(super) others: B,
    pub(super) without: u32,
    /// The positives `without` proves: `others` when there is such a
    /// hypothesis, else as near to it as any comes.
    pub(super) without_coverage: B,
    /// The literals both have.
    pub(super) shared: Vec<String>,
    /// The literals only `with` has.
    pub(super) only_with: Vec<String>,
    /// The literals only `without` has.
    pub(super) only_without: Vec<String>,
}

/// A literal and how many hypotheses have it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct LiteralUse {
    pub(super) literal: String,
    /// Hypotheses proving the noisy positive that have it.
    pub(super) in_covers: u32,
    /// Hypotheses proving no negative that have it.
    pub(super) in_clean: u32,
}

/// The literals that most tell the hypotheses proving a noisy positive
/// from those proving no negative: those with the largest difference
/// between the share of one group having them and the share of the other.
#[derive(Debug)]
pub(super) struct Boundary {
    pub(super) n_covers: usize,
    pub(super) n_clean: usize,
    /// More usual among the covers, the most lopsided first.
    pub(super) noisy: Vec<LiteralUse>,
    /// More usual among the clean hypotheses, the most lopsided first.
    pub(super) clean: Vec<LiteralUse>,
}

impl Boundary {
    /// Pick the literals from how many covers and how many clean
    /// hypotheses have each.
    pub(super) fn rank(
        in_covers: &HashMap<String, u32>,
        in_clean: &HashMap<String, u32>,
        n_covers: usize,
        n_clean: usize,
    ) -> Self {
        let share = |count: u32, of: usize| match of {
            0 => 0.0,
            of => count as f64 / of as f64,
        };
        // How much more of the covers have it than of the clean.
        let mut leans: Vec<(f64, LiteralUse)> = in_covers
            .keys()
            .chain(in_clean.keys().filter(|l| !in_covers.contains_key(*l)))
            .map(|literal| {
                let literal_use = LiteralUse {
                    literal: literal.clone(),
                    in_covers: in_covers.get(literal).copied().unwrap_or(0),
                    in_clean: in_clean.get(literal).copied().unwrap_or(0),
                };
                let lean =
                    share(literal_use.in_covers, n_covers) - share(literal_use.in_clean, n_clean);
                (lean, literal_use)
            })
            .collect();
        leans.sort_by(|(a, a_use), (b, b_use)| {
            b.total_cmp(a)
                .then_with(|| a_use.literal.cmp(&b_use.literal))
        });

        let noisy: Vec<&(f64, LiteralUse)> = leans.iter().filter(|(lean, _)| *lean > 0.0).collect();
        // The other side from the far end, equal leans still in name order.
        let mut clean: Vec<&(f64, LiteralUse)> =
            leans.iter().filter(|(lean, _)| *lean < 0.0).collect();
        clean.sort_by(|(a, _), (b, _)| a.total_cmp(b));
        let (noisy, clean) = (noisy.into_iter(), clean.into_iter());
        let take = |uses: &mut dyn Iterator<Item = &(f64, LiteralUse)>| -> Vec<LiteralUse> {
            uses.take(BOUNDARY_LITERALS)
                .map(|(_, literal_use)| literal_use.clone())
                .collect()
        };
        Self {
            n_covers,
            n_clean,
            noisy: take(&mut { noisy }),
            clean: take(&mut { clean }),
        }
    }
}

/// The example hypotheses for one noisy positive.
#[derive(Debug)]
pub(super) struct Examples<B = crate::learners::coverage::Coverage> {
    pub(super) lone: Vec<Lone<B>>,
    pub(super) pairs: Vec<Pair<B>>,
    pub(super) definitions: Definitions,
    pub(super) greedy: Greedy<B>,
    pub(super) boundary: Boundary,
    /// The other positives every hypothesis proving the noisy one proves.
    pub(super) always_with: B,
}

/// An invented predicate's definition and how many hypotheses call it,
/// directly or through another definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct DefUse {
    /// Index of the definition in the `PredDefTable`.
    pub(super) def: u32,
    /// Hypotheses proving the noisy positive that call it.
    pub(super) in_covers: u32,
    /// Hypotheses proving no negative that call it.
    pub(super) in_clean: u32,
}

/// The invented predicates that tell the hypotheses proving a noisy
/// positive from those proving no negative, and those that do not.
#[derive(Debug)]
pub(super) struct Definitions {
    /// How many hypotheses prove the noisy positive.
    pub(super) n_covers: usize,
    /// How many hypotheses prove no negative.
    pub(super) n_clean: usize,
    /// Called by covers and by the fewest clean hypotheses; most covers
    /// first among equals.
    pub(super) noisy: Vec<DefUse>,
    /// Called by clean hypotheses and by the fewest covers; most clean
    /// hypotheses first among equals.
    pub(super) clean: Vec<DefUse>,
    /// Called by the largest share of both, going by the smaller share.
    pub(super) common: Vec<DefUse>,
}

impl Definitions {
    /// Pick the definitions from how many covers and how many clean
    /// hypotheses call each, by definition index.
    pub(super) fn rank(
        in_covers: &[u32],
        in_clean: &[u32],
        n_covers: usize,
        n_clean: usize,
    ) -> Self {
        let uses = || {
            (0..in_covers.len()).map(|def| DefUse {
                def: def as u32,
                in_covers: in_covers[def],
                in_clean: in_clean[def],
            })
        };
        // Shares compared without dividing: a/n_covers against b/n_clean.
        let smaller_share = |d: &DefUse| {
            (d.in_covers as u128 * n_clean as u128).min(d.in_clean as u128 * n_covers as u128)
        };
        Self {
            n_covers,
            n_clean,
            noisy: least(uses().filter(|d| d.in_covers > 0), |d| {
                (d.in_clean, Reverse(d.in_covers))
            }),
            clean: least(uses().filter(|d| d.in_clean > 0), |d| {
                (d.in_covers, Reverse(d.in_clean))
            }),
            common: least(uses().filter(|d| d.in_covers > 0 && d.in_clean > 0), |d| {
                Reverse(smaller_share(d))
            }),
        }
    }
}

/// The [`PRED_EXAMPLES`] definitions with the least `key`, least first; the
/// earlier definition of two with the same key.
fn least<K: Ord>(uses: impl Iterator<Item = DefUse>, key: impl Fn(&DefUse) -> K) -> Vec<DefUse> {
    let mut least: Vec<(K, DefUse)> = Vec::with_capacity(PRED_EXAMPLES + 1);
    for def_use in uses {
        let key = key(&def_use);
        if least.len() == PRED_EXAMPLES && key >= least[PRED_EXAMPLES - 1].0 {
            continue;
        }
        let at = least.partition_point(|(other, _)| *other <= key);
        least.insert(at, (key, def_use));
        least.truncate(PRED_EXAMPLES);
    }
    least.into_iter().map(|(_, def_use)| def_use).collect()
}

/// Two greedy covers of the positives proved within the noise threshold:
/// one of just those, and one of those and a noisy positive, which may
/// also use the hypotheses over the threshold that prove the fewest
/// negatives alongside it ([`Conflict::smallest`]).
///
/// The negatives are those the sub hypotheses prove each on their own;
/// together they could prove more.
#[derive(Debug)]
pub(super) struct Greedy<B> {
    pub(super) without: Vec<u32>,
    pub(super) without_neg: B,
    pub(super) with: Vec<u32>,
    pub(super) with_neg: B,
}

impl<B: ExampleSet> Examples<B> {
    /// Pick the examples for `positive`, from the profiles within the
    /// noise threshold (`kept`) and over it (`rest`).
    pub(super) fn find(
        positive: &Conflict<B>,
        kept: &[HProfile<B>],
        rest: &[HProfile<B>],
        pos_goals: &[usize],
        ctx: SearchCtx,
    ) -> Self {
        let pos = positive.pos;
        // The examples' own predicates are in every hypothesis, so say
        // nothing about any one of them.
        let mut targets: Vec<usize> = pos_goals
            .iter()
            .map(|&goal| ctx.heap.symbol_arity(goal).0)
            .collect();
        targets.sort_unstable();
        targets.dedup();
        let targets = targets.as_slice();

        let covers: Vec<Cover<B>> = rest
            .par_iter()
            .filter(|h_profile| h_profile.coverage.get(pos))
            .map(|profile| Cover {
                profile,
                literals: literals(profile.h, targets, ctx),
                unique: Vec::new(),
            })
            .collect();
        let mut finder = Finder {
            pos,
            targets,
            covers,
            ctx,
        };
        let boundary = finder.mark_unique(kept, rest);
        let always_with = finder
            .covers
            .iter()
            .fold(B::full(pos_goals.len()), |all, cover| {
                all.intersection(&cover.profile.coverage)
            })
            .difference(&B::from_indices([pos]));
        Self {
            boundary,
            always_with,
            lone: finder.lone(),
            pairs: finder.pairs(kept),
            definitions: finder.definitions(kept),
            greedy: finder.greedy(positive, kept, rest),
        }
    }
}

/// A hypothesis proving the noisy positive.
struct Cover<'p, B> {
    profile: &'p HProfile<B>,
    /// Its literals, sorted.
    literals: Vec<String>,
    /// Those of them nothing but a cover has.
    unique: Vec<String>,
}

/// The search for one positive's [`Examples`].
struct Finder<'p, 'c, B> {
    pos: usize,
    targets: &'p [usize],
    covers: Vec<Cover<'p, B>>,
    ctx: SearchCtx<'c>,
}

impl<B: ExampleSet> Finder<'_, '_, B> {
    /// Fill in each cover's `unique` literals: those no hypothesis outside
    /// the covers has. The same pass over the hypotheses counts the
    /// literals of the clean ones, for the [`Boundary`].
    fn mark_unique(&mut self, kept: &[HProfile<B>], rest: &[HProfile<B>]) -> Boundary {
        let candidates: HashSet<&str> = self
            .covers
            .iter()
            .flat_map(|cover| cover.literals.iter().map(String::as_str))
            .collect();
        let (pos, targets, ctx) = (self.pos, self.targets, self.ctx);
        let neg_noise = ctx.parallel.neg_noise;

        type Seen = (HashSet<String>, HashMap<String, u32>, usize);
        let (elsewhere, in_clean, n_clean): Seen = kept
            .par_iter()
            .chain(rest.par_iter())
            .filter(|h_profile| !h_profile.coverage.get(pos))
            .fold(
                Seen::default,
                |(mut seen, mut in_clean, mut n_clean), h_profile| {
                    // Within the bound, as every one of `kept` is.
                    let is_clean = h_profile.neg_coverage.count() <= neg_noise;
                    n_clean += is_clean as usize;
                    for literal in literals(h_profile.h, targets, ctx) {
                        if is_clean {
                            *in_clean.entry(literal.clone()).or_default() += 1;
                        }
                        if candidates.contains(literal.as_str()) {
                            seen.insert(literal);
                        }
                    }
                    (seen, in_clean, n_clean)
                },
            )
            .reduce(Seen::default, |mut all, (seen, in_clean, n_clean)| {
                all.0.extend(seen);
                for (literal, count) in in_clean {
                    *all.1.entry(literal).or_default() += count;
                }
                all.2 += n_clean;
                all
            });

        let mut in_covers: HashMap<String, u32> = HashMap::new();
        for cover in &mut self.covers {
            for literal in &cover.literals {
                *in_covers.entry(literal.clone()).or_default() += 1;
            }
            cover.unique = cover
                .literals
                .iter()
                .filter(|literal| !elsewhere.contains(*literal))
                .cloned()
                .collect();
        }
        Boundary::rank(&in_covers, &in_clean, self.covers.len(), n_clean)
    }

    /// The covers that best show what is particular to them: first those
    /// with a unique literal, then those proving the fewest positives, then
    /// the fewest negatives, then the smallest.
    fn lone(&self) -> Vec<Lone<B>> {
        let mut order: Vec<&Cover<B>> = self.covers.iter().collect();
        order.sort_by_key(|cover| {
            let p = cover.profile;
            (
                cover.unique.is_empty(),
                p.coverage.count(),
                p.neg_coverage.count(),
                p.n_clauses,
                p.n_literals,
                p.h,
            )
        });

        // Each further example is the best one whose unique literals differ
        // from those already picked, while there is one.
        let mut picked: Vec<&Cover<B>> = Vec::new();
        while picked.len() < EXAMPLES.min(order.len()) {
            let fresh = |cover: &&&Cover<B>| picked.iter().all(|p| p.unique != cover.unique);
            let unpicked =
                |cover: &&&Cover<B>| picked.iter().all(|p| p.profile.h != cover.profile.h);
            let next = order.iter().find(|c| unpicked(c) && fresh(c));
            let next = next.or_else(|| order.iter().find(unpicked));
            picked.push(next.expect("fewer picked than there are covers"));
        }

        picked
            .into_iter()
            .map(|cover| Lone {
                h: cover.profile.h,
                coverage: cover.profile.coverage,
                neg_coverage: cover.profile.neg_coverage,
                unique: cover.unique.clone(),
            })
            .collect()
    }

    /// Pairs of a cover and the hypothesis nearest to proving the cover's
    /// other positives, of those proving no negative. Nearest is fewest of
    /// those positives missed, then fewest further ones proved, then most
    /// literals shared with the cover.
    ///
    /// A pair after the first is weighted towards differing from those
    /// already picked, in the positives its two hypotheses have in common
    /// and in the literals they share.
    fn pairs(&self, kept: &[HProfile<B>]) -> Vec<Pair<B>> {
        // The covers by the positives they prove besides this one, the
        // least noisy and smallest few of each.
        let mut by_others: HashMap<B, Vec<&Cover<B>>> = HashMap::new();
        for cover in &self.covers {
            let others = cover
                .profile
                .coverage
                .difference(&B::from_indices([self.pos]));
            if !others.is_empty() {
                by_others.entry(others).or_default().push(cover);
            }
        }
        for covers in by_others.values_mut() {
            covers.sort_by_key(|cover| {
                let p = cover.profile;
                (p.neg_coverage.count(), p.n_clauses, p.n_literals, p.h)
            });
            covers.truncate(COVERS_PER_SET);
        }

        // Per set of other positives, the nearest coverages any clean
        // hypothesis has; kept as clean coverage -> the sets it is nearest.
        let clean_sets: HashSet<B> = kept.iter().map(|p| p.coverage).collect();
        let distance =
            |others: B, set: B| (others.difference_count(&set), set.difference_count(&others));
        let mut nearest_to: HashMap<B, Vec<B>> = HashMap::new();
        for &others in by_others.keys() {
            // Missing every one of them is not near at all.
            let n_others = others.count();
            let near = |set: &&B| distance(others, **set).0 < n_others;
            let Some(nearest) = clean_sets
                .iter()
                .filter(near)
                .map(|&s| distance(others, s))
                .min()
            else {
                continue;
            };
            for &set in &clean_sets {
                if distance(others, set) == nearest {
                    nearest_to.entry(set).or_default().push(others);
                }
            }
        }

        // The candidates: per set and per list of shared literals, a cover
        // and the smallest clean hypothesis with a nearest coverage.
        let mut candidates: HashMap<(B, Vec<String>), (&Cover<B>, &HProfile<B>)> = HashMap::new();
        for without in kept {
            let Some(sets) = nearest_to.get(&without.coverage) else {
                continue;
            };
            let has = literals(without.h, self.targets, self.ctx);
            let size = |h_profile: &HProfile<B>| (h_profile.n_clauses, h_profile.n_literals);
            for others in sets {
                for &cover in &by_others[others] {
                    let shared = intersection(&cover.literals, &has);
                    match candidates.entry((*others, shared)) {
                        Entry::Vacant(entry) => {
                            entry.insert((cover, without));
                        }
                        Entry::Occupied(mut entry) => {
                            if size(without) < size(entry.get().1) {
                                entry.insert((cover, without));
                            }
                        }
                    }
                }
            }
        }

        struct Candidate<'c, 'p, B> {
            others: B,
            shared: Vec<String>,
            cover: &'c Cover<'p, B>,
            without: &'p HProfile<B>,
        }
        impl<B: ExampleSet> Candidate<'_, '_, B> {
            /// The positives the two hypotheses have in common.
            fn common(&self) -> B {
                self.others.intersection(&self.without.coverage)
            }
        }
        let mut candidates: Vec<Candidate<B>> = candidates
            .into_iter()
            .map(|((others, shared), (cover, without))| Candidate {
                others,
                shared,
                cover,
                without,
            })
            .collect();
        // Best first on their own merits; ties go to the earlier one.
        candidates.sort_by_key(|c| {
            (
                distance(c.others, c.without.coverage),
                Reverse(c.shared.len()),
                Reverse(c.others.count()),
                c.cover.profile.neg_coverage.count(),
                c.cover.profile.h,
                c.without.h,
            )
        });

        let mut picked: Vec<Candidate<B>> = Vec::new();
        while picked.len() < EXAMPLES && !candidates.is_empty() {
            let shown: HashSet<&String> = picked.iter().flat_map(|p| &p.shared).collect();
            let next = candidates
                .iter()
                .enumerate()
                .min_by_key(|(_, c)| {
                    // How far it repeats the pairs already picked.
                    let repeats: usize = picked
                        .iter()
                        .map(|p| {
                            (p.common() == c.common()) as usize + (p.shared == c.shared) as usize
                        })
                        .sum();
                    let unseen = c.shared.iter().filter(|l| !shown.contains(l)).count();
                    (
                        repeats,
                        distance(c.others, c.without.coverage),
                        Reverse(unseen),
                        Reverse(c.shared.len()),
                    )
                })
                .map(|(index, _)| index)
                .expect("candidates is not empty");
            picked.push(candidates.remove(next));
        }

        picked
            .into_iter()
            .map(|c| {
                let has = literals(c.without.h, self.targets, self.ctx);
                Pair {
                    with: c.cover.profile.h,
                    neg_coverage: c.cover.profile.neg_coverage,
                    others: c.others,
                    without: c.without.h,
                    without_coverage: c.without.coverage,
                    only_with: difference(&c.cover.literals, &has),
                    only_without: difference(&has, &c.cover.literals),
                    shared: c.shared,
                }
            })
            .collect()
    }

    /// Count the covers and the clean hypotheses calling each definition,
    /// and pick the [`Definitions`] from the counts.
    fn definitions(&self, kept: &[HProfile<B>]) -> Definitions {
        let ctx = self.ctx;
        let count = |profiles: Vec<&HProfile<B>>| -> (Vec<u32>, usize) {
            let uses: Vec<AtomicU32> = (0..ctx.pdt.len()).map(|_| AtomicU32::new(0)).collect();
            profiles.par_iter().for_each(|h_profile| {
                let mut defs = SmallVec::new();
                let hypothesis = ctx.hypotheses.get(h_profile.h as usize);
                ctx.pdt.dependencies(hypothesis.iter(), ctx.heap, &mut defs);
                for def in defs {
                    uses[def as usize].fetch_add(1, Ordering::Relaxed);
                }
            });
            let uses = uses.into_iter().map(AtomicU32::into_inner).collect();
            (uses, profiles.len())
        };

        let (in_covers, n_covers) = count(self.covers.iter().map(|c| c.profile).collect());
        let (in_clean, n_clean) = count(kept.iter().collect());
        Definitions::rank(&in_covers, &in_clean, n_covers, n_clean)
    }

    /// The [`Greedy`] covers for `positive`. Other noisy positives are in
    /// neither: only positives proved within the threshold are covered.
    fn greedy(
        &self,
        positive: &Conflict<B>,
        kept: &[HProfile<B>],
        rest: &[HProfile<B>],
    ) -> Greedy<B> {
        let within = covered_by(kept);
        let least_noisy = rest.iter().filter(|h_profile| {
            positive
                .smallest()
                .any(|(set, _)| set == h_profile.neg_coverage)
        });

        let without = greedy_cover(kept.iter(), within);
        let with = greedy_cover(
            kept.iter().chain(least_noisy),
            within.union(&B::from_indices([self.pos])),
        );
        let negatives = |group: &[&HProfile<B>]| {
            let none = B::empty();
            group.iter().fold(none, |all, p| all.union(&p.neg_coverage))
        };
        Greedy {
            without_neg: negatives(&without),
            without: without.iter().map(|p| p.h).collect(),
            with_neg: negatives(&with),
            with: with.iter().map(|p| p.h).collect(),
        }
    }
}

/// Cover the positives `target` greedily from `pool`: whichever profile
/// proves most of those still uncovered, then fewest negatives, then the
/// smallest, until none proves any more.
fn greedy_cover<'p, B: ExampleSet>(
    pool: impl Iterator<Item = &'p HProfile<B>> + Clone,
    target: B,
) -> Vec<&'p HProfile<B>> {
    let mut uncovered = target;
    let mut picked = Vec::new();
    while !uncovered.is_empty() {
        let gain = |h_profile: &HProfile<B>| h_profile.coverage.intersection(&uncovered).count();
        let best = pool
            .clone()
            .filter(|h_profile| gain(h_profile) > 0)
            .min_by_key(|p| {
                (
                    Reverse(gain(p)),
                    p.neg_coverage.count(),
                    p.n_clauses,
                    p.n_literals,
                    p.h,
                )
            });
        let Some(best) = best else {
            break;
        };
        uncovered.difference_with(&best.coverage);
        picked.push(best);
    }
    picked
}

/// The literals of sub hypothesis `h` and of the definitions it depends on,
/// as text, sorted. Each literal's variables are named afresh in the order
/// it has them, so a literal reads the same whatever clause it is in.
/// Leaves out literals of `targets` and of invented predicates, whose names
/// are particular to a definition.
fn literals(h: u32, targets: &[usize], ctx: SearchCtx) -> Vec<String> {
    let meta_subs = ctx
        .pdt
        .test_meta_subs(ctx.hypotheses.get(h as usize), ctx.heap);
    let hypothesis = meta_subs.as_slice();
    let mut heap = QueryHeap::new(ctx.heap, None);

    let mut literals = Vec::new();
    for index in 0..hypothesis.len() {
        let template = hypothesis.template(index, ctx.predicate_table);
        let threshold = template
            .meta_threshold()
            .expect("a hypothesis clause instantiates a meta clause");
        let mut substitution = Substitution::new(template.max_arg_id);
        hypothesis.load_subs(
            index,
            &mut substitution.arg_regs[threshold..template.max_arg_id],
        );
        for &literal in template.iter() {
            let addr = build(&mut heap, &mut substitution, Some(threshold), literal);
            let symbol = heap.symbol_arity(addr).0;
            if targets.contains(&symbol) || ctx.pdt.defines(symbol) {
                continue;
            }
            // The cells just built are this literal's alone.
            let mut seen: Vec<usize> = Vec::new();
            for cell in addr..heap.heap_len() {
                if let (Arg, arg_id) = heap[cell] {
                    let renamed = seen.iter().position(|&id| id == arg_id);
                    heap[cell].1 = renamed.unwrap_or_else(|| {
                        seen.push(arg_id);
                        seen.len() - 1
                    });
                }
            }
            literals.push(heap.term_string(addr));
        }
    }
    literals.sort_unstable();
    literals.dedup();
    literals
}

/// The elements two sorted lists share.
fn intersection(a: &[String], b: &[String]) -> Vec<String> {
    a.iter()
        .filter(|literal| b.binary_search(literal).is_ok())
        .cloned()
        .collect()
}

/// The elements of the first sorted list the second lacks.
fn difference(a: &[String], b: &[String]) -> Vec<String> {
    a.iter()
        .filter(|literal| b.binary_search(literal).is_err())
        .cloned()
        .collect()
}

/// One piece of a [`NoiseReport`].
#[derive(Debug)]
enum Block {
    /// What the report is of; once, first.
    Title(String),
    /// The start of one example's report, named for the example.
    Example(String),
    Section(&'static str),
    SubSection,
    /// A heading and the items under it.
    List(String, Vec<String>),
    Line(String),
}

/// The report, to be written out as text or as Markdown.
#[derive(Debug, Default)]
pub(super) struct NoiseReport {
    blocks: Vec<Block>,
}

impl NoiseReport {
    /// An empty report, headed by what it is a report of.
    pub(super) fn new(title: impl Into<String>) -> Self {
        Self {
            blocks: vec![Block::Title(title.into())],
        }
    }

    pub(super) fn section(&mut self, name: &'static str) {
        self.blocks.push(Block::Section(name));
    }

    fn sub_section(&mut self) {
        self.blocks.push(Block::SubSection);
    }

    pub(super) fn list(
        &mut self,
        heading: impl Into<String>,
        items: impl IntoIterator<Item = String>,
    ) {
        let items = items.into_iter().collect();
        self.blocks.push(Block::List(heading.into(), items));
    }

    pub(super) fn line(&mut self, text: impl Into<String>) {
        self.blocks.push(Block::Line(text.into()));
    }

    /// For the terminal: sections ruled off with `=`, sub sections with
    /// `-`, positives with a double `=`, and lists tab indented.
    pub(super) fn text(&self) -> String {
        let section = "=".repeat(RULE_WIDTH) + "\n";
        let sub_section = "-".repeat(RULE_WIDTH) + "\n";
        let mut text = String::new();
        for block in &self.blocks {
            match block {
                Block::Title(title) => text += &format!("{title}\n"),
                Block::Example(_) => text += &format!("{section}{section}"),
                Block::Section(name) => text += &format!("{section}{name}\n"),
                Block::SubSection => text += &sub_section,
                Block::List(heading, items) => {
                    text += &format!("{heading}\n");
                    for item in items {
                        text += &format!("\t{item}\n");
                    }
                }
                Block::Line(line) => text += &format!("{line}\n"),
            }
        }
        text
    }

    /// For a file: a heading per positive and per section, a rule per sub
    /// section, and lists as bullets of code.
    pub(super) fn markdown(&self) -> String {
        let mut markdown = String::new();
        for block in &self.blocks {
            match block {
                Block::Title(title) => markdown += &format!("# Noise report\n\n{title}\n\n"),
                Block::Example(name) => markdown += &format!("## `{name}`\n\n"),
                Block::Section(name) => markdown += &format!("### {name}\n\n"),
                Block::SubSection => markdown += "---\n\n",
                Block::List(heading, items) => {
                    markdown += &format!("**{heading}**\n\n");
                    for item in items {
                        markdown += &format!("- `{item}`\n");
                    }
                    if !items.is_empty() {
                        markdown += "\n";
                    }
                }
                Block::Line(line) => markdown += &format!("{line}\n\n"),
            }
        }
        markdown
    }
}

/// "1 sub hypothesis", "3 sub hypotheses".
fn sub_hypotheses(count: usize) -> String {
    match count {
        1 => "1 sub hypothesis".to_string(),
        count => format!("{count} sub hypotheses"),
    }
}

/// How the hypotheses within the negative noise bound are spoken of.
pub(super) fn within_bound(neg_noise: usize) -> String {
    match neg_noise {
        0 => "entailing no negative".to_string(),
        1 => "entailing at most 1 negative".to_string(),
        neg_noise => format!("entailing at most {neg_noise} negatives"),
    }
}

/// Add the part of the report on a noisy positive, in six sections.
///
pub(super) fn report_positive<B: ExampleSet>(
    report: &mut NoiseReport,
    positive: &Conflict<B>,
    profiled: Profiled<B>,
) {
    let Profiled {
        kept,
        rest,
        pos_goals,
        neg_goals,
        ctx,
    } = profiled;
    let examples = &Examples::find(positive, kept, rest, pos_goals, ctx);
    let mut heap = QueryHeap::new(ctx.heap, None);
    // The hypotheses the positive's own are set against.
    let bound = &within_bound(ctx.parallel.neg_noise);

    let names = |heap: &QueryHeap, set: B, goals: &[usize]| -> Vec<String> {
        set.indices()
            .into_iter()
            .map(|example| heap.term_string(goals[example]))
            .collect()
    };
    let hypotheses = |count: usize| match count {
        1 => "1 hypothesis".to_string(),
        count => format!("{count} hypotheses"),
    };
    // The clauses of a hypothesis and its definitions.
    let clauses = |heap: &mut QueryHeap, h: u32| -> Vec<String> {
        let meta_subs = ctx
            .pdt
            .test_meta_subs(ctx.hypotheses.get(h as usize), ctx.heap);
        meta_subs
            .as_slice()
            .clause_strings(heap, ctx.predicate_table)
    };

    let name = heap.term_string(pos_goals[positive.pos]);
    report.blocks.push(Block::Example(name));

    // The noisy positive and its minimal negative set.
    report.list(
        &format!(
            "Noisy positive (entailed by {})",
            hypotheses(positive.covering)
        ),
        [heap.term_string(pos_goals[positive.pos])],
    );
    if positive.shared_is_minimal() {
        report.list(
            &format!(
                "Minimal negatives (entailed alone by {})",
                hypotheses(positive.sets[0].1)
            ),
            names(&heap, positive.shared, neg_goals),
        );
    } else {
        match positive.shared.is_empty() {
            true => report.line("No negative is entailed by all of them"),
            false => report.list(
                "Negatives entailed by all of them",
                names(&heap, positive.shared, neg_goals),
            ),
        }
        for (set, count) in positive.smallest() {
            report.list(
                &format!(
                    "Smallest negative set (entailed alone by {})",
                    hypotheses(count)
                ),
                names(&heap, set, neg_goals),
            );
        }
    }
    // The minimal set is long enough to name once.
    let negatives = |report: &mut NoiseReport, heap: &QueryHeap, set: B| {
        if positive.shared_is_minimal() && set == positive.shared {
            report.line("Entails the minimal negatives");
        } else if set.count() == 0 {
            report.line("Entails no negative");
        } else {
            report.list("Negatives entailed", names(heap, set, neg_goals));
        }
    };
    // A heading is left out when it has nothing under it.
    let optional = |report: &mut NoiseReport, heading: &str, items: Vec<String>| {
        if !items.is_empty() {
            report.list(heading, items);
        }
    };

    report.section("Predicate definitions");
    let definitions = &examples.definitions;
    let sub_sections = [
        (
            format!("Least used by hypotheses {bound}"),
            &definitions.noisy,
        ),
        (
            "Least used by hypotheses entailing the noisy positive".to_string(),
            &definitions.clean,
        ),
        ("Most used by both".to_string(), &definitions.common),
    ];
    for (heading, def_uses) in sub_sections {
        report.sub_section();
        report.line(heading);
        if def_uses.is_empty() {
            report.line("No such invented predicate");
        }
        for def_use in def_uses {
            // Its own clauses name it, so it is found among the
            // definitions they call, with those it depends on.
            let mut defs = SmallVec::new();
            let own = ctx.pdt.get(def_use.def as usize);
            ctx.pdt.dependencies(own.iter(), ctx.heap, &mut defs);
            let meta_subs: Vec<&[usize]> = defs
                .iter()
                .flat_map(|&def| {
                    let def = ctx.pdt.get(def as usize);
                    (0..def.len()).map(move |clause| def.get(clause))
                })
                .collect();
            let clauses = meta_subs
                .as_slice()
                .clause_strings(&mut heap, ctx.predicate_table);
            report.list("Definition", clauses);
            report.line(format!(
                "Used by {} of {} entailing the noisy positive, and {} of {} entailing no \
                     negative",
                def_use.in_covers,
                hypotheses(definitions.n_covers),
                def_use.in_clean,
                hypotheses(definitions.n_clean),
            ));
        }
    }

    report.section("Unique properties");
    for lone in &examples.lone {
        report.sub_section();
        report.list("Hypothesis", clauses(&mut heap, lone.h));
        optional(
            report,
            "Literals only hypotheses entailing the noisy positive have",
            lone.unique.clone(),
        );
        let others = lone.coverage.difference(&B::from_indices([positive.pos]));
        optional(
            report,
            "Other positives entailed",
            names(&heap, others, pos_goals),
        );
        negatives(report, &heap, lone.neg_coverage);
    }

    report.section("Comparisons");
    if examples.pairs.is_empty() {
        report.line(format!(
            "No hypothesis entails any of the same positives and {}",
            bound.trim_start_matches("entailing ")
        ));
    }
    for pair in &examples.pairs {
        report.sub_section();
        report.list(
            "Hypothesis entailing the noisy positive",
            clauses(&mut heap, pair.with),
        );
        report.list(
            "Other positives entailed",
            names(&heap, pair.others, pos_goals),
        );
        negatives(report, &heap, pair.neg_coverage);

        let (others, without) = (pair.others, pair.without_coverage);
        report.list(
            &format!("Nearest hypothesis without it, {bound}"),
            clauses(&mut heap, pair.without),
        );
        report.list(
            "Positives entailed by both",
            names(&heap, others.intersection(&without), pos_goals),
        );
        optional(
            report,
            "Positives it does not entail",
            names(&heap, others.difference(&without), pos_goals),
        );
        optional(
            report,
            "Further positives it entails",
            names(&heap, without.difference(&others), pos_goals),
        );
        optional(report, "Literals both have", pair.shared.clone());
        optional(
            report,
            "Literals only the hypothesis entailing it has",
            pair.only_with.clone(),
        );
        optional(
            report,
            "Literals only the hypothesis without it has",
            pair.only_without.clone(),
        );
    }

    report.section("Greedy hypothesis");
    let greedy = &examples.greedy;
    let pool = match positive.shared_is_minimal() {
        true => "the minimal negatives",
        false => "a smallest negative set",
    };
    let runs = [
        (
            "Without the noisy positive".to_string(),
            &greedy.without,
            greedy.without_neg,
        ),
        (
            format!("With the noisy positive, adding hypotheses entailing {pool}"),
            &greedy.with,
            greedy.with_neg,
        ),
    ];
    for (heading, group, neg_coverage) in runs {
        report.sub_section();
        let sub_hypotheses = group.iter().map(|&h| ctx.hypotheses.get(h as usize));
        let meta_subs = ctx.pdt.union_meta_subs(sub_hypotheses, ctx.heap);
        let clauses = meta_subs
            .as_slice()
            .clause_strings(&mut heap, ctx.predicate_table);
        report.list(
            &format!(
                "{heading} ({} sub {})",
                group.len(),
                if group.len() == 1 {
                    "hypothesis"
                } else {
                    "hypotheses"
                }
            ),
            clauses,
        );
        negatives(report, &heap, neg_coverage);
    }

    report.section("Conclusions");
    let count = |count: usize, one: &str| match count {
        1 => format!("1 {one}"),
        count => format!("{count} {one}s"),
    };
    match positive.shared.count() {
        0 => report.line(format!(
            "No one negative comes with the noisy positive every time, but entailing it \
                 costs at least {}.",
            count(positive.fewest(), "negative")
        )),
        shared => {
            report.line(format!(
                "No hypothesis tells the noisy positive from {}: every hypothesis \
                     entailing it entails {} too. Either an example is mislabelled, or the \
                     background knowledge and/or meta-rules lack what is needed to form a \
                     hypothesis separating them.",
                count(shared, "negative"),
                if shared == 1 {
                    "that negative"
                } else {
                    "those negatives"
                }
            ));
            if !positive.shared_is_minimal() {
                report.line(format!(
                    "Entailing it costs at least {}.",
                    count(positive.fewest(), "negative")
                ));
            }
        }
    }
    optional(
        report,
        "Positives every hypothesis entailing it also entails",
        names(&heap, examples.always_with, pos_goals),
    );
    let boundary = &examples.boundary;
    let uses = |uses: &[LiteralUse]| -> Vec<String> {
        uses.iter()
            .map(|u| {
                format!(
                    "{} (in {} of {} entailing it, {} of {} {bound})",
                    u.literal, u.in_covers, boundary.n_covers, u.in_clean, boundary.n_clean
                )
            })
            .collect()
    };
    optional(
        report,
        "Literals most particular to hypotheses entailing the noisy positive",
        uses(&boundary.noisy),
    );
    optional(
        report,
        &format!("Literals most particular to hypotheses {bound}"),
        uses(&boundary.clean),
    );
    report.line(format!(
        "A greedy cover of the other positives takes {} and entails {}; with the noisy \
             positive it takes {} and entails {}.",
        sub_hypotheses(greedy.without.len()),
        count(greedy.without_neg.count(), "negative"),
        sub_hypotheses(greedy.with.len()),
        count(greedy.with_neg.count(), "negative"),
    ));
}

/// A toy learning problem.
///
/// Target `t/1`, positives `t(p1)`..`t(p5)`, negatives `t(n1)`..`t(n3)`,
/// and sub hypotheses of clauses `head(X):-body(X)` over background
/// predicates that each hold of the examples listed:
///
/// | body | positives | negatives  |
/// |------|-----------|------------|
/// | a    | p1, p2    |            |
/// | b    | p2, p3    | n1         |
/// | c    | p3        | n1, n2     |
/// | d    | p4        | n1         |
/// | e    | p4        | n2         |
/// | f    | p4        | n1, n2, n3 |
/// | g    | p4        | n1, n2     |
/// | h    | p4        | n1, n3     |
/// | i    | p2        |            |
/// | k    | p3        | n1         |
/// | m    | p1, p2, p3| n2         |
///
/// With one hypothesis `t(X):-body(X)` for each of `a`..`f` ([`BASE`]):
/// `p1` and `p2` are covered cleanly, `p3` only with `n1` (and `b` needs
/// nothing more), `p4` only with a negative but no one negative in
/// particular, and nothing covers `p5`.
#[cfg(test)]
pub(super) mod toy_model {
    use super::{
        report_positive, Conflict, DefUse, Definitions, Examples, LiteralUse, NoiseReport, Profiled,
    };
    use crate::bitflag::BitFlag;
    use crate::{
        learners::{
            coverage::{
                build_profiles,
                fixture::{fixture_with_facts, Fixture},
                within, HProfile,
            },
            noise::conflicts,
            utils::compile_examples,
        },
        ParallelConfig,
    };

    pub(in crate::learners) const FACTS: &[&str] = &[
        "a(p1).", "a(p2).", "b(p2).", "b(p3).", "b(n1).", "c(p3).", "c(n1).", "c(n2).", "d(p4).",
        "d(n1).", "e(p4).", "e(n2).", "f(p4).", "f(n1).", "f(n2).", "f(n3).", "g(p4).", "g(n1).",
        "g(n2).", "h(p4).", "h(n1).", "h(n3).", "i(p2).", "k(p3).", "k(n1).", "m(p1).", "m(p2).",
        "m(p3).", "m(n2).",
    ];
    pub(in crate::learners) const BASE: [&str; 6] = ["a", "b", "c", "d", "e", "f"];
    pub(in crate::learners) const POSITIVES: [&str; 5] =
        ["t(p1)", "t(p2)", "t(p3)", "t(p4)", "t(p5)"];
    pub(in crate::learners) const NEGATIVES: [&str; 3] = ["t(n1)", "t(n2)", "t(n3)"];
    /// Index of `t(p3)` and `t(p4)` in [`POSITIVES`].
    const P3: usize = 2;
    const P4: usize = 3;

    /// Sub hypotheses proved for real: those entailing no negative as
    /// `kept`, the others as `rest`.
    pub(in crate::learners) struct Model {
        pub(in crate::learners) fixture: Fixture,
        pub(in crate::learners) pos_goals: Vec<usize>,
        pub(in crate::learners) kept: Vec<HProfile>,
        pub(in crate::learners) rest: Vec<HProfile>,
    }

    /// One hypothesis `t(X):-body(X)` per body.
    pub(in crate::learners) fn single(
        bodies: &[&'static str],
    ) -> Vec<Vec<(&'static str, &'static str)>> {
        bodies.iter().map(|&body| vec![("t", body)]).collect()
    }

    pub(in crate::learners) fn model(hypotheses: &[Vec<(&str, &str)>]) -> Model {
        let mut fixture = fixture_with_facts(FACTS, hypotheses, &NEGATIVES);
        let positives: Vec<String> = POSITIVES.iter().map(|goal| goal.to_string()).collect();
        let pos_goals = compile_examples(&positives, &mut fixture.prog_heap);

        let ctx = fixture.ctx(ParallelConfig::default());
        let (kept, rest) = within(build_profiles(&pos_goals, &fixture.neg_goals, ctx), 0);
        Model {
            fixture,
            pos_goals,
            kept,
            rest,
        }
    }

    fn model_of(bodies: &[&'static str]) -> Model {
        model(&single(bodies))
    }

    impl Model {
        fn profiled(&self) -> Profiled<'_> {
            Profiled {
                kept: &self.kept,
                rest: &self.rest,
                pos_goals: &self.pos_goals,
                neg_goals: &self.fixture.neg_goals,
                ctx: self.fixture.ctx(ParallelConfig::default()),
            }
        }

        /// The positives only entailed together with negatives.
        fn noisy(&self) -> Vec<Conflict> {
            conflicts(self.profiled()).0
        }

        fn examples(&self, pos: usize) -> Examples {
            let noisy = self.noisy();
            let positive = noisy.iter().find(|n| n.pos == pos).unwrap();
            Examples::find(
                positive,
                &self.kept,
                &self.rest,
                &self.pos_goals,
                self.fixture.ctx(ParallelConfig::default()),
            )
        }

        /// Every noisy positive reported on.
        fn report(&self) -> NoiseReport {
            let noisy = self.noisy();
            let mut report = NoiseReport::new(format!(
                "{} positive example(s) are only entailed together with a negative",
                noisy.len()
            ));
            for positive in &noisy {
                report_positive(&mut report, positive, self.profiled());
            }
            report
        }
    }

    #[test]
    fn the_model_profiles_as_tabled() {
        let model = model(&single(&BASE));
        let coverage = |profiles: &[HProfile]| -> Vec<(u32, Vec<usize>, Vec<usize>)> {
            profiles
                .iter()
                .map(|p| (p.h, p.coverage.indices(), p.neg_coverage.indices()))
                .collect()
        };
        assert_eq!(coverage(&model.kept), vec![(0, vec![0, 1], vec![])]);
        assert_eq!(
            coverage(&model.rest),
            vec![
                (1, vec![1, 2], vec![0]),
                (2, vec![2], vec![0, 1]),
                (3, vec![3], vec![0]),
                (4, vec![3], vec![1]),
                (5, vec![3], vec![0, 1, 2]),
            ]
        );
    }

    #[test]
    fn cleanly_covered_and_uncovered_positives_are_not_noisy() {
        let positives: Vec<usize> = model(&single(&BASE))
            .noisy()
            .iter()
            .map(|n| n.pos)
            .collect();
        // Not p1 or p2 (`a` is clean, though `b` also covers p2), and not
        // p5, which nothing covers.
        assert_eq!(positives, vec![P3, P4]);
    }

    #[test]
    fn a_hypothesis_entailing_only_the_shared_negatives_makes_them_minimal() {
        let noisy = model(&single(&BASE)).noisy();
        let p3 = &noisy[0];

        assert_eq!(p3.covering, 2);
        assert_eq!(p3.shared, 0b001);
        assert_eq!(p3.fewest(), 1);
        assert!(p3.shared_is_minimal());
        assert_eq!(p3.sets[0].1, 1, "only `b`");
    }

    #[test]
    fn covers_sharing_no_negative_report_their_smallest_sets() {
        let noisy = model(&single(&BASE)).noisy();
        let p4 = &noisy[1];

        assert_eq!(p4.covering, 3);
        assert_eq!(p4.shared, 0);
        assert!(!p4.shared_is_minimal());
        assert_eq!(p4.fewest(), 1);
        let smallest: Vec<(u128, usize)> = p4.smallest().collect();
        assert_eq!(smallest, vec![(0b001, 1), (0b010, 1)]);
    }

    #[test]
    fn shared_negatives_are_not_minimal_when_every_cover_entails_more() {
        // `g` entails n1 and n2, `h` entails n1 and n3: both covers of p4
        // entail n1, but neither entails n1 alone.
        let noisy = model(&single(&["a", "g", "h"])).noisy();
        let p4 = &noisy[0];

        assert_eq!(p4.pos, P4);
        assert_eq!(p4.shared, 0b001);
        assert!(!p4.shared_is_minimal());
        assert_eq!(p4.fewest(), 2);
        let smallest: Vec<u128> = p4.smallest().map(|(set, _)| set).collect();
        assert_eq!(smallest, vec![0b011, 0b101]);
    }

    /// [`BASE`] and more, for the examples of `p3`:
    ///
    /// | h | clauses                | positives | negatives |
    /// |---|------------------------|-----------|-----------|
    /// | 0 | t:-a                   | p1, p2    |           |
    /// | 1 | t:-b                   | p2, p3    | n1        |
    /// | 2 | t:-c                   | p3        | n1, n2    |
    /// | 3 | t:-k                   | p3        | n1        |
    /// | 4 | t:-i                   | p2        |           |
    /// | 5 | t:-i, u:-b, u:-k       | p2        |           |
    ///
    /// Hypothesis 5 is 4 with clauses that prove no example, there to use
    /// `b` and `k` outside the covers of `p3`.
    fn extended() -> Vec<Vec<(&'static str, &'static str)>> {
        let mut hypotheses = single(&["a", "b", "c", "k", "i"]);
        hypotheses.push(vec![("t", "i"), ("u", "b"), ("u", "k")]);
        hypotheses
    }

    #[test]
    fn a_cover_with_a_literal_of_its_own_is_the_first_example() {
        let model = model(&extended());
        let lone = model.examples(P3).lone;

        // `c` is used by nothing but hypothesis 2, which so comes before 3
        // though 3 entails fewer negatives. 1 entails another positive too.
        let picked: Vec<(u32, Vec<String>)> = lone
            .iter()
            .map(|lone| (lone.h, lone.unique.clone()))
            .collect();
        assert_eq!(picked, vec![(2, vec!["c(A)".to_string()]), (3, vec![])]);
    }

    #[test]
    fn without_a_literal_of_their_own_the_smallest_coverage_comes_first() {
        // No `c` hypothesis, and `b` and `k` are used by hypothesis 4.
        let mut hypotheses = single(&["a", "b", "k", "i"]);
        hypotheses.push(vec![("t", "i"), ("u", "b"), ("u", "k")]);
        let model = model(&hypotheses);

        let picked: Vec<(u32, Vec<usize>)> = model
            .examples(P3)
            .lone
            .iter()
            .map(|lone| (lone.h, lone.coverage.indices()))
            .collect();
        assert_eq!(picked, vec![(2, vec![2]), (1, vec![1, 2])]);
    }

    #[test]
    fn a_pair_covers_the_same_other_positives_and_prefers_shared_literals() {
        let model = model(&extended());
        let pairs = model.examples(P3).pairs;

        // Only hypothesis 1 covers another positive, p2. Hypotheses 4 and 5
        // cover just p2 cleanly (0 covers p1 as well), and 5 shares `b(A)`.
        let pair = &pairs[0];
        assert_eq!((pair.with, pair.without), (1, 5));
        assert_eq!(pair.others.indices(), vec![1]);
        assert_eq!(pair.without_coverage.indices(), vec![1]);
        assert_eq!(pair.neg_coverage.indices(), vec![0]);
        assert_eq!(pair.shared, vec!["b(A)"]);
        assert!(pair.only_with.is_empty());
        assert_eq!(pair.only_without, vec!["i(A)", "k(A)", "u(A)"]);
    }

    #[test]
    fn a_second_pair_differs_from_the_first() {
        let model = model(&extended());
        let pairs = model.examples(P3).pairs;

        // The same cover and positives again, there being no others, but
        // not the same shared literals: hypothesis 4 shares none.
        assert_eq!(pairs.len(), 2);
        assert_eq!((pairs[1].with, pairs[1].without), (1, 4));
        assert!(pairs[1].shared.is_empty());
        assert_eq!(pairs[1].only_with, vec!["b(A)"]);
        assert_eq!(pairs[1].only_without, vec!["i(A)"]);
    }

    #[test]
    fn a_pair_differing_in_positives_and_literals_beats_a_nearer_repeat() {
        // `m` covers p1 and p2 besides p3, `b` just p2. `a` matches `m`
        // exactly, and `i` matches `b` exactly; a further `a` hypothesis
        // sharing `b(A)` would be as near to `m` as the first pair.
        let mut hypotheses = single(&["m", "b", "a", "i"]);
        hypotheses.push(vec![("t", "a"), ("u", "m")]);
        let model = model(&hypotheses);
        let pairs: Vec<(u32, u32, Vec<String>)> = model
            .examples(P3)
            .pairs
            .iter()
            .map(|pair| (pair.with, pair.without, pair.shared.clone()))
            .collect();

        // First the pair sharing `m(A)`; then, rather than `m` with the
        // plain `a` hypothesis (the same positives again), `b` with `i`.
        assert_eq!(
            pairs,
            vec![(0, 4, vec!["m(A)".to_string()]), (1, 3, vec![])]
        );
    }

    #[test]
    fn a_pair_need_not_share_a_literal() {
        let model = model(&single(&["a", "b", "c", "k", "i"]));
        let pairs = model.examples(P3).pairs;

        assert_eq!(pairs.len(), 1);
        assert_eq!((pairs[0].with, pairs[0].without), (1, 4));
        assert!(pairs[0].shared.is_empty());
    }

    #[test]
    fn without_an_exact_match_the_nearest_clean_coverage_is_paired() {
        // `m` covers p1 and p2 besides p3. `i` covers p2 alone.
        let model = model(&single(&["m", "i"]));
        let pairs = model.examples(P3).pairs;
        assert_eq!((pairs[0].with, pairs[0].without), (0, 1));
        assert_eq!(pairs[0].others.indices(), vec![0, 1]);
        assert_eq!(pairs[0].without_coverage.indices(), vec![1]);

        // With `a` there is an exact match for `m`. For `b`, which covers
        // p2 besides p3, `i` is exact and `a` covers p1 too.
        let model = model_of(&["m", "i", "a", "b"]);
        let pairs: Vec<(u32, u32)> = model
            .examples(P3)
            .pairs
            .iter()
            .map(|pair| (pair.with, pair.without))
            .collect();
        assert_eq!(pairs, vec![(0, 2), (3, 1)]);

        // Missing a positive is further off than covering one more.
        let model = model_of(&["a", "b"]);
        let pairs = model.examples(P3).pairs;
        assert_eq!((pairs[0].with, pairs[0].without), (1, 0));
        assert_eq!(pairs[0].without_coverage.indices(), vec![0, 1]);
    }

    #[test]
    fn no_pair_for_covers_entailing_no_other_positive() {
        let model = model(&single(&BASE));
        assert!(model.examples(P4).pairs.is_empty());
    }

    #[test]
    fn a_literal_reads_the_same_in_any_clause() {
        // `b(A)` is a body literal of `t` in one hypothesis and of `u` in
        // the other.
        let model = model(&extended());
        assert_eq!(model.examples(P3).pairs[0].shared, vec!["b(A)"]);
    }

    #[test]
    fn definitions_are_ranked_by_who_calls_them() {
        // Definition:            0   1   2   3   4
        let in_covers = [10, 10, 0, 4, 0];
        let in_clean = [0, 50, 90, 2, 0];
        let ranked = Definitions::rank(&in_covers, &in_clean, 10, 100);
        let defs = |uses: &[DefUse]| -> Vec<u32> { uses.iter().map(|d| d.def).collect() };

        // 0 is called by no clean hypothesis; 3 by fewer than 1 is.
        assert_eq!(defs(&ranked.noisy), vec![0, 3]);
        // 2 is called by no cover; then 3, by fewer covers than 1 is.
        assert_eq!(defs(&ranked.clean), vec![2, 3]);
        // 1 is called by all the covers and half the clean hypotheses;
        // 3 by 4 in 10 and 2 in 100. 4 is called by nothing and is nowhere.
        assert_eq!(defs(&ranked.common), vec![1, 3]);
        assert_eq!(
            ranked.common[0],
            DefUse {
                def: 1,
                in_covers: 10,
                in_clean: 50
            }
        );
    }

    #[test]
    fn a_model_without_invented_predicates_has_no_definitions_to_show() {
        let definitions = model(&single(&BASE)).examples(P3).definitions;
        assert_eq!((definitions.n_covers, definitions.n_clean), (2, 1));
        assert!(definitions.noisy.is_empty());
        assert!(definitions.clean.is_empty());
        assert!(definitions.common.is_empty());
    }

    #[test]
    fn the_greedy_cover_with_a_noisy_positive_adds_its_least_noisy_covers() {
        let model = model(&single(&BASE));

        // Only `a` is within the threshold; `b` entails just the minimal
        // negative of p3. p4 is in neither cover, being noisy itself.
        let greedy = model.examples(P3).greedy;
        assert_eq!(greedy.without, vec![0]);
        assert!(greedy.without_neg.indices().is_empty());
        assert_eq!(greedy.with, vec![0, 1]);
        assert_eq!(greedy.with_neg.indices(), vec![0]);

        // p4 has two smallest negative sets, from `d` and `e`: either
        // will do, and `c` and `f` are not used.
        let greedy = model.examples(P4).greedy;
        assert_eq!(greedy.without, vec![0]);
        assert_eq!(greedy.with, vec![0, 3]);
        assert_eq!(greedy.with_neg.indices(), vec![0]);
    }

    #[test]
    fn boundary_literals_are_the_most_lopsided() {
        // The covers of p3 are `b`, `c` and `k`; the clean hypotheses are
        // 0 (`a`), 4 (`i`) and 5 (`i`, with `u:-b` and `u:-k`).
        let model = model(&extended());
        let examples = model.examples(P3);
        let boundary = &examples.boundary;
        assert_eq!((boundary.n_covers, boundary.n_clean), (3, 3));

        let literals = |uses: &[LiteralUse]| -> Vec<(String, u32, u32)> {
            uses.iter()
                .map(|u| (u.literal.clone(), u.in_covers, u.in_clean))
                .collect()
        };
        // `b(A)` and `k(A)` are in one of each, so on neither side.
        assert_eq!(literals(&boundary.noisy), vec![("c(A)".to_string(), 1, 0)]);
        assert_eq!(
            literals(&boundary.clean),
            vec![
                ("i(A)".to_string(), 0, 2),
                ("a(A)".to_string(), 0, 1),
                ("u(A)".to_string(), 0, 1)
            ]
        );
        // `b` covers p2 as well, `c` and `k` do not.
        assert!(examples.always_with.indices().is_empty());
    }

    #[test]
    fn positives_every_cover_entails_are_found() {
        // `m` is the one cover of p3, and covers p1 and p2 too.
        let model = model(&single(&["m", "i"]));
        assert_eq!(model.examples(P3).always_with.indices(), vec![0, 1]);
    }

    #[test]
    fn the_report_as_text() {
        let report = model(&extended()).report().text();
        let (section, sub_section) = (&"=".repeat(80)[..], &"-".repeat(80)[..]);
        let expected = [
            "1 positive example(s) are only entailed together with a negative",
            section,
            section,
            "Noisy positive (entailed by 3 hypotheses)",
            "\tt(p3)",
            "Minimal negatives (entailed alone by 2 hypotheses)",
            "\tt(n1)",
            section,
            "Predicate definitions",
            sub_section,
            "Least used by hypotheses entailing no negative",
            "No such invented predicate",
            sub_section,
            "Least used by hypotheses entailing the noisy positive",
            "No such invented predicate",
            sub_section,
            "Most used by both",
            "No such invented predicate",
            section,
            "Unique properties",
            sub_section,
            "Hypothesis",
            "\tt(A):-c(A).",
            "Literals only hypotheses entailing the noisy positive have",
            "\tc(A)",
            "Negatives entailed",
            "\tt(n1)",
            "\tt(n2)",
            sub_section,
            "Hypothesis",
            "\tt(A):-k(A).",
            "Entails the minimal negatives",
            section,
            "Comparisons",
            sub_section,
            "Hypothesis entailing the noisy positive",
            "\tt(A):-b(A).",
            "Other positives entailed",
            "\tt(p2)",
            "Entails the minimal negatives",
            "Nearest hypothesis without it, entailing no negative",
            "\tt(A):-i(A).",
            "\tu(A):-b(A).",
            "\tu(A):-k(A).",
            "Positives entailed by both",
            "\tt(p2)",
            "Literals both have",
            "\tb(A)",
            "Literals only the hypothesis without it has",
            "\ti(A)",
            "\tk(A)",
            "\tu(A)",
            sub_section,
            "Hypothesis entailing the noisy positive",
            "\tt(A):-b(A).",
            "Other positives entailed",
            "\tt(p2)",
            "Entails the minimal negatives",
            "Nearest hypothesis without it, entailing no negative",
            "\tt(A):-i(A).",
            "Positives entailed by both",
            "\tt(p2)",
            "Literals only the hypothesis entailing it has",
            "\tb(A)",
            "Literals only the hypothesis without it has",
            "\ti(A)",
            section,
            "Greedy hypothesis",
            sub_section,
            "Without the noisy positive (1 sub hypothesis)",
            "\tt(A):-a(A).",
            "Entails no negative",
            sub_section,
            "With the noisy positive, adding hypotheses entailing the minimal negatives (2 sub hypotheses)",
            "\tt(A):-a(A).",
            "\tt(A):-b(A).",
            "Entails the minimal negatives",
            section,
            "Conclusions",
            "No hypothesis tells the noisy positive from 1 negative: every hypothesis entailing it entails that negative too. Either an example is mislabelled, or the background knowledge and/or meta-rules lack what is needed to form a hypothesis separating them.",
            "Literals most particular to hypotheses entailing the noisy positive",
            "\tc(A) (in 1 of 3 entailing it, 0 of 3 entailing no negative)",
            "Literals most particular to hypotheses entailing no negative",
            "\ti(A) (in 0 of 3 entailing it, 2 of 3 entailing no negative)",
            "\ta(A) (in 0 of 3 entailing it, 1 of 3 entailing no negative)",
            "\tu(A) (in 0 of 3 entailing it, 1 of 3 entailing no negative)",
            "A greedy cover of the other positives takes 1 sub hypothesis and entails 0 negatives; with the noisy positive it takes 2 sub hypotheses and entails 1 negative.",
        ];
        assert_eq!(report, expected.join("\n") + "\n");
    }

    #[test]
    fn the_report_as_markdown() {
        let report = model(&extended()).report();
        let expected = [
            "# Noise report",
            "",
            "1 positive example(s) are only entailed together with a negative",
            "",
            "## `t(p3)`",
            "",
            "**Noisy positive (entailed by 3 hypotheses)**",
            "",
            "- `t(p3)`",
            "",
            "**Minimal negatives (entailed alone by 2 hypotheses)**",
            "",
            "- `t(n1)`",
            "",
            "### Predicate definitions",
            "",
            "---",
            "",
            "Least used by hypotheses entailing no negative",
            "",
            "No such invented predicate",
            "",
            "---",
            "",
            "Least used by hypotheses entailing the noisy positive",
            "",
            "No such invented predicate",
            "",
            "---",
            "",
            "Most used by both",
            "",
            "No such invented predicate",
            "",
            "### Unique properties",
            "",
            "---",
            "",
            "**Hypothesis**",
            "",
            "- `t(A):-c(A).`",
            "",
            "**Literals only hypotheses entailing the noisy positive have**",
            "",
            "- `c(A)`",
            "",
            "**Negatives entailed**",
            "",
            "- `t(n1)`",
            "- `t(n2)`",
            "",
            "---",
            "",
            "**Hypothesis**",
            "",
            "- `t(A):-k(A).`",
            "",
            "Entails the minimal negatives",
            "",
            "### Comparisons",
            "",
            "---",
            "",
            "**Hypothesis entailing the noisy positive**",
            "",
            "- `t(A):-b(A).`",
            "",
            "**Other positives entailed**",
            "",
            "- `t(p2)`",
            "",
            "Entails the minimal negatives",
            "",
            "**Nearest hypothesis without it, entailing no negative**",
            "",
            "- `t(A):-i(A).`",
            "- `u(A):-b(A).`",
            "- `u(A):-k(A).`",
            "",
            "**Positives entailed by both**",
            "",
            "- `t(p2)`",
            "",
            "**Literals both have**",
            "",
            "- `b(A)`",
            "",
            "**Literals only the hypothesis without it has**",
            "",
            "- `i(A)`",
            "- `k(A)`",
            "- `u(A)`",
            "",
            "---",
            "",
            "**Hypothesis entailing the noisy positive**",
            "",
            "- `t(A):-b(A).`",
            "",
            "**Other positives entailed**",
            "",
            "- `t(p2)`",
            "",
            "Entails the minimal negatives",
            "",
            "**Nearest hypothesis without it, entailing no negative**",
            "",
            "- `t(A):-i(A).`",
            "",
            "**Positives entailed by both**",
            "",
            "- `t(p2)`",
            "",
            "**Literals only the hypothesis entailing it has**",
            "",
            "- `b(A)`",
            "",
            "**Literals only the hypothesis without it has**",
            "",
            "- `i(A)`",
            "",
            "### Greedy hypothesis",
            "",
            "---",
            "",
            "**Without the noisy positive (1 sub hypothesis)**",
            "",
            "- `t(A):-a(A).`",
            "",
            "Entails no negative",
            "",
            "---",
            "",
            "**With the noisy positive, adding hypotheses entailing the minimal negatives (2 sub hypotheses)**",
            "",
            "- `t(A):-a(A).`",
            "- `t(A):-b(A).`",
            "",
            "Entails the minimal negatives",
            "",
            "### Conclusions",
            "",
            "No hypothesis tells the noisy positive from 1 negative: every hypothesis entailing it entails that negative too. Either an example is mislabelled, or the background knowledge and/or meta-rules lack what is needed to form a hypothesis separating them.",
            "",
            "**Literals most particular to hypotheses entailing the noisy positive**",
            "",
            "- `c(A) (in 1 of 3 entailing it, 0 of 3 entailing no negative)`",
            "",
            "**Literals most particular to hypotheses entailing no negative**",
            "",
            "- `i(A) (in 0 of 3 entailing it, 2 of 3 entailing no negative)`",
            "- `a(A) (in 0 of 3 entailing it, 1 of 3 entailing no negative)`",
            "- `u(A) (in 0 of 3 entailing it, 1 of 3 entailing no negative)`",
            "",
            "A greedy cover of the other positives takes 1 sub hypothesis and entails 0 negatives; with the noisy positive it takes 2 sub hypotheses and entails 1 negative.",
        ];
        assert_eq!(report.markdown(), expected.join("\n") + "\n\n");
    }
}
