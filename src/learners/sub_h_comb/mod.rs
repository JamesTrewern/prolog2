//! Sub hypothesis combination: from the sub hypotheses generalisation
//! found to the hypotheses returned.
//!
//! [`combine`] is the way in. Its stages, in order:
//!
//! 1. **Profile** (`coverage`): every example is proved against every sub
//!    hypothesis, once.
//! 2. **Filter** (`coverage`, `noise`): the sub hypotheses within the
//!    negative noise bound are kept. A positive none of them proves ends
//!    the run with a report (`noise_report`), unless it may be left.
//! 3. **Search** (`search`): groups of sub hypotheses covering the
//!    positives are built from the profiles alone.
//! 4. **Pool** (`pool`): each group's hypothesis is reduced, proved and
//!    ranked, and the best returned.

mod coverage;
mod noise;
mod noise_report;
mod pool;
mod search;

use coverage::{build_profiles, within, ExampleSet, HProfile, Profiled};
use noise::{uncovered, uncovered_report};
use pool::best_of_pool;
use search::{undominated, Search, BRANCHING_FACTOR, MAX_EFFORT};

use super::utils::SearchCtx;
use crate::{
    heap::{Heap, ProgramHeap, QueryHeap},
    program::{HypothesisTrait, PredicateTable},
};

/// The hypotheses learned from the sub hypotheses in `ctx`, as Prolog
/// source and best first; `None` when there is none to return.
///
/// `pos_goals` and `neg_goals` are the examples, compiled onto the program
/// heap. At most 1024 of either can be learned from.
pub(super) fn combine(
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Option<Vec<String>> {
    // The narrowest sets that hold the examples: there is one profile to a
    // sub hypothesis, and the search reads them all at every step.
    let most = pos_goals.len().max(neg_goals.len());
    match most {
        0..=8 => combine_as::<u8>(pos_goals, neg_goals, ctx),
        9..=16 => combine_as::<u16>(pos_goals, neg_goals, ctx),
        17..=32 => combine_as::<u32>(pos_goals, neg_goals, ctx),
        33..=64 => combine_as::<u64>(pos_goals, neg_goals, ctx),
        65..=128 => combine_as::<u128>(pos_goals, neg_goals, ctx),
        129..=256 => combine_as::<[u128; 2]>(pos_goals, neg_goals, ctx),
        257..=512 => combine_as::<[u128; 4]>(pos_goals, neg_goals, ctx),
        513..=1024 => combine_as::<[u128; 8]>(pos_goals, neg_goals, ctx),
        _ => {
            println!(
                "{most} positive or negative examples are more than the 1024 of either that \
                 can be learned from"
            );
            println!("No Valid Hypothesis Found");
            None
        }
    }
}

/// [`combine`] with profiles holding sets of `B`: profile them, keep those within the negative noise
/// bound, search for groups of them, and take the best of the hypotheses
/// those groups stand for.
///
/// `B` must be wide enough for as many examples as there are of either
/// kind.
fn combine_as<B: ExampleSet>(
    pos_goals: &[usize],
    neg_goals: &[usize],
    ctx: SearchCtx,
) -> Option<Vec<String>> {
    let parallel = ctx.parallel;
    eprintln!("Coverage held in {} bits", B::CAPACITY);

    // What each sub hypothesis proves, then those within the negative noise
    // bound apart from the rest.
    let profiles: Vec<HProfile<B>> = build_profiles(pos_goals, neg_goals, ctx, "sub hypotheses");
    let (kept, rest) = within(profiles, parallel.neg_noise);
    println!(
        "=== Specialisation ===\n{} of {} hypotheses entail {} of the {} negatives",
        kept.len(),
        ctx.hypotheses.len(),
        match parallel.neg_noise {
            0 => "none".to_string(),
            neg_noise => format!("at most {neg_noise}"),
        },
        neg_goals.len(),
    );

    // A positive none of those entails cannot be covered within the bound.
    let profiled = Profiled {
        kept: &kept,
        rest: &rest,
        pos_goals,
        neg_goals,
        ctx,
    };
    let uncovered = uncovered(profiled);
    let dropped = if uncovered.is_empty() {
        B::empty()
    } else if uncovered.count() <= parallel.pos_noise {
        // TODO: refine. Every uncovered positive is left as noise when
        // there are few enough of them, whatever it would take to cover one.
        println!(
            "=== Noise ===\nLeaving {} of the {} positives uncovered as noise (at most {})",
            uncovered.count(),
            pos_goals.len(),
            parallel.pos_noise
        );
        let heap = QueryHeap::new(ctx.heap, None);
        for pos in uncovered.iter() {
            println!("\t{}", heap.term_string(pos_goals[pos]));
        }
        uncovered
    } else {
        let report = uncovered_report(profiled);
        println!("=== Noise ===\n{}", report.text());
        let time_stamp = chrono::Utc::now().format("%d-%m-%Y,%H:%M:%S");
        let path = format!("noise_report_{time_stamp}.md");
        match std::fs::write(&path, report.markdown()) {
            Ok(()) => println!("Noise report written to {path}"),
            Err(error) => eprintln!("Could not write {path}: {error}"),
        }
        println!("No Valid Hypothesis Found");
        return None;
    };

    // Groups of sub hypotheses covering the positives within the bound,
    // going by what each proves alone.
    let candidates = undominated(&kept, parallel.sort_by_literals);
    eprintln!("{} of those are not bettered by another", candidates.len());
    let groups = Search {
        profiles: &candidates,
        n_pos: pos_goals.len(),
        neg_noise: parallel.neg_noise,
        dropped,
        per_start: parallel.final_h_count,
        by_literals: parallel.sort_by_literals,
        branching: BRANCHING_FACTOR,
        max_effort: MAX_EFFORT,
    }
    .run();
    eprintln!("{} groups found", groups.len());

    // The hypotheses those groups stand for, proved, and the best of them.
    let pool = best_of_pool(&groups, &candidates, pos_goals, neg_goals, dropped, ctx);
    eprintln!(
        "{} distinct hypotheses, {} hold up",
        pool.hypotheses.len(),
        pool.held_up
    );
    if pool.best.is_empty() {
        println!(
            "No hypothesis was found covering every positive while entailing at most {} \
             negative(s)",
            parallel.neg_noise
        );
        println!("No Valid Hypothesis Found");
        return None;
    }

    let mut buffer = Vec::new();
    for (i, profile) in pool.best.iter().enumerate() {
        println!("Hypothesis {i}");
        let hypothesis: Vec<&[usize]> = pool.hypotheses.get(profile.h as usize).iter().collect();
        buffer.push(hypothesis_string(
            &hypothesis,
            ctx.heap,
            ctx.predicate_table,
        ));

        if !profile.neg_coverage.is_empty() {
            println!(
                "Entails {} of the {} negatives, taken as noise",
                profile.neg_coverage.count(),
                neg_goals.len()
            );
            let heap = QueryHeap::new(ctx.heap, None);
            for neg in profile.neg_coverage.iter() {
                println!("\t{}", heap.term_string(neg_goals[neg]));
            }
        }
    }
    Some(buffer)
}

/// `hypothesis` as Prolog source, a clause to a line. Printed as well.
fn hypothesis_string(
    hypothesis: &[&[usize]],
    heap: &ProgramHeap,
    predicate_table: &PredicateTable,
) -> String {
    // Clauses are built to be printed, on a scratch heap.
    let mut scratch = QueryHeap::new(heap, None);
    let mut buffer = String::new();
    for clause in hypothesis.clause_strings(&mut scratch, predicate_table) {
        buffer += &clause;
        buffer += "\n";
    }
    println!("\n=== Top Program ({} clauses) ===", hypothesis.len());
    println!("{buffer}");
    buffer
}
