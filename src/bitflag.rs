//! Sets of small indices, a bit each.
//!
//! [`BitFlag`] is the one interface to them. It is implemented for every
//! unsigned integer, which holds as many indices as it has bits, and for
//! [`BitVec`], which grows to hold any index.
//!
//! The integers share one implementation, written with the bit operators
//! over [`Word`]. [`BitVec`] has its own, which never takes an operand by
//! value.
//!
//! A set holds only the indices put in it. There is no padding convention:
//! whether a set holds all of the first `n` indices is asked with
//! [`BitFlag::is_full`].

// Until the callers move onto it.
#![allow(dead_code)]

use std::ops::{BitAnd, BitOr, Not, Shl};

/// A set of indices.
///
/// The required methods change a set in place or read it. The combining
/// methods that return a new set are provided from those.
pub(crate) trait BitFlag: Clone + PartialEq {
    /// The most indices a set can hold: indices `0..n` for `Some(n)`, any
    /// index for `None`.
    const CAPACITY: Option<usize>;

    /// The set of nothing.
    fn empty() -> Self;

    /// Whether `index` is in the set. An index past the capacity is not.
    fn get(&self, index: usize) -> bool;

    /// Put `index` in the set.
    ///
    /// # Panics
    ///
    /// If `index` is past the capacity.
    fn set(&mut self, index: usize);

    /// Take `index` out of the set.
    fn unset(&mut self, index: usize);

    /// Add everything in `other`.
    fn union_with(&mut self, other: &Self);

    /// Keep only what is also in `other`.
    fn intersect_with(&mut self, other: &Self);

    /// Remove everything in `other`.
    fn difference_with(&mut self, other: &Self);

    /// How many indices are in the set.
    fn count(&self) -> usize;

    /// Whether nothing is in the set.
    fn is_empty(&self) -> bool;

    /// Whether everything in the set is in `other`.
    fn is_subset(&self, other: &Self) -> bool;

    /// The lowest index in the set that is at least `from`.
    fn next_set(&self, from: usize) -> Option<usize>;

    /// The set of indices `0..n`.
    ///
    /// # Panics
    ///
    /// If `n` is more than the capacity.
    fn full(n: usize) -> Self {
        let mut full = Self::empty();
        for index in 0..n {
            full.set(index);
        }
        full
    }

    /// Whether every index in `0..n` is in the set.
    fn is_full(&self, n: usize) -> bool {
        Self::full(n).is_subset(self)
    }

    /// Everything in either set.
    fn union(&self, other: &Self) -> Self {
        let mut union = self.clone();
        union.union_with(other);
        union
    }

    /// Everything in both sets.
    fn intersection(&self, other: &Self) -> Self {
        let mut intersection = self.clone();
        intersection.intersect_with(other);
        intersection
    }

    /// Everything in this set that is not in `other`.
    fn difference(&self, other: &Self) -> Self {
        let mut difference = self.clone();
        difference.difference_with(other);
        difference
    }

    /// How many indices are in this set and not in `other`.
    fn difference_count(&self, other: &Self) -> usize {
        self.difference(other).count()
    }

    /// The indices in the set, lowest first.
    fn iter(&self) -> Iter<'_, Self> {
        Iter {
            flags: self,
            from: 0,
        }
    }

    /// The set of `indices`.
    ///
    /// # Panics
    ///
    /// If one is past the capacity.
    fn from_indices(indices: impl IntoIterator<Item = usize>) -> Self {
        let mut flags = Self::empty();
        for index in indices {
            flags.set(index);
        }
        flags
    }
}

/// The indices of a [`BitFlag`], lowest first.
pub(crate) struct Iter<'a, B> {
    flags: &'a B,
    from: usize,
}

impl<B: BitFlag> Iterator for Iter<'_, B> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let index = self.flags.next_set(self.from)?;
        self.from = index + 1;
        Some(index)
    }
}

/// An unsigned integer, as [`BitFlag`] needs it.
///
/// The bit operators come from the standard traits. The required items are
/// what no standard trait gives, and the provided ones are built from both.
///
/// `BitFlag` is implemented for every `Word` at once. Being this crate's own
/// trait, the compiler knows what does not implement it, which is what lets
/// [`BitVec`] have an implementation of its own beside that one.
pub(crate) trait Word:
    Copy
    + Eq
    + Default
    + From<u8>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + Not<Output = Self>
    + Shl<usize, Output = Self>
{
    /// Bits in the integer.
    const BITS: usize;

    /// How many bits are set.
    fn ones(self) -> usize;

    /// Index of the lowest set bit; [`Self::BITS`] if there is none.
    fn lowest(self) -> usize;

    /// The word with only bit `index` set. `index` must be below
    /// [`Self::BITS`].
    fn bit(index: usize) -> Self {
        Self::from(1) << index
    }

    /// The word with every bit from `from` up set; none if `from` is past
    /// them.
    fn bits_from(from: usize) -> Self {
        if from < Self::BITS {
            !Self::default() << from
        } else {
            Self::default()
        }
    }
}

macro_rules! impl_word {
    ($($word:ty),*) => {$(
        impl Word for $word {
            const BITS: usize = <$word>::BITS as usize;

            fn ones(self) -> usize {
                self.count_ones() as usize
            }

            fn lowest(self) -> usize {
                self.trailing_zeros() as usize
            }
        }
    )*};
}
impl_word!(u8, u16, u32, u64, u128);

impl<W: Word> BitFlag for W {
    const CAPACITY: Option<usize> = Some(W::BITS);

    fn empty() -> Self {
        W::default()
    }

    fn get(&self, index: usize) -> bool {
        index < W::BITS && *self & W::bit(index) != W::default()
    }

    fn set(&mut self, index: usize) {
        assert!(
            index < W::BITS,
            "index {index} is past the {} a set of this width holds",
            W::BITS
        );
        *self = *self | W::bit(index);
    }

    fn unset(&mut self, index: usize) {
        if index < W::BITS {
            *self = *self & !W::bit(index);
        }
    }

    fn union_with(&mut self, other: &Self) {
        *self = *self | *other;
    }

    fn intersect_with(&mut self, other: &Self) {
        *self = *self & *other;
    }

    fn difference_with(&mut self, other: &Self) {
        *self = *self & !*other;
    }

    fn count(&self) -> usize {
        self.ones()
    }

    fn is_empty(&self) -> bool {
        *self == W::default()
    }

    fn is_subset(&self, other: &Self) -> bool {
        *self & !*other == W::default()
    }

    fn next_set(&self, from: usize) -> Option<usize> {
        let rest = *self & W::bits_from(from);
        (rest != W::default()).then(|| rest.lowest())
    }

    fn full(n: usize) -> Self {
        assert!(
            n <= W::BITS,
            "{n} indices are more than the {} a set of this width holds",
            W::BITS
        );
        !W::bits_from(n)
    }

    fn difference_count(&self, other: &Self) -> usize {
        (*self & !*other).ones()
    }
}

/// A set of indices of any size, 64 to a word.
///
/// The last word is never zero, so equal sets are equal word for word.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BitVec {
    words: Vec<u64>,
}

impl BitVec {
    const WORD: usize = u64::BITS as usize;

    /// Restore the invariant: drop the zero words at the end.
    fn trim(&mut self) {
        while self.words.last() == Some(&0) {
            self.words.pop();
        }
    }

    /// Word `i`, zero past the end.
    fn word(&self, i: usize) -> u64 {
        self.words.get(i).copied().unwrap_or(0)
    }
}

impl BitFlag for BitVec {
    const CAPACITY: Option<usize> = None;

    fn empty() -> Self {
        Self::default()
    }

    fn get(&self, index: usize) -> bool {
        self.word(index / Self::WORD) & 1 << (index % Self::WORD) != 0
    }

    fn set(&mut self, index: usize) {
        let word = index / Self::WORD;
        if self.words.len() <= word {
            self.words.resize(word + 1, 0);
        }
        self.words[word] |= 1 << (index % Self::WORD);
    }

    fn unset(&mut self, index: usize) {
        if let Some(word) = self.words.get_mut(index / Self::WORD) {
            *word &= !(1 << (index % Self::WORD));
            self.trim();
        }
    }

    fn union_with(&mut self, other: &Self) {
        if self.words.len() < other.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (word, other) in self.words.iter_mut().zip(&other.words) {
            *word |= other;
        }
    }

    fn intersect_with(&mut self, other: &Self) {
        self.words.truncate(other.words.len());
        for (word, other) in self.words.iter_mut().zip(&other.words) {
            *word &= other;
        }
        self.trim();
    }

    fn difference_with(&mut self, other: &Self) {
        for (word, other) in self.words.iter_mut().zip(&other.words) {
            *word &= !other;
        }
        self.trim();
    }

    fn count(&self) -> usize {
        self.words
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum()
    }

    fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    fn is_subset(&self, other: &Self) -> bool {
        // A longer set has an index the shorter cannot: its last word is
        // not zero.
        self.words.len() <= other.words.len()
            && self
                .words
                .iter()
                .zip(&other.words)
                .all(|(word, other)| word & !other == 0)
    }

    fn next_set(&self, from: usize) -> Option<usize> {
        let first = from / Self::WORD;
        // Of the first word, only the bits from `from` up.
        let mut mask = u64::MAX << (from % Self::WORD);
        for (i, word) in self.words.iter().enumerate().skip(first) {
            let rest = word & mask;
            if rest != 0 {
                return Some(i * Self::WORD + rest.trailing_zeros() as usize);
            }
            mask = u64::MAX;
        }
        None
    }

    fn difference_count(&self, other: &Self) -> usize {
        self.words
            .iter()
            .enumerate()
            .map(|(i, word)| (word & !other.word(i)).count_ones() as usize)
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, fmt::Debug};

    use super::{BitFlag, BitVec};

    /// The set a `BitFlag` should agree with.
    type Model = BTreeSet<usize>;

    fn model<B: BitFlag>(flags: &B) -> Model {
        flags.iter().collect()
    }

    /// Indices to test with: every one a `u8` holds, and for a wider set
    /// those either side of each word boundary up to its capacity (300 for
    /// one with none).
    fn indices<B: BitFlag>() -> Vec<usize> {
        let limit = B::CAPACITY.unwrap_or(300);
        let mut indices: Vec<usize> = (0..8).collect();
        for boundary in [16, 32, 64, 128, 192, 256, 300] {
            indices.extend([boundary - 1, boundary]);
        }
        indices.retain(|&index| index < limit);
        indices
    }

    /// A stream of numbers that is the same every run.
    fn numbers() -> impl Iterator<Item = usize> {
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        std::iter::repeat_with(move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) as usize
        })
    }

    /// Every operation of `B` against the same operation on a [`Model`],
    /// over sets made by a fixed run of sets and unsets.
    fn agrees_with_the_model<B: BitFlag + Debug>() {
        let indices = indices::<B>();
        let mut numbers = numbers();
        let mut pick = |n: usize| numbers.next().unwrap() % n;

        let (mut a, mut b) = (B::empty(), B::empty());
        let (mut model_a, mut model_b) = (Model::new(), Model::new());
        assert!(a.is_empty() && a.count() == 0 && a.next_set(0).is_none());

        for _ in 0..400 {
            // Change one of the two sets by one index.
            let index = indices[pick(indices.len())];
            let (flags, model_flags) = match pick(2) {
                0 => (&mut a, &mut model_a),
                _ => (&mut b, &mut model_b),
            };
            if pick(3) == 0 {
                flags.unset(index);
                model_flags.remove(&index);
            } else {
                flags.set(index);
                model_flags.insert(index);
            }

            // Reading.
            assert_eq!(model(&a), model_a);
            assert_eq!(model(&b), model_b);
            assert_eq!(a.count(), model_a.len());
            assert_eq!(a.is_empty(), model_a.is_empty());
            for &index in &indices {
                assert_eq!(a.get(index), model_a.contains(&index), "get {index}");
                assert_eq!(
                    a.next_set(index),
                    model_a.range(index..).next().copied(),
                    "next_set {index}"
                );
            }

            // Combining, as new sets and in place.
            let set = |model: Model| B::from_indices(model);
            assert_eq!(a.union(&b), set(&model_a | &model_b));
            assert_eq!(a.intersection(&b), set(&model_a & &model_b));
            assert_eq!(a.difference(&b), set(&model_a - &model_b));
            assert_eq!(a.difference_count(&b), (&model_a - &model_b).len());
            assert_eq!(a.is_subset(&b), model_a.is_subset(&model_b));
            assert_eq!(b.is_subset(&a), model_b.is_subset(&model_a));
            let mut in_place = a.clone();
            in_place.union_with(&b);
            in_place.difference_with(&b);
            assert_eq!(in_place, set(&model_a - &model_b));

            // Equal sets are equal however they were made.
            assert_eq!(a, set(model_a.clone()));
            assert_eq!(a == b, model_a == model_b);
        }
    }

    #[test]
    fn every_width_agrees_with_the_model() {
        agrees_with_the_model::<u8>();
        agrees_with_the_model::<u16>();
        agrees_with_the_model::<u32>();
        agrees_with_the_model::<u64>();
        agrees_with_the_model::<u128>();
        agrees_with_the_model::<BitVec>();
    }

    /// `full(n)` is the indices `0..n` and nothing else, and `is_full(n)`
    /// asks for exactly those, at every `n` the set can hold.
    fn full_is_the_first_n<B: BitFlag + Debug>() {
        let limit = B::CAPACITY.unwrap_or(200);
        for n in 0..=limit {
            let full = B::full(n);
            assert_eq!(full.count(), n, "full({n})");
            assert_eq!(model(&full), (0..n).collect::<Model>());
            assert!(full.is_full(n));
            // A set with more than the first `n` is still full of them.
            assert!(B::full(limit).is_full(n));
            if n > 0 {
                assert!(!B::full(n - 1).is_full(n));
                let mut missing_one = full.clone();
                missing_one.unset(n / 2);
                assert!(!missing_one.is_full(n));
            }
        }
    }

    #[test]
    fn full_is_the_first_n_at_every_width() {
        full_is_the_first_n::<u8>();
        full_is_the_first_n::<u16>();
        full_is_the_first_n::<u32>();
        full_is_the_first_n::<u64>();
        full_is_the_first_n::<u128>();
        full_is_the_first_n::<BitVec>();
    }

    #[test]
    fn the_integers_hold_as_many_indices_as_they_have_bits() {
        assert_eq!(<u8 as BitFlag>::CAPACITY, Some(8));
        assert_eq!(<u128 as BitFlag>::CAPACITY, Some(128));
        assert_eq!(<BitVec as BitFlag>::CAPACITY, None);

        // The top bit is an index like any other.
        let mut flags = 0u8;
        BitFlag::set(&mut flags, 7);
        assert_eq!(flags, 0b1000_0000);
        assert_eq!(flags.next_set(0), Some(7));

        // Past the capacity nothing is in the set, and nothing is found.
        assert!(!BitFlag::get(&u8::MAX, 8));
        assert_eq!(u8::MAX.next_set(8), None);
        let mut unchanged = u8::MAX;
        unchanged.unset(8);
        assert_eq!(unchanged, u8::MAX);
    }

    #[test]
    #[should_panic(expected = "index 8 is past the 8")]
    fn setting_past_an_integers_capacity_panics() {
        let mut flags = 0u8;
        BitFlag::set(&mut flags, 8);
    }

    #[test]
    #[should_panic(expected = "9 indices are more than the 8")]
    fn filling_past_an_integers_capacity_panics() {
        let _ = <u8 as BitFlag>::full(9);
    }

    /// Taking out the highest indices leaves no empty words behind, so the
    /// set equals one that never held them.
    #[test]
    fn a_bit_vec_shrinks_back() {
        let mut flags = BitVec::from_indices([3, 700]);
        flags.unset(700);
        assert_eq!(flags, BitVec::from_indices([3]));
        flags.unset(3);
        assert_eq!(flags, BitVec::empty());
        assert!(flags.is_empty());

        let high = BitVec::from_indices([700]);
        let mut low = BitVec::from_indices([3, 700]);
        low.difference_with(&high);
        assert_eq!(low, BitVec::from_indices([3]));
        let mut both = BitVec::from_indices([3, 700]);
        both.intersect_with(&BitVec::from_indices([3]));
        assert_eq!(both, BitVec::from_indices([3]));
    }

    /// Sets of different lengths combine as if the shorter were padded.
    #[test]
    fn bit_vecs_of_different_lengths_combine() {
        let short = BitVec::from_indices([1]);
        let long = BitVec::from_indices([1, 500]);
        assert!(short.is_subset(&long));
        assert!(!long.is_subset(&short));
        assert_eq!(short.union(&long), long);
        assert_eq!(long.union(&short), long);
        assert_eq!(long.intersection(&short), short);
        assert_eq!(long.difference_count(&short), 1);
        assert_eq!(short.difference_count(&long), 0);
        assert_eq!(long.iter().collect::<Vec<_>>(), vec![1, 500]);
    }
}
