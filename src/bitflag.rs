//! Sets of small indices, a bit each.
//!
//! [`BitFlag`] is the one interface to them. It is implemented for every
//! unsigned integer, which holds as many indices as it has bits, and for
//! every array of them, which holds as many as its integers do together:
//! `[u128; 8]` holds 1024.
//!
//! An implementor only says how it is seen as a slice of [`Word`]s. Every
//! operation is written once, in the trait, over those slices.
//!
//! A set holds only the indices put in it. There is no padding convention:
//! whether a set holds all of the first `n` indices is asked with
//! [`BitFlag::is_full`].

use std::ops::{BitAnd, BitOr, Not, Shl};

/// A set of indices below [`Self::CAPACITY`].
// The whole interface: not every operation has a caller yet.
#[allow(dead_code)]
pub(crate) trait BitFlag: Copy + PartialEq {
    /// The integer the set is made of.
    type Word: Word;

    /// How many indices the set can hold: `0..CAPACITY`.
    const CAPACITY: usize;

    /// The set of nothing.
    fn empty() -> Self;

    /// The set as its words, the lowest indices first.
    fn words(&self) -> &[Self::Word];

    /// As [`Self::words`], to change.
    fn words_mut(&mut self) -> &mut [Self::Word];

    /// Whether `index` is in the set. An index past the capacity is not.
    fn get(&self, index: usize) -> bool {
        let (word, bit) = position::<Self>(index);
        self.words()
            .get(word)
            .is_some_and(|word| *word & bit != zero::<Self>())
    }

    /// Put `index` in the set.
    ///
    /// # Panics
    ///
    /// If `index` is past the capacity.
    fn set(&mut self, index: usize) {
        assert!(
            index < Self::CAPACITY,
            "index {index} is past the {} a set of this width holds",
            Self::CAPACITY
        );
        let (word, bit) = position::<Self>(index);
        let word = &mut self.words_mut()[word];
        *word = *word | bit;
    }

    /// Take `index` out of the set.
    fn unset(&mut self, index: usize) {
        let (word, bit) = position::<Self>(index);
        if let Some(word) = self.words_mut().get_mut(word) {
            *word = *word & !bit;
        }
    }

    /// Add everything in `other`.
    fn union_with(&mut self, other: &Self) {
        for (word, other) in self.words_mut().iter_mut().zip(other.words()) {
            *word = *word | *other;
        }
    }

    /// Keep only what is also in `other`.
    fn intersect_with(&mut self, other: &Self) {
        for (word, other) in self.words_mut().iter_mut().zip(other.words()) {
            *word = *word & *other;
        }
    }

    /// Remove everything in `other`.
    fn difference_with(&mut self, other: &Self) {
        for (word, other) in self.words_mut().iter_mut().zip(other.words()) {
            *word = *word & !*other;
        }
    }

    /// How many indices are in the set.
    fn count(&self) -> usize {
        self.words().iter().map(|word| word.ones()).sum()
    }

    /// Whether nothing is in the set.
    fn is_empty(&self) -> bool {
        self.words().iter().all(|word| *word == zero::<Self>())
    }

    /// Whether everything in the set is in `other`.
    fn is_subset(&self, other: &Self) -> bool {
        self.words()
            .iter()
            .zip(other.words())
            .all(|(word, other)| *word & !*other == zero::<Self>())
    }

    /// The lowest index in the set that is at least `from`.
    fn next_set(&self, from: usize) -> Option<usize> {
        let bits = Self::Word::BITS;
        // Of the first word looked at, only the bits from `from` up.
        let mut mask = Self::Word::bits_from(from % bits);
        for (i, word) in self.words().iter().enumerate().skip(from / bits) {
            let rest = *word & mask;
            if rest != zero::<Self>() {
                return Some(i * bits + rest.lowest());
            }
            mask = !zero::<Self>();
        }
        None
    }

    /// The set of indices `0..n`.
    ///
    /// # Panics
    ///
    /// If `n` is more than the capacity.
    fn full(n: usize) -> Self {
        assert!(
            n <= Self::CAPACITY,
            "{n} indices are more than the {} a set of this width holds",
            Self::CAPACITY
        );
        let bits = Self::Word::BITS;
        let mut full = Self::empty();
        for (i, word) in full.words_mut().iter_mut().enumerate() {
            // How many of the `n` fall in this word: all of it, part, none.
            let in_word = n.saturating_sub(i * bits);
            *word = !Self::Word::bits_from(in_word);
        }
        full
    }

    /// Whether every index in `0..n` is in the set. Never, for more than
    /// the capacity.
    fn is_full(&self, n: usize) -> bool {
        n <= Self::CAPACITY && Self::full(n).is_subset(self)
    }

    /// Everything in either set.
    fn union(&self, other: &Self) -> Self {
        let mut union = *self;
        union.union_with(other);
        union
    }

    /// Everything in both sets.
    fn intersection(&self, other: &Self) -> Self {
        let mut intersection = *self;
        intersection.intersect_with(other);
        intersection
    }

    /// Everything in this set that is not in `other`.
    fn difference(&self, other: &Self) -> Self {
        let mut difference = *self;
        difference.difference_with(other);
        difference
    }

    /// How many indices are in this set and not in `other`.
    fn difference_count(&self, other: &Self) -> usize {
        self.words()
            .iter()
            .zip(other.words())
            .map(|(word, other)| (*word & !*other).ones())
            .sum()
    }

    /// The indices in the set, lowest first.
    fn iter(&self) -> Iter<'_, Self> {
        Iter {
            flags: self,
            from: 0,
        }
    }

    /// The indices in the set as a list, lowest first.
    fn indices(&self) -> Vec<usize> {
        self.iter().collect()
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

/// The word of no bits.
fn zero<B: BitFlag>() -> B::Word {
    B::Word::default()
}

/// Where `index` is held: which word, and the bit of it.
fn position<B: BitFlag>(index: usize) -> (usize, B::Word) {
    let bits = B::Word::BITS;
    (index / bits, B::Word::bit(index % bits))
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
/// trait, the compiler knows an array is not one, which is what lets the
/// arrays have an implementation beside that one.
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

/// One integer: a set of as many indices as it has bits.
impl<W: Word> BitFlag for W {
    type Word = W;

    const CAPACITY: usize = W::BITS;

    fn empty() -> Self {
        W::default()
    }

    fn words(&self) -> &[W] {
        std::slice::from_ref(self)
    }

    fn words_mut(&mut self) -> &mut [W] {
        std::slice::from_mut(self)
    }
}

/// Several integers: a set of as many indices as they have bits together.
impl<W: Word, const N: usize> BitFlag for [W; N] {
    type Word = W;

    const CAPACITY: usize = W::BITS * N;

    fn empty() -> Self {
        [W::default(); N]
    }

    fn words(&self) -> &[W] {
        self
    }

    fn words_mut(&mut self) -> &mut [W] {
        self
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, fmt::Debug};

    use super::BitFlag;

    /// The set a `BitFlag` should agree with.
    type Model = BTreeSet<usize>;

    fn model<B: BitFlag>(flags: &B) -> Model {
        flags.iter().collect()
    }

    /// Indices to test with: every one a `u8` holds, and for a wider set
    /// those either side of each word boundary up to its capacity.
    fn indices<B: BitFlag>() -> Vec<usize> {
        let mut indices: Vec<usize> = (0..8).collect();
        for boundary in [16, 32, 64, 128, 192, 256, 512, 1024] {
            indices.extend([boundary - 1, boundary]);
        }
        indices.retain(|&index| index < B::CAPACITY);
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
            let mut in_place = a;
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
        agrees_with_the_model::<[u8; 1]>();
        agrees_with_the_model::<[u64; 3]>();
        agrees_with_the_model::<[u128; 2]>();
        agrees_with_the_model::<[u128; 8]>();
    }

    /// `full(n)` is the indices `0..n` and nothing else, and `is_full(n)`
    /// asks for exactly those, at every `n` the set can hold.
    fn full_is_the_first_n<B: BitFlag + Debug>() {
        for n in 0..=B::CAPACITY {
            let full = B::full(n);
            assert_eq!(full.count(), n, "full({n})");
            assert_eq!(model(&full), (0..n).collect::<Model>());
            assert!(full.is_full(n));
            // A set with more than the first `n` is still full of them.
            assert!(B::full(B::CAPACITY).is_full(n));
            if n > 0 {
                assert!(!B::full(n - 1).is_full(n));
                let mut missing_one = full;
                missing_one.unset(n / 2);
                assert!(!missing_one.is_full(n));
            }
        }
        // More than it can hold is never all there.
        assert!(!B::full(B::CAPACITY).is_full(B::CAPACITY + 1));
    }

    #[test]
    fn full_is_the_first_n_at_every_width() {
        full_is_the_first_n::<u8>();
        full_is_the_first_n::<u16>();
        full_is_the_first_n::<u32>();
        full_is_the_first_n::<u64>();
        full_is_the_first_n::<u128>();
        full_is_the_first_n::<[u8; 1]>();
        full_is_the_first_n::<[u64; 3]>();
        full_is_the_first_n::<[u128; 2]>();
        full_is_the_first_n::<[u128; 8]>();
    }

    #[test]
    fn a_set_holds_as_many_indices_as_it_has_bits() {
        assert_eq!(<u8 as BitFlag>::CAPACITY, 8);
        assert_eq!(<u128 as BitFlag>::CAPACITY, 128);
        assert_eq!(<[u64; 3] as BitFlag>::CAPACITY, 192);
        assert_eq!(<[u128; 8] as BitFlag>::CAPACITY, 1024);

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

    /// An index is held in the word it falls in, lowest words first.
    #[test]
    fn an_array_holds_an_index_in_the_word_it_falls_in() {
        let flags = <[u64; 3]>::from_indices([0, 63, 64, 191]);
        assert_eq!(flags, [1 | 1 << 63, 1, 1 << 63]);
        assert_eq!(flags.iter().collect::<Vec<_>>(), vec![0, 63, 64, 191]);

        // One word in an array is the word.
        assert_eq!(
            <[u64; 1]>::from_indices([5, 40])[0],
            u64::from_indices([5, 40])
        );
    }

    #[test]
    #[should_panic(expected = "index 8 is past the 8")]
    fn setting_past_an_integers_capacity_panics() {
        let mut flags = 0u8;
        BitFlag::set(&mut flags, 8);
    }

    #[test]
    #[should_panic(expected = "index 256 is past the 256")]
    fn setting_past_an_arrays_capacity_panics() {
        let mut flags = [0u128; 2];
        flags.set(256);
    }

    #[test]
    #[should_panic(expected = "9 indices are more than the 8")]
    fn filling_past_the_capacity_panics() {
        let _ = <u8 as BitFlag>::full(9);
    }
}
