use std::ops::{Deref, DerefMut};

use multiversion::multiversion;
use num_traits::{PrimInt, Unsigned};
use smallvec::SmallVec;

//Return type for binary search of predicate keys
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FindReturn {
    Index(usize),
    InsertPos(usize),
}

/// Compact 64-bit flag set used to mark meta-variables and constrained variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BitFlag16(u16);

impl BitFlag16 {
    pub fn set(&mut self, idx: usize) {
        self.0 = self.0 | 1 << idx;
    }

    pub fn _unset(&mut self, idx: usize) {
        self.0 = self.0 & !(1 << idx);
    }

    pub fn get(&self, idx: usize) -> bool {
        self.0 & (1 << idx) != 0
    }

    pub fn is_some(&self) -> bool {
        self.0 != 0
    }

    pub fn is_none(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Debug)]
pub struct DirGraph8 {
    size: usize,
    edges: [u8; 8],
}
impl Deref for DirGraph8 {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.edges
    }
}
impl DerefMut for DirGraph8 {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.edges
    }
}

impl DirGraph8 {
    pub fn new(size: usize) -> Self {
        Self {
            size,
            edges: [0; 8],
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize) {
        self[from] = self[from] | 1 << to
    }

    pub fn is_edge(&self, from: usize, to: usize) -> bool {
        self[from] & 1 << to != 0
    }

    pub fn closure(&self) -> [u8; 8] {
        let mut r = self.edges;
        for k in 0..8 {
            let row_k = r[k];
            for row in r.iter_mut() {
                // all ones if this row has bit k set, otherwise zero
                let mask = 0u8.wrapping_sub((*row >> k) & 1);
                *row |= row_k & mask;
            }
        }
        r
    }

    /// One bitmask per group of nodes bound together by cycles.
    pub fn cyclic_groups(&self) -> SmallVec<[u8; 4]> {
        let r = self.closure();

        let mut t = [0u8; 8];
        for i in 0..8 {
            for j in 0..8 {
                t[j] |= ((r[i] >> j) & 1) << i;
            }
        }

        let mut assigned = 0u8;
        let mut groups = SmallVec::new();
        for v in 0..self.size {
            let bit = 1u8 << v;
            if r[v] & bit == 0 || assigned & bit != 0 {
                continue;
            }
            let g = r[v] & t[v]; // reachable from v AND reaches v
            assigned |= g;
            groups.push(g);
        }
        groups
    }
}

#[derive(Debug)]
pub struct DirGraph16 {
    size: usize,
    edges: [u16; 16],
}
impl Deref for DirGraph16 {
    type Target = [u16];

    fn deref(&self) -> &Self::Target {
        &self.edges
    }
}
impl DerefMut for DirGraph16 {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.edges
    }
}

impl DirGraph16 {
    fn add_edge(&mut self, from: usize, to: usize) {
        self[from] = self[from] | 1 << to
    }

    fn is_edge(&self, from: usize, to: usize) -> bool {
        self[from] & 1 << to != 0
    }

    pub fn closure(&self) -> [u16; 16] {
        let mut r = self.edges;
        for k in 0..16 {
            let row_k = r[k];
            for row in r.iter_mut() {
                // all ones if this row has bit k set, otherwise zero
                let mask = 0u16.wrapping_sub((*row >> k) & 1);
                *row |= row_k & mask;
            }
        }
        r
    }

    /// One bitmask per group of nodes bound together by cycles.
    pub fn cyclic_groups(&self) -> SmallVec<[u16; 8]> {
        let r = self.closure();

        let mut t = [0u16; 16];
        for i in 0..16 {
            for j in 0..16 {
                t[j] |= ((r[i] >> j) & 1) << i;
            }
        }

        let mut assigned = 0u16;
        let mut groups = SmallVec::new();
        for v in 0..self.size {
            let bit = 1u16 << v;
            if r[v] & bit == 0 || assigned & bit != 0 {
                continue;
            }
            let g = r[v] & t[v]; // reachable from v AND reaches v
            assigned |= g;
            groups.push(g);
        }
        groups
    }
}

pub struct DirGraph<const N: usize, T: PrimInt + Unsigned> {
    size: usize,
    edges: [T; N],
}
impl<const N: usize, T: PrimInt + Unsigned> Deref for DirGraph<N, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.edges
    }
}
impl<const N: usize, T: PrimInt + Unsigned> DerefMut for DirGraph<N, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.edges
    }
}

impl<const N: usize, T: PrimInt + Unsigned> DirGraph<N, T> {
    pub fn add_edge(&mut self, from: usize, to: usize) {
        self[from] = self[from] | T::one() << to
    }

    pub fn is_edge(&self, from: usize, to: usize) -> bool {
        self[from] & T::one() << to != T::zero()
    }
}

/// Column i of the edge table: bit r set iff edge_table[r] has bit i set
#[allow(dead_code)]
fn column(edge_table: &[u16; 16], i: usize) -> u16 {
    (0..16).fold(0, |col, r| col | ((edge_table[r] >> i) & 1) << r)
}

// Without AVX2 this barely vectorizes (~7x slower), so dispatch at runtime
#[multiversion(targets = "simd")]
fn transpose(edge_table: &[u16; 16]) -> [u16; 16] {
    std::array::from_fn(|i| column(edge_table, i))
}

#[cfg(test)]
mod tests {
    use crate::utils::DirGraph8;

    use super::DirGraph16;

    #[test]
    fn example_graph16() {
        let mut g = DirGraph16 {
            size: 4,
            edges: [0; 16],
        };
        g.edges[0] |= 1 << 1; // a -> b
        g.edges[1] |= 1 << 2; // b -> c
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1 << 1; // d -> b
        assert_eq!(g.cyclic_groups().as_slice(), [0b1110]); // {b, c, d}

        let mut g = DirGraph16 {
            size: 4,
            edges: [0; 16],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1 << 3; // b -> d
        g.edges[2] |= 1; // c -> a
        g.edges[3] |= 1 << 1; // d -> b
        assert_eq!(g.cyclic_groups().as_slice(), [0b0101, 0b1010]); // {a,c}, {b,d}

        let mut g = DirGraph16 {
            size: 4,
            edges: [0; 16],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1; // d -> a
        assert_eq!(g.cyclic_groups().as_slice(), [0b1101]); // {a, c, d}
    }

    #[test]
    fn example_graph8() {
        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 1; // a -> b
        g.edges[1] |= 1 << 2; // b -> c
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1 << 1; // d -> b
        assert_eq!(g.cyclic_groups().as_slice(), [0b1110]); // {b, c, d}

        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1 << 3; // b -> d
        g.edges[2] |= 1; // c -> a
        g.edges[3] |= 1 << 1; // d -> b
        assert_eq!(g.cyclic_groups().as_slice(), [0b0101, 0b1010]); // {a,c}, {b,d}

        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1; // d -> a
        assert_eq!(g.cyclic_groups().as_slice(), [0b1101]); // {a, c, d}
    }
}

// /// Row i has bit j set iff edge_table has both i->j and j->i
// fn bidirectional(edge_table: &[u16; 16]) -> [u16; 16] {
//     let t = transpose(edge_table);
//     std::array::from_fn(|i| edge_table[i] & t[i])
// }

// pub fn merge_nodes(&mut self, mut n1: usize, mut n2: usize) {
//     // Guard against n1 greater than n2
//     if n1 > n2 {
//         let temp = n2;
//         n2 = n1;
//         n1 = temp;
//     }
//     // merge rows in edge table
//     self[n1] = self[n1] | self[n2];
//     // update edge to n2 to n1
//     self.replace_edge(n2, n1);
//     // shift table rows down
//     self.edges.copy_within(n2 + 1..self.size, n2);
//     self.remove_column(n2);
//     self.size -= 1;
// }

// /// Every pair (i, j) with i < j and edges i->j and j->i. Self loops are not reported.
// pub fn find_bidirection(&self) -> Vec<(usize, usize)> {
//     let bidir = bidirectional(&self.edges);
//     let in_graph = (1u32 << self.size) - 1;
//     let mut pairs = Vec::new();
//     for i in 0..self.size {
//         // only look above the diagonal so each pair is reported once
//         let mut row = bidir[i] as u32 & in_graph & !((2u32 << i) - 1);
//         while row != 0 {
//             pairs.push((i, row.trailing_zeros() as usize));
//             row &= row - 1;
//         }
//     }
//     pairs
// }

// /// Merge bidirectional nodes until none remain, as merging can create new bidirections.
// /// Returns the merges in the order applied, using the node indexes at the time of each
// /// merge, so they can be replayed with merge_nodes on data kept alongside the graph.
// pub fn merge_bidirections(&mut self) -> Vec<(usize, usize)> {
//     let mut merged = Vec::new();
//     // a merge shifts indexes above n2, so recompute after each one
//     while let Some(&(n1, n2)) = self.find_bidirection().first() {
//         self.merge_nodes(n1, n2);
//         merged.push((n1, n2));
//     }
//     merged
// }

// fn remove_column(&mut self, n: usize) {
//     let low = (1u16 << n) - 1;
//     for row in self.iter_mut() {
//         *row = (*row & low) | ((*row >> 1) & !low);
//     }
// }

// fn replace_edge(&mut self, old: usize, new: usize) {
//     let old = 1 << old;
//     let new = 1 << new;
//     for row in self.iter_mut() {
//         *row = if *row & old != 0 {
//             (*row | new) & !old
//         } else {
//             *row
//         };
//     }
// }
