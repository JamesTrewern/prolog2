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

#[derive(Debug, PartialEq, Eq)]
pub struct DirGraph8 {
    pub size: usize,
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

fn row_to_string(row: u8, size: usize) -> String {
    let mut buf = String::from("|");
    for i in 0..size {
        if row & 1 << i != 0 {
            buf += "1|";
        } else {
            buf += "0|";
        }
    }
    buf
}

fn print_table(table: [u8; 8], size: usize) {
    println!("{:-<1$}", "", size * 2 + 1);
    for i in 0..size {
        println!("{}", row_to_string(table[i], size))
    }
    println!("{:-<1$}", "", size * 2 + 1);
}

impl DirGraph8 {
    const IDENTITYB: [u8; 8] = [
        0b00000001, 0b00000010, 0b00000100, 0b00001000, 0b00010000, 0b00100000, 0b01000000,
        0b10000000,
    ];

    const IDENTITY64: u64 = u64::from_ne_bytes(Self::IDENTITYB);

    fn from_edges<const N: usize>(edge_rows: [u8; N]) -> Self {
        if N > 8 {
            panic!("Can't have more than 8 nodes")
        }
        let mut edges = [0; 8];
        for (i, &row) in edge_rows.iter().enumerate() {
            edges[i] = row
        }
        Self { size: N, edges }
    }

    pub fn new(size: usize) -> Self {
        Self {
            size,
            edges: [0; 8],
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize) {
        self[from] = self[from] | 1 << to
    }

    fn closure(&self) -> [u8; 8] {
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
    /// Returns grouping as slice with size 8 and length
    /// If no SCC groups return none
    pub fn cyclic_groups(&self) -> Option<(Self, Self)> {
        let r = self.closure();
        //No Groups
        if u64::from_ne_bytes(r) & Self::IDENTITY64 == 0 {
            return None;
        }

        let rt = transpose8(r);

        // let grouped: [u8; 8] = std::array::from_fn(|i| (r[i] & rt[i]) | Self::IDENTITYB[i]);
        let grouped =
            (u64::from_ne_bytes(r) & u64::from_ne_bytes(rt) | Self::IDENTITY64).to_ne_bytes();

        let mut assigned: u8 = 0;
        let mut groups = [0; 8];
        let mut gd = [0; 8];
        let mut size = 0;
        let mut reps: u8 = 0;

        for i in 0..self.size {
            let bit = 1u8 << i;
            if assigned & bit != 0 {
                continue;
            }
            assigned |= grouped[i];
            groups[size] = grouped[i];
            gd[size] = r[i];
            size += 1;
            reps |= bit;
            if assigned == u8::MAX {
                break;
            }
        }

        const LSB: u64 = 0x0101_0101_0101_0101;

        let x = u64::from_le_bytes(gd);
        let mut out = 0u64;
        let mut j = 0;
        while reps != 0 {
            // bit `rep` of every row -> bit `j` of every row
            out |= ((x >> reps.trailing_zeros()) & LSB) << j;
            j += 1;
            reps &= reps - 1;
        }
        let new_edges = (out & !Self::IDENTITY64).to_le_bytes();

        Some((
            Self {
                size,
                edges: groups,
            },
            Self {
                size,
                edges: new_edges,
            },
        ))
    }

    pub fn ordered_cyclic_groups(&self) -> Option<Self> {
        let mut r = self.closure();
        //No Groups
        if u64::from_ne_bytes(r) & Self::IDENTITY64 == 0 {
            return None;
        }

        let rt = transpose8(r);

        // let grouped: [u8; 8] = std::array::from_fn(|i| (r[i] & rt[i]) | Self::IDENTITYB[i]);
        let grouped =
            (u64::from_ne_bytes(r) & u64::from_ne_bytes(rt) | Self::IDENTITY64).to_ne_bytes();

        r = (u64::from_ne_bytes(r) & !Self::IDENTITY64).to_ne_bytes();

        let mut assigned: u8 = 0;
        let mut groups_r = [(0, 0); 8];
        let mut size = 0;
        let mut reps: u8 = 0;

        for i in 0..self.size {
            let bit = 1u8 << i;
            if assigned & bit != 0 {
                continue;
            }
            assigned |= grouped[i];
            groups_r[size] = (grouped[i], r[i]);
            size += 1;
            reps |= bit;
            if assigned == u8::MAX {
                break;
            }
        }

        for row in groups_r.iter_mut() {
            //one bit set per group
            row.1 &= reps;
            //count edges to groups
            row.1 = row.1.count_zeros() as u8
        }

        groups_r[..size].sort_unstable_by_key(|&(_, c)| c);
        let groups: [u8; 8] = groups_r.map(|(g, _)| g);
        Some(Self {
            edges: groups,
            size,
        })
    }

    pub fn order(&self) -> [usize; 8] {
        let r = self.closure();
        let mut order: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        order[..self.size].sort_by_key(|&i| std::cmp::Reverse(r[i].count_ones()));
        order
    }

    fn print_table(&self) {
        print_table(self.edges, self.size);
    }
}

#[derive(Debug, PartialEq, Eq)]
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
    /// Identity matrix as (rows 0..8, rows 8..16), laid out as in `to_halves`
    const IDENTITY: (u128, u128) = {
        let (mut a, mut b) = (0u128, 0u128);
        let mut i = 0;
        while i < 8 {
            a |= 1 << (17 * i);
            b |= 1 << (17 * i + 8);
            i += 1;
        }
        (a, b)
    };

    fn from_edges<const N: usize>(edge_rows: [u16; N]) -> Self {
        if N > 16 {
            panic!("Can't have more than 16 nodes")
        }
        let mut edges = [0; 16];
        for (i, &row) in edge_rows.iter().enumerate() {
            edges[i] = row
        }
        Self { size: N, edges }
    }

    pub fn new(size: usize) -> Self {
        Self {
            size,
            edges: [0; 16],
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize) {
        self[from] = self[from] | 1 << to
    }

    fn closure(&self) -> [u16; 16] {
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
    /// Returns the groups and the edges between groups, each sized to the number of groups.
    /// If no SCC groups return none
    pub fn cyclic_groups(&self) -> Option<(Self, Self)> {
        let r = self.closure();
        let (ra, rb) = to_halves(r);
        let (ia, ib) = Self::IDENTITY;
        //No Groups
        if (ra & ia) | (rb & ib) == 0 {
            return None;
        }

        let (ta, tb) = to_halves(transpose16(r));
        let grouped = from_halves(ra & ta | ia, rb & tb | ib);

        let mut assigned: u16 = 0;
        let mut groups = [0; 16];
        let mut gd = [0; 16];
        let mut size = 0;
        let mut reps: u16 = 0;

        for i in 0..self.size {
            let bit = 1u16 << i;
            if assigned & bit != 0 {
                continue;
            }
            assigned |= grouped[i];
            groups[size] = grouped[i];
            gd[size] = r[i];
            size += 1;
            reps |= bit;
            if assigned == u16::MAX {
                break;
            }
        }

        const LSB: u128 = 0x0001_0001_0001_0001_0001_0001_0001_0001;

        let (xa, xb) = to_halves(gd);
        let (mut oa, mut ob) = (0u128, 0u128);
        let mut j = 0;
        while reps != 0 {
            // bit `rep` of every row -> bit `j` of every row
            let rep = reps.trailing_zeros();
            oa |= ((xa >> rep) & LSB) << j;
            ob |= ((xb >> rep) & LSB) << j;
            j += 1;
            reps &= reps - 1;
        }
        let new_edges = from_halves(oa & !ia, ob & !ib);

        Some((
            Self {
                size,
                edges: groups,
            },
            Self {
                size,
                edges: new_edges,
            },
        ))
    }
}

fn transpose8(m: [u8; 8]) -> [u8; 8] {
    let mut x = u64::from_le_bytes(m);
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^= t ^ (t << 28);
    x.to_le_bytes()
}

fn transpose16(m: [u16; 16]) -> [u16; 16] {
    let (mut a, mut b) = to_halves(m);

    // Swap within each half: 1×1, 2×2 and 4×4 sub-blocks
    for x in [&mut a, &mut b] {
        let t = (*x ^ (*x >> 15)) & 0x0000AAAA_0000AAAA_0000AAAA_0000AAAA;
        *x ^= t ^ (t << 15);
        let t = (*x ^ (*x >> 30)) & 0x00000000_CCCCCCCC_00000000_CCCCCCCC;
        *x ^= t ^ (t << 30);
        let t = (*x ^ (*x >> 60)) & 0x00000000_00000000_F0F0F0F0_F0F0F0F0;
        *x ^= t ^ (t << 60);
    }

    // Swap 8×8 blocks across halves: high byte of a's rows <-> low byte of b's rows
    let t = ((a >> 8) ^ b) & 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF;
    a ^= t << 8;
    b ^= t;

    from_halves(a, b)
}

/// Split 16 rows into (rows 0..8, rows 8..16), with row i at bits 16i..16i+16 of its half
fn to_halves(m: [u16; 16]) -> (u128, u128) {
    let pack = |rows: &[u16]| {
        rows.iter()
            .enumerate()
            .fold(0u128, |acc, (i, &r)| acc | (r as u128) << (16 * i))
    };
    (pack(&m[..8]), pack(&m[8..]))
}

fn from_halves(a: u128, b: u128) -> [u16; 16] {
    std::array::from_fn(|i| {
        if i < 8 {
            (a >> (16 * i)) as u16
        } else {
            (b >> (16 * (i - 8))) as u16
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::utils::{print_table, DirGraph8};

    use super::DirGraph16;

    #[test]
    fn cycle_groups_graph16() {
        let mut g = DirGraph16::new(4);
        g.add_edge(0, 1); // a -> b
        g.add_edge(1, 2); // b -> c
        g.add_edge(2, 3); // c -> d
        g.add_edge(3, 1); // d -> b
        let (groups, new_edges) = g.cyclic_groups().unwrap();
        assert_eq!(groups, DirGraph16::from_edges([0b0001, 0b1110])); // {a}, {b, c, d}
        assert_eq!(new_edges, DirGraph16::from_edges([0b10, 0b00]));

        let mut g = DirGraph16::new(4);
        g.add_edge(0, 2); // a -> c
        g.add_edge(1, 3); // b -> d
        g.add_edge(2, 0); // c -> a
        g.add_edge(3, 1); // d -> b
        let (groups, new_edges) = g.cyclic_groups().unwrap();
        assert_eq!(groups, DirGraph16::from_edges([0b0101, 0b1010])); // {a, c}, {b, d}
        assert_eq!(new_edges, DirGraph16::from_edges([0b00, 0b00]));

        let mut g = DirGraph16::new(4);
        g.add_edge(0, 1); // a -> b
        g.add_edge(1, 2); // b -> c
        assert_eq!(g.cyclic_groups(), None);
    }

    #[test]
    fn group_sccs_16_across_halves() {
        let mut g = DirGraph16::new(12);
        g.add_edge(1, 9); // cycle {1, 9, 10}
        g.add_edge(9, 10);
        g.add_edge(10, 1);
        g.add_edge(3, 11); // cycle {3, 11}
        g.add_edge(11, 3);
        g.add_edge(0, 1);
        g.add_edge(10, 3);

        let (groups, new_edges) = g.cyclic_groups().unwrap();

        let ex_groups = DirGraph16::from_edges([
            1 << 0,
            1 << 1 | 1 << 9 | 1 << 10,
            1 << 2,
            1 << 3 | 1 << 11,
            1 << 4,
            1 << 5,
            1 << 6,
            1 << 7,
            1 << 8,
        ]);
        let exp_new_edges = DirGraph16::from_edges([0b1010, 0b1000, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(groups, ex_groups);
        assert_eq!(new_edges, exp_new_edges);
    }

    #[test]
    fn graph16_matches_graph8() {
        let mut s: u64 = 0x9E3779B97F4A7C15;
        let mut rnd = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for _ in 0..10_000 {
            let n = (rnd() % 8 + 1) as usize;
            let (mut g8, mut g16) = (DirGraph8::new(n), DirGraph16::new(n));
            for from in 0..n {
                for to in 0..n {
                    if rnd() % 4 == 0 {
                        g8.add_edge(from, to);
                        g16.add_edge(from, to);
                    }
                }
            }
            let widen = |g: DirGraph8| DirGraph16 {
                size: g.size,
                edges: std::array::from_fn(|i| if i < 8 { g.edges[i] as u16 } else { 0 }),
            };
            let expected = g8.cyclic_groups().map(|(gr, ne)| (widen(gr), widen(ne)));
            assert_eq!(g16.cyclic_groups(), expected);
        }
    }

    #[test]
    fn cycle_groups_graph8() {
        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 1; // a -> b
        g.edges[1] |= 1 << 2; // b -> c
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1 << 1; // d -> b
        let expected = DirGraph8::from_edges([0b0001, 0b1110]);
        assert_eq!(g.cyclic_groups().unwrap().0, expected); // {b, c, d}

        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1 << 3; // b -> d
        g.edges[2] |= 1; // c -> a
        g.edges[3] |= 1 << 1; // d -> b
        let expected = DirGraph8::from_edges([0b0101, 0b1010]);
        assert_eq!(g.cyclic_groups().unwrap().0, expected); // {b, c, d}

        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1; // d -> a
        let expected = DirGraph8::from_edges([0b1101, 0b0010]);
        assert_eq!(g.cyclic_groups().unwrap().0, expected); // {b, c, d}

        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 2; // a -> c
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1; // d -> a
        let expected = DirGraph8::from_edges([0b1101, 0b0010]);
        assert_eq!(g.cyclic_groups().unwrap().0, expected); // {b, c, d}
    }

    #[test]
    fn group_sccs_8() {
        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= (1 << 2) | (1 << 1); // a -> {b,c}
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1 << 2; // d -> c

        let Some((groups, new_edges)) = g.cyclic_groups() else {
            panic!()
        };

        new_edges.print_table();

        let ex_groups = DirGraph8::from_edges([0b0011, 0b1100]);
        let exp_new_edges = DirGraph8::from_edges([0b10, 0b00]);

        assert_eq!(groups, ex_groups); // {b, c, d}
        assert_eq!(new_edges, exp_new_edges);
    }

    #[test]
    fn order_8() {
        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[3] |= (1 << 1) | (1 << 2); // d -> {b,c}
        g.edges[2] |= 1; // c -> a

        let order = g.order();
        println!("{order:?}");

        // every edge i -> j must have i before j
        let pos = |n: usize| order[..g.size].iter().position(|&x| x == n).unwrap();
        for i in 0..g.size {
            for j in 0..g.size {
                if g.edges[i] & (1 << j) != 0 {
                    assert!(pos(i) < pos(j), "{i} -> {j} out of order: {order:?}");
                }
            }
        }
    }

    #[test]
    fn group_order_sccs_8() {
        let mut g = DirGraph8 {
            size: 4,
            edges: [0; 8],
        };
        g.edges[0] |= (1 << 2) | (1 << 1); // a -> {b,c}
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= 1 << 3; // c -> d
        g.edges[3] |= 1 << 2; // d -> c

        let Some(groups) = g.ordered_cyclic_groups() else {
            panic!()
        };
        assert_eq!(groups.size, 2);

        assert_eq!(groups[..groups.size], [0b0011, 0b1100]);

        let mut g = DirGraph8 {
            size: 5,
            edges: [0; 8],
        };
        g.edges[0] |= 1 << 1; // a -> b
        g.edges[1] |= 1; // b -> a
        g.edges[2] |= (1 << 3) | (1 << 1); // c -> d,b
        g.edges[3] |= 1 << 2; // d -> c
        g.edges[4] |= 1 << 3; // e -> c

        g.print_table();

        let Some(groups) = g.ordered_cyclic_groups() else {
            panic!()
        };
        assert_eq!(groups.size, 3);

        assert_eq!(groups[..groups.size], [0b10000, 0b1100, 0b0011]);
    }
}
