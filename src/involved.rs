use std::cmp::{Ordering, Reverse};
use std::mem::swap;
use std::ops::Div;
use crate::{Input, Solution};
use crate::involved::DominationResult::{Everywhere, LeftOf, Nowhere};

#[derive(Copy, Clone, Debug)]
struct FunctionEntry {
    index: usize,
    last_dom_incl: i128,
}

#[derive(Debug)]
pub struct LookupStructure {
    data: Vec<FunctionEntry>,
    lower_level: Option<Box<LookupStructure>>,
}

impl LookupStructure {
    fn new(depth: usize) -> Box<LookupStructure> {
        Box::new(LookupStructure {
            data: vec![],
            lower_level: if depth == 0 { None } else { Some(Self::new(depth - 1)) },
        })
    }

    fn add_lowest(&mut self, index: usize, last_dom_incl: i128) {
        if let Some(k) = self.peek_lowest() {
            debug_assert!(k.last_dom_incl > last_dom_incl);
        }
        self.data.push(FunctionEntry {
            index,
            last_dom_incl,
        })
    }

    fn add_lowest_combining(&mut self, index: usize, last_dom_incl: i128) {
        if self.peek_lowest().map(|x| x.last_dom_incl == last_dom_incl).unwrap_or(false) {
            self.drop_lowest();
        }
        self.data.push(FunctionEntry {
            index,
            last_dom_incl,
        })
    }

    fn drop_lowest(&mut self) -> FunctionEntry {
        self.data.pop().expect("Not to be empty")
    }

    fn peek_lowest(&self) -> Option<FunctionEntry> {
        self.data.last().copied()
    }

    fn insert(&mut self, input: &Input, idx: usize) {
        let mut new_back_for_lowest = Vec::<FunctionEntry>::new();
        let mut cur_lb = i128::MIN;
        let handler = |this: &mut Self, coord: i128, entry : FunctionEntry, mut new_back_for_lowest: Vec<FunctionEntry>| {
            this.add_lowest(idx, coord);
            if let Some(ref mut next) = this.lower_level {
                // insert ourselves into next, clearing all until at least coord
                next.insert(input, idx);
                // add line we replaced
                // this and the next one might only dominate for < 1 grid.
                // in other words, the domination is never observed
                // so we add them in this order (by domination at the grid slot where it actually matters).
                next.add_lowest_combining(entry.index, coord);
                if let Some(x) = new_back_for_lowest.pop() {
                    next.add_lowest_combining(x.index, x.last_dom_incl);
                }
                while let Some(x) = new_back_for_lowest.pop() {
                    next.add_lowest(x.index, x.last_dom_incl);
                }
            }

        };


        while let Some(entry) = self.peek_lowest() {
            match input.starts_dominating(idx, entry.index) {
                // we do not dominate the lowest
                Nowhere => {
                    if cur_lb != i128::MIN {
                        handler(self, cur_lb, entry, new_back_for_lowest);
                    } else if let Some(ref mut next) = self.lower_level {
                        // insert into next
                        next.insert(input, idx);
                    }
                    return;
                }
                // we dominate the current lowest, but not fully
                LeftOf(coord) if cur_lb.max(coord) < entry.last_dom_incl => {
                    handler(self, cur_lb.max(coord), entry, new_back_for_lowest);
                    return;
                }
                _ => {
                    let entry = self.drop_lowest();
                    cur_lb = cur_lb.max(entry.last_dom_incl);
                    if self.lower_level.is_some() {
                        new_back_for_lowest.push(entry)
                    }
                    continue;
                }
            }
        }

        self.add_lowest(idx, i128::MAX) // infty
    }

    fn dominating_at(&self, idx: i128, depth: usize) -> &FunctionEntry {
        if depth > 0 {
            return self.lower_level.as_ref().unwrap().dominating_at(idx, depth - 1);
        }
        let res = self.data.binary_search_by_key(&Reverse(idx), |x| Reverse(x.last_dom_incl));
        match res {
            Ok(x) => &self.data[x],
            Err(x) => &self.data[x - 1]
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum DominationResult {
    Nowhere,
    Everywhere,
    LeftOf(i128),
}

impl Input {
    fn sort(&mut self) {
        let mut vec_to_sort: Vec<_> = self.data.iter().copied().enumerate().collect();
        vec_to_sort.sort_unstable_by(|l, r| {
            let cmp = if l.1.1 < 0 {l.1.0.cmp(&r.1.0).reverse()} else {l.1.0.cmp(&r.1.0)};
            l.1.1.cmp(&r.1.1).then(cmp).reverse()
        });
        let mut new_perm = Vec::with_capacity(vec_to_sort.len());
        for (new_idx, (old_idx, (a, b))) in vec_to_sort.iter().copied().enumerate() {
            self.data[new_idx] = (a, b);
            new_perm.push(self.permutation[old_idx]);
        }
        swap(&mut self.permutation, &mut new_perm);
    }

    fn starts_dominating(&self, f_1: usize, f_2: usize) -> DominationResult {
        let (a_1, b_1) = self.data[f_1];
        let (a_2, b_2) = self.data[f_2];
        compare_fns(a_1, b_1, a_2, b_2)
    }

    pub fn build_lookup_structure(&mut self) -> Box<LookupStructure> {
        self.sort();
        let mut lu = LookupStructure::new(1);
        for idx in 0..self.data.len() {
            lu.insert(self, idx);
        }
        lu
    }

    fn eval_f(&self, i: usize, x: i128) -> i128 {
        let (a_i, b_i) = self.data[i];
        let a_i = i128::from(a_i);
        let b_i = i128::from(b_i);
        a_i * b_i + x * b_i
    }

    pub fn solve_involvedly(&mut self) -> Solution {
        let lu = self.build_lookup_structure();
        let mut mx = None;
        for i in 0..self.data.len() {
            let (a_i, b_i) = self.data[i];
            let a_i = i128::from(a_i);
            let b_i = i128::from(b_i);
            let mut dom = lu.dominating_at(a_i, 0);
            if dom.index == i {
                dom = lu.dominating_at(a_i, 1);
                assert_ne!(dom.index, i);
            }
            let mv = a_i * b_i + self.eval_f(dom.index, a_i);
            if mx.map(|(v, _)| mv > v).unwrap_or(true) {
                mx = Some((mv, (i, dom.index)))
            }
        }
        let (max, (i, j)) = mx.unwrap();
        (max, (self.permutation[i], self.permutation[j]))
    }
}


pub fn compare_fns(a_1: i32, b_1: i32, a_2: i32, b_2: i32) -> DominationResult {
    debug_assert!(b_1 <= b_2);
    if b_1 == b_2 {
        if if b_1 > 0 {a_1 < a_2} else {a_2 < a_1} {
            Nowhere
        } else {
            Everywhere
        }
    } else {
        let a_1 = i128::from(a_1);
        let a_2 = i128::from(a_2);
        let b_1 = i128::from(b_1);
        let b_2 = i128::from(b_2);
        let ab_1 = a_1 * b_1;
        let ab_2 = a_2 * b_2;
        LeftOf(
            divide_towards_minus_infinity(ab_2 - ab_1, b_1 - b_2)
        )
    }
}

pub fn divide_towards_minus_infinity(a:i128, b:i128) -> i128 {
    let res = a / b;
    let rem = a % b;
    // Correct division result downwards if up-rounding happened,
    // (for non-zero remainder of sign different than the divisor).
    let corr = (rem != 0 && ((rem < 0) != (b < 0)));
    res - (if corr {1} else {0})
}