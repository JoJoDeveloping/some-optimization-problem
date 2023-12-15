use std::cmp::{Ordering, Reverse};
use std::mem::swap;
use std::ops::Div;
use num_traits::{One, Zero};
use crate::{Input, Solution};
use crate::infint::InfInt;
use crate::infint::InfInt::{MinusInf, Num, PlusInf};
use crate::myint::{DivideTowardsNegInfty, MyInt};

#[derive(Clone, Debug)]
struct FunctionEntry {
    index: usize,
    first_incl: InfInt<MyInt>,
    last_incl: InfInt<MyInt>
}

#[derive(Debug)]
pub struct LookupStructure {
    /*
    Invariants:
    Each function entry is an interval.
    * The function in this interval dominates all functions so far considered
        (excluding those at a higher level)
    * The intervals are disjoint, cover all of Z, and are linearly ordered (backwards)
    * All functions right of the interval (plus the functions in higher levels right) dominate the current function right of it.
     */
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

    fn add_lowest(&mut self, index: usize, last_incl: InfInt<MyInt>) {
        assert!(last_incl > MinusInf);
        let first_incl = MinusInf;
        if let Some(k) = self.peek_lowest_mut() {
            debug_assert!(&k.last_incl > &last_incl);
            k.first_incl = last_incl.clone() + MyInt::one();
        }
        self.data.push(FunctionEntry {
            index,
            first_incl,
            last_incl
        })
    }

    fn add_lowest_combining(&mut self, index: usize, last_incl: InfInt<MyInt>) {
        if self.peek_lowest().map(|x| x.last_incl == last_incl).unwrap_or(false) {
            self.drop_lowest();
        }
        self.add_lowest(index, last_incl);
    }

    fn drop_lowest(&mut self) -> FunctionEntry {
        self.data.pop().expect("Not to be empty")
    }

    fn peek_lowest(&self) -> Option<&FunctionEntry> {
        self.data.last()
    }

    fn peek_lowest_mut(&mut self) -> Option<&mut FunctionEntry> {
        self.data.last_mut()
    }

    fn insert_at_coord(&mut self, input: &Input, idx: usize, coord: InfInt<MyInt>, entry_index: usize,
                       mut new_back_for_lowest: Vec<FunctionEntry>) {
        debug_assert!(coord != MinusInf);
        self.add_lowest(idx, coord.clone());
        if let Some(ref mut next) = self.lower_level {
            // insert ourselves into next, clearing all until at least coord
            next.insert(input, idx);
            // add line we replaced
            // this and the next one might only dominate for < 1 grid.
            // in other words, the domination is never observed
            // so we add them in this order (by domination at the grid slot where it actually matters).
            next.add_lowest_combining(entry_index, coord.clone());
            if let Some(x) = new_back_for_lowest.pop() {
                next.add_lowest_combining(x.index, x.last_incl);
            }
            while let Some(x) = new_back_for_lowest.pop() {
                next.add_lowest(x.index, x.last_incl);
            }
        }
    }

    fn insert(&mut self, input: &Input, idx: usize) {
        let mut new_back_for_lowest = Vec::<FunctionEntry>::new();

        while let Some(entry) = self.peek_lowest() {
            match input.starts_dominating(idx, entry.index) {
                k if k < entry.first_incl => {
                    // the domain ends before we can dominate (and does not start at -inf)
                    // this means that we removed all stuff that came before
                    // and are now the new dominators for that all
                    let coord = entry.first_incl.clone() + (-MyInt::one());
                    self.insert_at_coord(input, idx, coord, entry.index, new_back_for_lowest);
                    return;
                }
                MinusInf => { // we never dominate, needs special handling, since we do not want to add these
                    if let Some(ref mut next) = self.lower_level {
                        // insert into next
                        next.insert(input, idx);
                    }
                    return;
                }
                k if k >= entry.last_incl => { // we dominate on the entire domain
                    let entry = self.drop_lowest();
                    if self.lower_level.is_some() {
                        new_back_for_lowest.push(entry)
                    }
                    continue;
                }
                k if k >= entry.first_incl && k < entry.last_incl => {
                    let coord = k;
                    self.insert_at_coord(input, idx, coord, entry.index, new_back_for_lowest);
                    return;
                }
                _ => {
                    unreachable!()
                }
            }
        }
        // default case, if we are empty
        self.add_lowest(idx, PlusInf)
    }

    fn dominating_at(&self, idx: &MyInt, depth: usize) -> &FunctionEntry {
        if depth > 0 {
            return self.lower_level.as_ref().unwrap().dominating_at(idx, depth - 1);
        }
        let res = self.data.binary_search_by_key(&Reverse(Num(idx)), |x| Reverse(x.last_incl.as_ref()));
        let res = match res {
            Ok(x) => &self.data[x],
            Err(x) => &self.data[x - 1]
        };
        debug_assert!(res.first_incl <= Num(idx.clone()) && Num(idx.clone()) <= res.last_incl);
        res
    }
}


impl Input {
    fn sort(&mut self) {
        let mut self_data = vec![];
        swap(&mut self_data, &mut self.data);
        let mut vec_to_sort: Vec<_> = self_data.into_iter().enumerate().collect();
        vec_to_sort.sort_unstable_by(|l, r| {
            l.1.1.cmp(&r.1.1).then_with(|| {
                let l1 = &l.1.0 * &l.1.1;
                let r1 = &r.1.0 * &r.1.1;
                l1.cmp(&r1)
            }
            ).reverse()
        });
        let mut new_perm = Vec::with_capacity(vec_to_sort.len());
        for (old_idx, (a, b)) in vec_to_sort.into_iter() {
            self.data.push((a, b));
            new_perm.push(self.permutation[old_idx]);
        }
        swap(&mut self.permutation, &mut new_perm);
    }

    fn starts_dominating(&self, f_1: usize, f_2: usize) -> InfInt<MyInt> {
        let (a_1, b_1) = &self.data[f_1];
        let (a_2, b_2) = &self.data[f_2];
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

    fn eval_f(&self, i: usize, x: &MyInt) -> MyInt {
        let (a_i, b_i) = &self.data[i];
        a_i * b_i + x * b_i
    }

    pub fn solve_fast(&mut self) -> Solution {
        let lu = self.build_lookup_structure();
        let mut mx = None;
        for i in 0..self.data.len() {
            let (a_i, b_i) = &self.data[i];
            let mut dom = lu.dominating_at(a_i, 0);
            if dom.index == i {
                dom = lu.dominating_at(a_i, 1);
                assert_ne!(dom.index, i);
            }
            let mv = a_i * b_i + self.eval_f(dom.index, a_i);
            if mx.as_ref().map(|(v, _)| &mv > v).unwrap_or(true) {
                mx = Some((mv, (i, dom.index)))
            }
        }
        let (max, (i, j)) = mx.unwrap();
        (max, (self.permutation[i], self.permutation[j]))
    }
}

/**
  given f_1(x) = a_1 * b_1 + x * b_1,
        f_2(x) = a_2 * b_2 + x * b_2,
  returns z such that
      forall k >  z, f_2(k)  > f_1(k)
  and forall k <= z, f_2(k) <= f_1(k)
*/
pub fn compare_fns(a_1: &MyInt, b_1: &MyInt, a_2: &MyInt, b_2: &MyInt) -> InfInt<MyInt> {
    debug_assert!(b_1 <= b_2);
    if b_1 == b_2 {
        if if b_1.is_positive() {a_1 < a_2} else {a_2 < a_1} {
            MinusInf
        } else {
            PlusInf
        }
    } else {
        let ab_1 = a_1 * b_1;
        let ab_2 = a_2 * b_2;
        Num(
            (ab_2 - ab_1).divide_towards_neg_infty(&(b_1 - b_2))
        )
    }
}
