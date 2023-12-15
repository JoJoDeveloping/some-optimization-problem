use crate::{Input, Solution};
use crate::myint::MyInt;

impl Input {
    pub fn to_max_at(&self, i: usize, j: usize) -> MyInt {
        let (a_i, b_i) = &self.data[i];
        let (a_j, b_j) = &self.data[j];
        a_i * b_i + a_j * b_j + a_i * b_j
    }

    pub fn solve_naively(&self) -> Solution {
        let mut state = None;
        for i in 0..self.data.len() {
            for j in 0..self.data.len() {
                if i == j { continue; }
                let cur = self.to_max_at(i, j);
                if state.as_ref().map(|(max, _)| max < &cur).unwrap_or(true) {
                    state = Some((cur, (i, j)))
                }
            }
        }
        let (max, (i, j)) = state.unwrap();
        (max, (self.permutation[i], self.permutation[j]))
    }
}