use crate::{Input, Solution};

impl Input {
    pub fn to_max_at(&self, i: usize, j: usize) -> i128 {
        let (a_i, b_i) = self.data[i];
        let (a_j, b_j) = self.data[j];
        let a_i = i128::from(a_i);
        let a_j = i128::from(a_j);
        let b_i = i128::from(b_i);
        let b_j = i128::from(b_j);
        a_i * b_i + a_j * b_j + a_i * b_j
    }

    pub fn solve_naively(&self) -> Solution {
        let mut state = None;
        for i in 0..self.data.len() {
            for j in 0..self.data.len() {
                if i == j { continue; }
                let cur = self.to_max_at(i, j);
                if state.map(|(max, _)| max < cur).unwrap_or(true) {
                    state = Some((cur, (i, j)))
                }
            }
        }
        let (max, (i, j)) = state.unwrap();
        (max, (self.permutation[i], self.permutation[j]))
    }
}