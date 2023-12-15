use std::{env, panic};

use rand::Rng;
use crate::myint::MyInt;
use crate::test::*;

#[derive(Debug)]
pub struct Input {
    data: Vec<(MyInt, MyInt)>,
    // current index -> original index
    permutation: Vec<usize>,
}

impl Input {
    pub fn new(data: Vec<(MyInt, MyInt)>) -> Self {
        debug_assert!(!data.is_empty());
        let permutation = (0..data.len()).collect();
        Self {
            data,
            permutation,
        }
    }
    pub fn from_i32(data: Vec<(i32, i32)>) -> Self {
        debug_assert!(!data.is_empty());
        let permutation = (0..data.len()).collect();
        Self {
            data: data.into_iter().map(|(a,b)| (MyInt::from(a), MyInt::from(b))).collect(),
            permutation,
        }
    }
}

pub type Solution = (MyInt, (usize, usize));

pub mod naive;
pub mod involved;

pub mod infint;

pub mod myint;

pub mod test;

fn random_vec(len: usize) -> Vec<(MyInt, MyInt)> {
    let mut rng = rand::thread_rng();
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push((
            MyInt::from(rng.gen_range(-100..=100)),
            MyInt::from(rng.gen_range(-100..=100))))
    }
    let v2 = v.clone();
    panic::set_hook(Box::new(move |_| {
        dbg!(&v2);
    }));
    v
}

fn test_random() {
    let num = env::args().skip(1).next().unwrap().parse::<usize>().unwrap();
    let involved = env::args().skip(2).next().unwrap().parse::<i32>().unwrap();
    let cnt = env::args().skip(3).next().unwrap_or_else(|| "1".into()).parse::<usize>().unwrap();
    for i in 0..cnt {
        let mut a = Input::new(random_vec(num));
        match involved {
            0 => { dbg!(a.solve_naively()); }
            1 => { dbg!(a.solve_fast()); }
            _ => {
                let a1 = a.solve_naively();
                let a2 = a.solve_fast();
                // dbg!(&a1);
                // dbg!(&a2);
                assert_eq!(a1.0, a2.0)
            }
        }
    }
}

fn main() {
    // test_random();
    test_example();
    test_example2();
    test_example3();
    test_example4();
    test_example5();
    test_example6();
    test_example7();
    test_example8();
    test_example9();
}

