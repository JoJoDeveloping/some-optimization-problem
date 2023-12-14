use std::{env, panic};

use rand::Rng;

#[derive(Debug)]
pub struct Input {
    data: Vec<(i32, i32)>,
    // current index -> original index
    permutation: Vec<usize>,
}

impl Input {
    pub fn new(data: Vec<(i32, i32)>) -> Self {
        debug_assert!(!data.is_empty());
        let permutation = (0..data.len()).collect();
        Self {
            data,
            permutation,
        }
    }
}

pub type Solution = (i128, (usize, usize));

pub mod naive;
pub mod involved;

fn random_vec(len: usize) -> Vec<(i32, i32)> {
    let mut rng = rand::thread_rng();
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push((rng.gen_range(-100..=100), rng.gen_range(-100..=100)))
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
            1 => { dbg!(a.solve_involvedly()); }
            _ => {
                let a1 = a.solve_naively();
                let a2 = a.solve_involvedly();
                // dbg!(&a1);
                // dbg!(&a2);
                assert_eq!(a1.0, a2.0)
            }
        }
    }
}

fn test_example() {
    let data_vec = vec![
        (-27, 7),
        (1, 4),
        (3, 3),
        (28, 2),
        (27, 2),
        (70, 1),
        (80, 0),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(input);
    dbg!(ls);
}

fn test_example2() {
    let data_vec = vec![
        // (13, 10),
        (5, 21),
        (3, 32),
        (3, 40),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(input);
    dbg!(ls);
}

fn test_example3() {
    let data_vec = vec![
        (0, 105),
        // (17, 6),
        (16, 6),
        (100, 1),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(input);
    dbg!(ls);
}

fn test_example4() {
    let data_vec = vec![
        (-63, 71, ),
        (67, -9, ),
        (9, -31, ),
        (32, -31, ),
        (-42, -51, ),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_involvedly();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}

fn test_example5() {
    let data_vec = vec![
        (4, 100, ),
        (54, 89, ),
        (54, 89, ),
        // (61, 11, ),
        // (74, 2, ),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_involvedly();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


fn test_example6() {
    let data_vec = vec![
        (1, 50),
        (4, 33),
        // (14, 6),
        (80, 3),
        (100, 2),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_involvedly();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


fn test_example7() {
    let data_vec = vec![
        (15, 94),
        (85, 93),
        (62, 78),
        (26, 62),
        (72, 48),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_involvedly();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


fn test_example8() {
    let data_vec = vec![
        (0, 91),
        (13, 76),
        (72, 74),
        (20, 71),
        (49, 54)
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_involvedly();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}

fn test_example9() {
    let data_vec = vec![
        (-33, 81),
        (0, 71),
        (43, 22),
        (-50, -23),
        (-49, -23),
    ];
    let mut input = Input::new(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_involvedly();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


fn main() {
    test_random();
    // test_example();
    // test_example2();
    // test_example3();
    // test_example4();
    // test_example5();
    // test_example6();
    // test_example7();
    // test_example8();
    // test_example9();
}

