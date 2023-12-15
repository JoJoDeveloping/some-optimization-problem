use crate::Input;

pub fn test_example() {
    let data_vec = vec![
        (-27, 7),
        (1, 4),
        (3, 3),
        (28, 2),
        (27, 2),
        (70, 1),
        (80, 0),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(input);
    dbg!(ls);
}

pub fn test_example2() {
    let data_vec = vec![
        // (13, 10),
        (5, 21),
        (3, 32),
        (3, 40),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(input);
    dbg!(ls);
}

pub fn test_example3() {
    let data_vec = vec![
        (0, 105),
        // (17, 6),
        (16, 6),
        (100, 1),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(input);
    dbg!(ls);
}

pub fn test_example4() {
    let data_vec = vec![
        (-63, 71, ),
        (67, -9, ),
        (9, -31, ),
        (32, -31, ),
        (-42, -51, ),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_fast();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}

pub fn test_example5() {
    let data_vec = vec![
        (4, 100, ),
        (54, 89, ),
        (54, 89, ),
        // (61, 11, ),
        // (74, 2, ),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_fast();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


pub fn test_example6() {
    let data_vec = vec![
        (1, 50),
        (4, 33),
        // (14, 6),
        (80, 3),
        (100, 2),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_fast();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


pub fn test_example7() {
    let data_vec = vec![
        (15, 94),
        (85, 93),
        (62, 78),
        (26, 62),
        (72, 48),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_fast();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}


pub fn test_example8() {
    let data_vec = vec![
        (0, 91),
        (13, 76),
        (72, 74),
        (20, 71),
        (49, 54)
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_fast();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}

pub fn test_example9() {
    let data_vec = vec![
        (-33, 81),
        (0, 71),
        (43, 22),
        (-50, -23),
        (-49, -23),
    ];
    let mut input = Input::from_i32(data_vec);
    let ls = input.build_lookup_structure();
    dbg!(&input);
    dbg!(ls);
    let a1 = input.solve_naively();
    let a2 = input.solve_fast();
    // dbg!(&a1);
    // dbg!(&a2);
    assert_eq!(a1.0, a2.0)
}
