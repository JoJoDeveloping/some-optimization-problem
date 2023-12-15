use std::cmp::Ordering;
use std::ops::{Add, Mul, Neg, Sub};
use num_traits::{One, Signed, Zero};

pub trait DivideTowardsNegInfty {
    fn divide_towards_neg_infty(&self, b: &Self) -> Self;
}

impl DivideTowardsNegInfty for i128 {
    fn divide_towards_neg_infty(&self, b: &Self) -> Self {
        let a = self;
        let res = a / b;
        let rem = a % b;
        // Correct division result downwards if up-rounding happened,
        // (for non-zero remainder of sign different than the divisor).
        let corr = (!rem.is_zero() && ((rem.is_negative()) != (b.is_negative())));
        let res = res - (if corr {1} else {0});
        res
    }
}

pub type MyInt = i128;

/*

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MyInt(i128);

impl MyInt {

    pub fn is_positive(&self) -> bool {
        self.0.is_positive()
    }
}

impl DivideTowardsNegInfty for MyInt {
    fn divide_towards_neg_infty(&self, b: &Self) -> Self {
        MyInt(self.0.divide_towards_neg_infty(&b.0))
    }

}

impl PartialOrd for MyInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for MyInt {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl Add for MyInt {
    type Output = MyInt;

    fn add(self, rhs: Self) -> Self::Output {
        MyInt(self.0 + rhs.0)
    }
}

impl Sub for MyInt {
    type Output = MyInt;

    fn sub(self, rhs: Self) -> Self::Output {
        MyInt(self.0 - rhs.0)
    }
}

impl Sub for &MyInt {
    type Output = MyInt;

    fn sub(self, rhs: Self) -> Self::Output {
        MyInt(self.0 - rhs.0)
    }
}

impl Zero for MyInt {
    fn zero() -> Self {
        MyInt(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl Mul<Self> for MyInt {
    type Output = MyInt;

    fn mul(self, rhs: Self) -> Self::Output {
        MyInt(self.0 * rhs.0)
    }
}
impl Mul<Self> for &MyInt {
    type Output = MyInt;

    fn mul(self, rhs: Self) -> Self::Output {
        MyInt(self.0 * rhs.0)
    }
}


impl One for MyInt {
    fn one() -> Self {
        MyInt(1)
    }
}

impl Neg for MyInt {
    type Output = MyInt;

    fn neg(self) -> Self::Output {
        MyInt(-self.0)
    }
}

impl From<i32> for MyInt {
    fn from(value: i32) -> Self {
        MyInt(value.into())
    }
}
*/