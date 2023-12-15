use std::ops::{Div, Rem, Sub};

use num_traits::{One, Zero};

pub trait DivideTowardsNegInfty {
    type Output;
    fn divide_towards_neg_infty(&self, b: &Self) -> Self::Output;
}

impl<T> DivideTowardsNegInfty for T
    where for<'a> &'a T: Div<Output=T> + Rem<Output=T>, T: Sub<Output=T> + Zero + One + Ord {
    type Output = T;
    fn divide_towards_neg_infty(&self, b: &Self) -> Self::Output {
        let a = self;
        let res = a / b;
        let rem = a % b;
        // Correct division result downwards if up-rounding happened,
        // (for non-zero remainder of sign different than the divisor).
        let corr = !rem.is_zero() && ((rem < T::zero()) != (*b < T::zero()));
        let res = res - (if corr { T::one() } else { T::zero() });
        res
    }
}

// change this to e.g. BigInt
pub type MyInt = i128;