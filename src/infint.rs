use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::ops::{Add, Sub};

use InfInt::{MinusInf, PlusInf};

use crate::infint::InfInt::Num;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InfInt<T> {
    PlusInf,
    MinusInf,
    Num(T),
}

impl<T> InfInt<T> {
    pub fn as_ref(&self) -> InfInt<&T> {
        match self {
            PlusInf => PlusInf,
            MinusInf => MinusInf,
            Num(ref x) => Num(x)
        }
    }
}


impl<T: PartialOrd> PartialOrd<Self> for InfInt<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            (PlusInf, PlusInf) => Equal,
            (MinusInf, MinusInf) => Equal,
            (PlusInf, _) => Greater,
            (_, PlusInf) => Less,
            (MinusInf, _) => Less,
            (_, MinusInf) => Greater,
            (Num(n1), Num(n2)) => n1.partial_cmp(n2)?,
        })
    }
}

impl<T: Ord> Ord for InfInt<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (PlusInf, PlusInf) => Equal,
            (MinusInf, MinusInf) => Equal,
            (PlusInf, _) => Greater,
            (_, PlusInf) => Less,
            (MinusInf, _) => Less,
            (_, MinusInf) => Greater,
            (Num(n1), Num(n2)) => n1.cmp(n2),
        }
    }
}

impl<T: Add> Add<T> for InfInt<T> {
    type Output = InfInt<<T as Add>::Output>;

    fn add(self, rhs: T) -> Self::Output {
        match self {
            PlusInf => PlusInf,
            MinusInf => MinusInf,
            Num(lhs) => Num(lhs + rhs)
        }
    }
}

impl<T: Sub> Sub<T> for InfInt<T> {
    type Output = InfInt<<T as Sub>::Output>;

    fn sub(self, rhs: T) -> Self::Output {
        match self {
            PlusInf => PlusInf,
            MinusInf => MinusInf,
            Num(lhs) => Num(lhs - rhs)
        }
    }
}