use crate::rational::Rational;
use std::{
    cmp::Ordering,
    fmt::{Display, Formatter, Result},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

/// Represents a rational number extended with an infinitesimal part.
///
/// The value is represented as `rat + inf * ε`, where `ε` (epsilon) is an infinitesimal
/// value that is positive but smaller than any positive rational number.
///
/// - `rat`: The standard rational part.
/// - `inf`: The coefficient of the infinitesimal `ε`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InfRational {
    rat: Rational,
    inf: Rational,
}

impl InfRational {
    /// Creates a new `InfRational` number from its rational and infinitesimal parts.
    ///
    /// The number represents `rat + inf * ε`.
    pub fn new(rat: Rational, inf: Rational) -> Self {
        InfRational { rat, inf }
    }

    pub const POSITIVE_INFINITY: Self = Self { rat: Rational::POSITIVE_INFINITY, inf: Rational::ZERO };
    pub const NEGATIVE_INFINITY: Self = Self { rat: Rational::NEGATIVE_INFINITY, inf: Rational::ZERO };
    pub const ZERO: Self = Self { rat: Rational::ZERO, inf: Rational::ZERO };
}

impl From<Rational> for InfRational {
    fn from(arg: Rational) -> Self {
        InfRational { rat: arg, inf: Rational::ZERO }
    }
}

impl From<i64> for InfRational {
    fn from(arg: i64) -> Self {
        InfRational { rat: Rational::from(arg), inf: Rational::ZERO }
    }
}

impl PartialOrd<&Rational> for InfRational {
    fn partial_cmp(&self, other: &&Rational) -> Option<Ordering> {
        match self.rat.partial_cmp(*other) {
            Some(Ordering::Equal) => self.inf.partial_cmp(&0),
            ord => ord,
        }
    }
}

impl PartialOrd<i64> for InfRational {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        match self.rat.partial_cmp(other) {
            Some(Ordering::Equal) => self.inf.partial_cmp(&0),
            ord => ord,
        }
    }
}

impl PartialEq<i64> for InfRational {
    fn eq(&self, other: &i64) -> bool {
        self.inf == 0 && self.rat == *other
    }
}

impl PartialEq<&Rational> for InfRational {
    fn eq(&self, other: &&Rational) -> bool {
        self.inf == 0 && self.rat == **other
    }
}

macro_rules! impl_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        // InfRational op InfRational
        impl $trait<InfRational> for InfRational {
            type Output = InfRational;
            fn $method(mut self, other: InfRational) -> InfRational {
                self.$assign_method(&other);
                self
            }
        }

        // InfRational op &InfRational
        impl $trait<&InfRational> for InfRational {
            type Output = InfRational;
            fn $method(mut self, other: &InfRational) -> InfRational {
                self.$assign_method(other);
                self
            }
        }

        // &InfRational op InfRational
        impl $trait<InfRational> for &InfRational {
            type Output = InfRational;
            fn $method(self, other: InfRational) -> InfRational {
                let mut result = *self;
                result.$assign_method(&other);
                result
            }
        }

        // &InfRational op &InfRational
        impl $trait<&InfRational> for &InfRational {
            type Output = InfRational;
            fn $method(self, other: &InfRational) -> InfRational {
                let mut result = *self;
                result.$assign_method(other);
                result
            }
        }
    };
}

macro_rules! impl_op_scalar {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        // InfRational op Rational
        impl $trait<&Rational> for InfRational {
            type Output = InfRational;
            fn $method(mut self, other: &Rational) -> InfRational {
                self.$assign_method(other);
                self
            }
        }

        // &InfRational op Rational
        impl $trait<&Rational> for &InfRational {
            type Output = InfRational;
            fn $method(self, other: &Rational) -> InfRational {
                let mut result = *self;
                result.$assign_method(other);
                result
            }
        }

        // InfRational op i64
        impl $trait<i64> for InfRational {
            type Output = InfRational;
            fn $method(mut self, other: i64) -> InfRational {
                self.$assign_method(other);
                self
            }
        }

        // &InfRational op i64
        impl $trait<i64> for &InfRational {
            type Output = InfRational;
            fn $method(self, other: i64) -> InfRational {
                let mut result = *self;
                result.$assign_method(other);
                result
            }
        }
    };
}

macro_rules! impl_rev_op {
    ($trait:ident, $method:ident) => {
        // Rational op InfRational
        impl $trait<InfRational> for Rational {
            type Output = InfRational;
            fn $method(self, other: InfRational) -> InfRational {
                other.$method(&self)
            }
        }

        // Rational op &InfRational
        impl $trait<&InfRational> for Rational {
            type Output = InfRational;
            fn $method(self, other: &InfRational) -> InfRational {
                other.$method(&self)
            }
        }

        // &Rational op InfRational
        impl $trait<InfRational> for &Rational {
            type Output = InfRational;
            fn $method(self, other: InfRational) -> InfRational {
                other.$method(self)
            }
        }

        // &Rational op &InfRational
        impl $trait<&InfRational> for &Rational {
            type Output = InfRational;
            fn $method(self, other: &InfRational) -> InfRational {
                other.$method(self)
            }
        }

        // i64 op InfRational
        impl $trait<InfRational> for i64 {
            type Output = InfRational;
            fn $method(self, other: InfRational) -> InfRational {
                other.$method(self)
            }
        }

        // i64 op &InfRational
        impl $trait<&InfRational> for i64 {
            type Output = InfRational;
            fn $method(self, other: &InfRational) -> InfRational {
                other.$method(self)
            }
        }
    };
}

impl_op!(Add, add, AddAssign, add_assign);
impl_op!(Sub, sub, SubAssign, sub_assign);

impl_op_scalar!(Add, add, AddAssign, add_assign);
impl_op_scalar!(Sub, sub, SubAssign, sub_assign);
impl_op_scalar!(Mul, mul, MulAssign, mul_assign);
impl_op_scalar!(Div, div, DivAssign, div_assign);

impl_rev_op!(Add, add);
impl_rev_op!(Mul, mul);

// Manual implementation for reverse subtraction (non-commutative)
// Rational - InfRational
impl Sub<InfRational> for Rational {
    type Output = InfRational;
    fn sub(self, other: InfRational) -> InfRational {
        InfRational { rat: self - other.rat, inf: -other.inf }
    }
}

// Rational - &InfRational
impl Sub<&InfRational> for Rational {
    type Output = InfRational;
    fn sub(self, other: &InfRational) -> InfRational {
        InfRational { rat: self - other.rat, inf: -other.inf }
    }
}

// &Rational - InfRational
impl Sub<InfRational> for &Rational {
    type Output = InfRational;
    fn sub(self, other: InfRational) -> InfRational {
        InfRational { rat: self - other.rat, inf: -other.inf }
    }
}

// &Rational - &InfRational
impl Sub<&InfRational> for &Rational {
    type Output = InfRational;
    fn sub(self, other: &InfRational) -> InfRational {
        InfRational { rat: self - other.rat, inf: -other.inf }
    }
}

// i64 - InfRational
impl Sub<InfRational> for i64 {
    type Output = InfRational;
    fn sub(self, other: InfRational) -> InfRational {
        InfRational { rat: Rational::from(self) - other.rat, inf: -other.inf }
    }
}

// i64 - &InfRational
impl Sub<&InfRational> for i64 {
    type Output = InfRational;
    fn sub(self, other: &InfRational) -> InfRational {
        InfRational { rat: Rational::from(self) - other.rat, inf: -other.inf }
    }
}

impl AddAssign for InfRational {
    fn add_assign(&mut self, other: Self) {
        self.rat += other.rat;
        self.inf += other.inf;
    }
}

impl AddAssign<&InfRational> for InfRational {
    fn add_assign(&mut self, other: &InfRational) {
        self.rat += &other.rat;
        self.inf += &other.inf;
    }
}

impl AddAssign<&Rational> for InfRational {
    fn add_assign(&mut self, other: &Rational) {
        self.rat += other;
    }
}

impl AddAssign<i64> for InfRational {
    fn add_assign(&mut self, other: i64) {
        self.rat += other;
    }
}

impl SubAssign for InfRational {
    fn sub_assign(&mut self, other: Self) {
        self.rat -= other.rat;
        self.inf -= other.inf;
    }
}

impl SubAssign<&InfRational> for InfRational {
    fn sub_assign(&mut self, other: &InfRational) {
        self.rat -= &other.rat;
        self.inf -= &other.inf;
    }
}

impl SubAssign<&Rational> for InfRational {
    fn sub_assign(&mut self, other: &Rational) {
        self.rat -= other;
    }
}

impl SubAssign<i64> for InfRational {
    fn sub_assign(&mut self, other: i64) {
        self.rat -= other;
    }
}

impl MulAssign for InfRational {
    fn mul_assign(&mut self, other: Self) {
        let a = self.rat;
        let b = self.inf;
        let c = other.rat;
        let d = other.inf;

        self.rat = a * c;
        self.inf = (a * d) + (b * c);
    }
}

impl MulAssign<&Rational> for InfRational {
    fn mul_assign(&mut self, other: &Rational) {
        self.rat *= other;
        self.inf *= other;
    }
}

impl MulAssign<i64> for InfRational {
    fn mul_assign(&mut self, other: i64) {
        self.rat *= other;
        self.inf *= other;
    }
}

impl DivAssign for InfRational {
    fn div_assign(&mut self, other: Self) {
        let a = self.rat;
        let b = self.inf;
        let c = other.rat;
        let d = other.inf;

        self.rat = a / c;
        self.inf = (b * c - a * d) / (c * c);
    }
}

impl DivAssign<&Rational> for InfRational {
    fn div_assign(&mut self, other: &Rational) {
        self.rat /= other;
        self.inf /= other;
    }
}

impl DivAssign<i64> for InfRational {
    fn div_assign(&mut self, other: i64) {
        self.rat /= other;
        self.inf /= other;
    }
}

impl Neg for InfRational {
    type Output = InfRational;

    fn neg(self) -> InfRational {
        InfRational { rat: -self.rat, inf: -self.inf }
    }
}

impl Display for InfRational {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.inf == 0 {
            write!(f, "{}", self.rat)
        } else if self.rat == 0 {
            write!(f, "{}ε", self.inf)
        } else if self.inf > 0 {
            write!(f, "{} + {}ε", self.rat, self.inf)
        } else {
            write!(f, "{} - {}ε", self.rat, -self.inf)
        }
    }
}

pub fn inf_i(arg: i64) -> InfRational {
    InfRational::new(Rational::ZERO, Rational::from(arg))
}

pub fn inf(rat: Rational, inf: Rational) -> InfRational {
    InfRational::new(rat, inf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let r1 = Rational::new(1, 2);
        let r2 = Rational::new(3, 4);
        let ir = inf(r1, r2);
        assert_eq!(ir.rat, r1);
        assert_eq!(ir.inf, r2);
    }

    #[test]
    fn test_equality() {
        let ir1 = inf(Rational::new(1, 2), Rational::new(3, 4));
        let ir2 = inf(Rational::new(2, 4), Rational::new(3, 4));
        assert_eq!(ir1, ir2);

        let ir3 = InfRational::from(Rational::new(1, 2));
        let ra = Rational::new(1, 2);
        assert_eq!(ir3, &ra);

        // This fails to compile if PartialEq<i64> isn't implemented correctly or type inference fails
        // PartialEquals<i64> is implemented.
        let ir4 = InfRational::from(Rational::from(5));
        assert_eq!(ir4, 5);
    }

    #[test]
    fn test_ord() {
        let ir1 = inf_i(1); // 1ε
        let ir2 = InfRational::from(Rational::from(100)); // 100

        // 1ε < 100
        assert!(ir1 < ir2);

        let ir3 = inf_i(-1); // -1ε
        assert!(ir3 < ir2);
        assert!(ir3 < ir1);

        let ir4 = inf(Rational::from(1), Rational::from(1)); // 1 + 1ε
        // 1 + 1ε > 0 + 1ε
        assert!(ir4 > ir1);
    }

    #[test]
    fn test_ord_with_primitive_and_rational() {
        let pos_inf = inf_i(1);
        let neg_inf = inf_i(-1);
        let zero = 0;
        let rat_ten = Rational::from(10);

        // 0 < 0 + 1ε
        assert!(pos_inf > zero);
        // 0 + 1ε < 10
        assert!(pos_inf < &rat_ten);

        // -1ε < 0
        assert!(neg_inf < zero);
        // -1ε < 10
        assert!(neg_inf < &rat_ten);
    }

    #[test]
    fn test_arithmetic() {
        let a = inf(Rational::from(1), Rational::from(2)); // 1 + 2ε
        let b = inf(Rational::from(3), Rational::from(4)); // 3 + 4ε

        // Add
        assert_eq!(a + &b, inf(Rational::from(4), Rational::from(6)));

        // Sub
        assert_eq!(b - &a, inf(Rational::from(2), Rational::from(2)));

        // Mul by scalar
        let scalar = Rational::from(2);
        assert_eq!(a * &scalar, inf(Rational::from(2), Rational::from(4)));

        // Div by scalar
        assert_eq!(a / &scalar, inf(Rational::new(1, 2), Rational::from(1)));
    }

    #[test]
    fn test_ordering() {
        let mut list = vec![inf(Rational::new(1, 2), Rational::ZERO), inf(Rational::new(1, 2), Rational::new(1, 1)), inf(Rational::new(1, 2), Rational::new(-1, 1)), InfRational::ZERO, InfRational::POSITIVE_INFINITY, InfRational::NEGATIVE_INFINITY, inf(Rational::POSITIVE_INFINITY, Rational::new(1, 1))];

        list.sort();

        let expected = vec![InfRational::NEGATIVE_INFINITY, InfRational::ZERO, inf(Rational::new(1, 2), Rational::new(-1, 1)), inf(Rational::new(1, 2), Rational::ZERO), inf(Rational::new(1, 2), Rational::new(1, 1)), InfRational::POSITIVE_INFINITY, inf(Rational::POSITIVE_INFINITY, Rational::new(1, 1))];

        assert_eq!(list, expected);
    }

    #[test]
    fn test_from_conversions() {
        // Test from_rational
        let rat_val = Rational::new(3, 4);
        let ir = InfRational::from(rat_val);
        assert_eq!(ir.rat, rat_val);
        assert_eq!(ir.inf, Rational::ZERO);

        // Test from_integer
        let ir2 = InfRational::from(42);
        assert_eq!(ir2.rat, Rational::from(42));
        assert_eq!(ir2.inf, Rational::ZERO);

        // Test From<Rational> trait
        let ir3: InfRational = Rational::new(1, 2).into();
        assert_eq!(ir3.rat, Rational::new(1, 2));
        assert_eq!(ir3.inf, Rational::ZERO);

        // Test From<i64> trait
        let ir4: InfRational = 100.into();
        assert_eq!(ir4.rat, Rational::from(100));
        assert_eq!(ir4.inf, Rational::ZERO);
    }

    #[test]
    fn test_partial_ord_rational() {
        let ir = inf(Rational::from(5), Rational::from(1)); // 5 + 1ε
        let rat_five = Rational::from(5);
        let rat_six = Rational::from(6);

        // ir > 5 because of the infinitesimal part
        assert!(ir > &rat_five);
        // ir < 6
        assert!(ir < &rat_six);

        // Test when rational parts are equal
        let ir_exact = InfRational::from(Rational::from(5)); // 5 + 0ε
        assert!(ir_exact == &rat_five);
    }

    #[test]
    fn test_partial_ord_i64() {
        let ir = inf(Rational::from(5), Rational::from(1)); // 5 + 1ε

        // ir > 5
        assert!(ir > 5);
        // ir < 6
        assert!(ir < 6);

        // Test equality
        let ir_exact = InfRational::from(Rational::from(5)); // 5 + 0ε
        assert!(ir_exact == 5);

        // Test with negative infinitesimal
        let ir_neg = inf(Rational::from(5), Rational::from(-1)); // 5 - 1ε
        assert!(ir_neg < 5);
    }

    #[test]
    fn test_add_variations() {
        let a = inf(Rational::from(1), Rational::from(2));
        let b = inf(Rational::from(3), Rational::from(4));

        // Test &InfRational + InfRational
        let res1 = &a + b;
        assert_eq!(res1, inf(Rational::from(4), Rational::from(6)));

        // Test InfRational + InfRational (already covered but ensures compilation)
        let res2 = a + b;
        assert_eq!(res2, inf(Rational::from(4), Rational::from(6)));

        // Test &InfRational + &InfRational
        let res3 = &a + &b;
        assert_eq!(res3, inf(Rational::from(4), Rational::from(6)));
    }

    #[test]
    fn test_sub_variations() {
        let a = inf(Rational::from(5), Rational::from(3));
        let b = inf(Rational::from(2), Rational::from(1));

        // Test &InfRational - InfRational
        let res1 = &a - b;
        assert_eq!(res1, inf(Rational::from(3), Rational::from(2)));

        // Test InfRational - InfRational
        let res2 = a - b;
        assert_eq!(res2, inf(Rational::from(3), Rational::from(2)));

        // Test &InfRational - &InfRational
        let res3 = &a - &b;
        assert_eq!(res3, inf(Rational::from(3), Rational::from(2)));
    }

    #[test]
    fn test_scalar_add_variations() {
        let ir = inf(Rational::from(2), Rational::from(3));
        let rat_val = Rational::from(5);

        // Test InfRational + &Rational
        let res1 = ir + &rat_val;
        assert_eq!(res1, inf(Rational::from(7), Rational::from(3)));

        // Test &InfRational + &Rational
        let res2 = &ir + &rat_val;
        assert_eq!(res2, inf(Rational::from(7), Rational::from(3)));

        // Test InfRational + i64
        let res3 = ir + 10;
        assert_eq!(res3, inf(Rational::from(12), Rational::from(3)));

        // Test &InfRational + i64
        let res4 = &ir + 10;
        assert_eq!(res4, inf(Rational::from(12), Rational::from(3)));
    }

    #[test]
    fn test_scalar_sub_variations() {
        let ir = inf(Rational::from(10), Rational::from(3));
        let rat_val = Rational::from(5);

        // Test InfRational - &Rational
        let res1 = ir - &rat_val;
        assert_eq!(res1, inf(Rational::from(5), Rational::from(3)));

        // Test &InfRational - &Rational
        let res2 = &ir - &rat_val;
        assert_eq!(res2, inf(Rational::from(5), Rational::from(3)));

        // Test InfRational - i64
        let res3 = ir - 3;
        assert_eq!(res3, inf(Rational::from(7), Rational::from(3)));

        // Test &InfRational - i64
        let res4 = &ir - 3;
        assert_eq!(res4, inf(Rational::from(7), Rational::from(3)));
    }

    #[test]
    fn test_scalar_mul_variations() {
        let ir = inf(Rational::from(2), Rational::from(3));
        let rat_val = Rational::from(4);

        // Test InfRational * &Rational
        let res1 = ir * &rat_val;
        assert_eq!(res1, inf(Rational::from(8), Rational::from(12)));

        // Test &InfRational * &Rational
        let res2 = &ir * &rat_val;
        assert_eq!(res2, inf(Rational::from(8), Rational::from(12)));

        // Test InfRational * i64
        let res3 = ir * 5;
        assert_eq!(res3, inf(Rational::from(10), Rational::from(15)));

        // Test &InfRational * i64
        let res4 = &ir * 5;
        assert_eq!(res4, inf(Rational::from(10), Rational::from(15)));
    }

    #[test]
    fn test_scalar_div_variations() {
        let ir = inf(Rational::from(8), Rational::from(12));
        let rat_val = Rational::from(4);

        // Test InfRational / &Rational
        let res1 = ir / &rat_val;
        assert_eq!(res1, inf(Rational::from(2), Rational::from(3)));

        // Test &InfRational / &Rational
        let res2 = &ir / &rat_val;
        assert_eq!(res2, inf(Rational::from(2), Rational::from(3)));

        // Test InfRational / i64
        let res3 = ir / 2;
        assert_eq!(res3, inf(Rational::from(4), Rational::from(6)));

        // Test &InfRational / i64
        let res4 = &ir / 2;
        assert_eq!(res4, inf(Rational::from(4), Rational::from(6)));
    }

    #[test]
    fn test_reverse_ops() {
        let ir = inf(Rational::from(2), Rational::from(3));
        let rat_val = Rational::from(5);

        // Test &Rational + InfRational
        let res1 = &rat_val + ir;
        assert_eq!(res1, inf(Rational::from(7), Rational::from(3)));

        // Test &Rational + &InfRational
        let res2 = &rat_val + &ir;
        assert_eq!(res2, inf(Rational::from(7), Rational::from(3)));

        // Test i64 + InfRational
        let res3 = 10 + ir;
        assert_eq!(res3, inf(Rational::from(12), Rational::from(3)));

        // Test i64 + &InfRational
        let res4 = 10 + &ir;
        assert_eq!(res4, inf(Rational::from(12), Rational::from(3)));

        // Test reverse subtraction (now correctly implemented)
        // &Rational - InfRational: 5 - (2 + 3ε) = 3 - 3ε
        let res5 = &rat_val - ir;
        assert_eq!(res5, inf(Rational::from(3), Rational::from(-3)));

        // &Rational - &InfRational
        let res6 = &rat_val - &ir;
        assert_eq!(res6, inf(Rational::from(3), Rational::from(-3)));

        // i64 - InfRational: 10 - (2 + 3ε) = 8 - 3ε
        let res7 = 10 - ir;
        assert_eq!(res7, inf(Rational::from(8), Rational::from(-3)));

        // i64 - &InfRational
        let res8 = 10 - &ir;
        assert_eq!(res8, inf(Rational::from(8), Rational::from(-3)));

        // Multiplication is commutative, so reverse ops work correctly
        // Test Rational * InfRational
        let res9 = rat_val * ir;
        assert_eq!(res9, inf(Rational::from(10), Rational::from(15)));

        // Test Rational * &InfRational
        let res10 = rat_val * &ir;
        assert_eq!(res10, inf(Rational::from(10), Rational::from(15)));

        // Test &Rational * InfRational
        let res11 = &rat_val * ir;
        assert_eq!(res11, inf(Rational::from(10), Rational::from(15)));

        // Test &Rational * &InfRational
        let res12 = &rat_val * &ir;
        assert_eq!(res12, inf(Rational::from(10), Rational::from(15)));

        // Test i64 * InfRational
        let res13 = 3 * ir;
        assert_eq!(res13, inf(Rational::from(6), Rational::from(9)));

        // Test i64 * &InfRational
        let res14 = 3 * &ir;
        assert_eq!(res14, inf(Rational::from(6), Rational::from(9)));
    }

    #[test]
    fn test_assign_ops() {
        // Test AddAssign with InfRational
        let mut ir1 = inf(Rational::from(1), Rational::from(2));
        ir1 += inf(Rational::from(3), Rational::from(4));
        assert_eq!(ir1, inf(Rational::from(4), Rational::from(6)));

        // Test AddAssign with &InfRational
        let mut ir2 = inf(Rational::from(1), Rational::from(2));
        ir2 += &inf(Rational::from(3), Rational::from(4));
        assert_eq!(ir2, inf(Rational::from(4), Rational::from(6)));

        // Test AddAssign with &Rational
        let mut ir3 = inf(Rational::from(1), Rational::from(2));
        ir3 += &Rational::from(5);
        assert_eq!(ir3, inf(Rational::from(6), Rational::from(2)));

        // Test AddAssign with i64
        let mut ir4 = inf(Rational::from(1), Rational::from(2));
        ir4 += 7;
        assert_eq!(ir4, inf(Rational::from(8), Rational::from(2)));

        // Test SubAssign with InfRational
        let mut ir5 = inf(Rational::from(5), Rational::from(6));
        ir5 -= inf(Rational::from(1), Rational::from(2));
        assert_eq!(ir5, inf(Rational::from(4), Rational::from(4)));

        // Test SubAssign with &InfRational
        let mut ir6 = inf(Rational::from(5), Rational::from(6));
        ir6 -= &inf(Rational::from(1), Rational::from(2));
        assert_eq!(ir6, inf(Rational::from(4), Rational::from(4)));

        // Test SubAssign with &Rational
        let mut ir7 = inf(Rational::from(10), Rational::from(3));
        ir7 -= &Rational::from(4);
        assert_eq!(ir7, inf(Rational::from(6), Rational::from(3)));

        // Test SubAssign with i64
        let mut ir8 = inf(Rational::from(10), Rational::from(3));
        ir8 -= 3;
        assert_eq!(ir8, inf(Rational::from(7), Rational::from(3)));

        // Test MulAssign with &Rational
        let mut ir9 = inf(Rational::from(2), Rational::from(3));
        ir9 *= &Rational::from(4);
        assert_eq!(ir9, inf(Rational::from(8), Rational::from(12)));

        // Test MulAssign with i64
        let mut ir10 = inf(Rational::from(2), Rational::from(3));
        ir10 *= 5;
        assert_eq!(ir10, inf(Rational::from(10), Rational::from(15)));

        // Test DivAssign with &Rational
        let mut ir11 = inf(Rational::from(8), Rational::from(12));
        ir11 /= &Rational::from(4);
        assert_eq!(ir11, inf(Rational::from(2), Rational::from(3)));

        // Test DivAssign with i64
        let mut ir12 = inf(Rational::from(8), Rational::from(12));
        ir12 /= 2;
        assert_eq!(ir12, inf(Rational::from(4), Rational::from(6)));
    }

    #[test]
    fn test_mul_inf_rationals() {
        // Test MulAssign with InfRational
        // (a + bε) * (c + dε) = ac + (ad + bc)ε
        let mut ir = inf(Rational::from(2), Rational::from(3)); // 2 + 3ε
        ir *= inf(Rational::from(4), Rational::from(5)); // * (4 + 5ε)
        // = 2*4 + (2*5 + 3*4)ε = 8 + 22ε
        assert_eq!(ir, inf(Rational::from(8), Rational::from(22)));
    }

    #[test]
    fn test_div_inf_rationals() {
        // Test DivAssign with InfRational
        // (a + bε) / (c + dε) = a/c + (b*c - a*d)/(c*c) ε
        let mut ir = inf(Rational::from(8), Rational::from(22)); // 8 + 22ε
        ir /= inf(Rational::from(4), Rational::from(5)); // / (4 + 5ε)
        // = 8/4 + (22*4 - 8*5)/(4*4) ε = 2 + (88-40)/16 ε = 2 + 3ε
        assert_eq!(ir, inf(Rational::from(2), Rational::from(3)));
    }

    #[test]
    fn test_neg_operator() {
        let ir = inf(Rational::from(5), Rational::from(3));
        let neg = -ir;
        assert_eq!(neg, inf(Rational::from(-5), Rational::from(-3)));
    }

    #[test]
    fn test_display_variations() {
        // Test with zero infinitesimal part
        let ir1 = InfRational::from(Rational::from(5));
        assert_eq!(format!("{}", ir1), "5");

        // Test with only infinitesimal part (rat = 0)
        let ir2 = inf(Rational::ZERO, Rational::from(3));
        assert_eq!(format!("{}", ir2), "3ε");

        // Test with positive infinitesimal
        let ir3 = inf(Rational::from(2), Rational::from(3));
        assert_eq!(format!("{}", ir3), "2 + 3ε");

        // Test with negative infinitesimal
        let ir4 = inf(Rational::from(2), Rational::from(-3));
        assert_eq!(format!("{}", ir4), "2 - 3ε");
    }

    #[test]
    fn test_helper_functions() {
        // Test i_i
        let ir1 = InfRational::from(42);
        assert_eq!(ir1, InfRational::from(42));

        // Test InfRational::from
        let ir2 = InfRational::from(Rational::new(3, 4));
        assert_eq!(ir2, InfRational::from(Rational::new(3, 4)));

        // Test inf_i
        let ir3 = inf_i(5);
        assert_eq!(ir3.rat, Rational::ZERO);
        assert_eq!(ir3.inf, Rational::from(5));

        // Test inf
        let ir4 = inf(Rational::from(1), Rational::from(2));
        assert_eq!(ir4.rat, Rational::from(1));
        assert_eq!(ir4.inf, Rational::from(2));
    }
}
