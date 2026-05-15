use crate::{VarId, rational::Rational};
use std::{
    collections::HashMap,
    fmt,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lin {
    pub vars: HashMap<VarId, Rational>,
    pub known_term: Rational,
}

/// A linear expression represented as a sum of variables with rational coefficients plus a known term.
///
/// This struct represents a linear combination of variables with rational coefficients,
/// along with a constant term. It supports variable substitution.
impl Lin {
    pub fn new(vars: HashMap<VarId, Rational>, known_term: Rational) -> Self {
        Lin { vars, known_term }
    }

    pub fn new_var(var: VarId, coeff: Rational) -> Self {
        let mut vars = HashMap::new();
        vars.insert(var, coeff);
        Lin::new(vars, Rational::ZERO)
    }

    /// Substitutes a variable with another linear expression.
    ///
    /// If this expression is $L$ and the substitution is $x_i = E$, this method
    /// calculates $L[x_i \mapsto E]$.
    ///
    /// Mathematically, if $L = a_i x_i + \sum a_j x_j + K$ and $x_i = \sum b_k x_k + K'$,
    /// the new expression becomes:
    /// $$L' = a_i \left( \sum b_k x_k + K' \right) + \sum a_j x_j + K$$
    ///
    /// # Arguments
    ///
    /// * `var` - The index ($i$) of the variable to be substituted out.
    /// * `lin` - The linear expression ($E$) to substitute in its place.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(added, removed)` of `Vec<VarId>` containing:
    /// * `added`: Variable indices that were not in the expression but now have non-zero coefficients.
    /// * `removed`: Variable indices that previously had non-zero coefficients but are now zero
    ///   (including the substituted `var`).
    ///
    /// # Panics
    ///
    /// Panics if the variable to substitute is not present in this expression.
    pub fn substitute(&mut self, var: VarId, lin: &Lin) -> (Vec<VarId>, Vec<VarId>) {
        assert!(self.vars.contains_key(&var));
        let mut added = Vec::new();
        let mut removed = Vec::new();
        let coeff = self.vars.remove(&var).unwrap();
        for (v, c) in &lin.vars {
            if let Some(old_coeff) = self.vars.get_mut(v) {
                *old_coeff += &(c * coeff);
                if old_coeff.is_zero() {
                    self.vars.remove(v);
                    removed.push(*v);
                }
            } else {
                self.vars.insert(*v, c * coeff);
                added.push(*v);
            }
        }
        self.known_term += &(lin.known_term * coeff);
        (added, removed)
    }
}

impl From<Rational> for Lin {
    fn from(value: Rational) -> Self {
        Lin::new(HashMap::new(), value)
    }
}

impl From<i64> for Lin {
    fn from(value: i64) -> Self {
        Lin::new(HashMap::new(), Rational::from(value))
    }
}

impl From<VarId> for Lin {
    fn from(var: VarId) -> Self {
        Lin::new_var(var, Rational::from(1))
    }
}

pub fn vc(idx: VarId, coeff: i64) -> Lin {
    Lin::new_var(idx, Rational::from(coeff))
}

impl fmt::Display for Lin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Sort terms to ensure deterministic formatting regardless of HashMap iteration order.
        let mut terms: Vec<(VarId, &Rational)> = self.vars.iter().map(|(var, coeff)| (*var, coeff)).collect();
        terms.sort_unstable_by_key(|(var, _)| var.0);

        let mut first = true;
        for (var, coeff) in terms {
            if first {
                if coeff.is_positive() {
                    if coeff == &Rational::from(1) {
                        write!(f, "{}", var)?;
                    } else {
                        write!(f, "{}*{}", coeff, var)?;
                    }
                } else if coeff == &Rational::from(-1) {
                    write!(f, "-{}", var)?;
                } else {
                    write!(f, "-{}*{}", -coeff, var)?;
                }
                first = false;
            } else if coeff.is_positive() {
                if coeff == &Rational::from(1) {
                    write!(f, " + {}", var)?;
                } else {
                    write!(f, " + {}*{}", coeff, var)?;
                }
            } else if coeff == &Rational::from(-1) {
                write!(f, " - {}", var)?;
            } else {
                write!(f, " - {}*{}", -coeff, var)?;
            }
        }
        if first {
            write!(f, "{}", self.known_term)
        } else if !self.known_term.is_zero() {
            if self.known_term.is_positive() { write!(f, " + {}", self.known_term) } else { write!(f, " - {}", -self.known_term) }
        } else {
            Ok(())
        }
    }
}

impl AddAssign<Lin> for Lin {
    fn add_assign(&mut self, other: Lin) {
        for (var, coeff) in &other.vars {
            *self.vars.entry(*var).or_insert(Rational::ZERO) += coeff;
        }
        self.known_term += &other.known_term;
    }
}

impl AddAssign<Rational> for Lin {
    fn add_assign(&mut self, other: Rational) {
        self.known_term += other;
    }
}

impl AddAssign<&Lin> for Lin {
    fn add_assign(&mut self, other: &Lin) {
        for (var, coeff) in &other.vars {
            *self.vars.entry(*var).or_insert(Rational::ZERO) += coeff;
        }
        self.known_term += &other.known_term;
    }
}

impl AddAssign<&Rational> for Lin {
    fn add_assign(&mut self, other: &Rational) {
        self.known_term += other;
    }
}

impl Add<Lin> for Lin {
    type Output = Lin;

    fn add(self, other: Lin) -> Lin {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<Lin> for &Lin {
    type Output = Lin;

    fn add(self, other: Lin) -> Lin {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl Add<&Lin> for Lin {
    type Output = Lin;

    fn add(self, other: &Lin) -> Lin {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<&Lin> for &Lin {
    type Output = Lin;

    fn add(self, other: &Lin) -> Lin {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl Add<Rational> for Lin {
    type Output = Lin;

    fn add(self, other: Rational) -> Lin {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<Rational> for &Lin {
    type Output = Lin;

    fn add(self, other: Rational) -> Lin {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl Add<&Rational> for Lin {
    type Output = Lin;

    fn add(self, other: &Rational) -> Lin {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<&Rational> for &Lin {
    type Output = Lin;

    fn add(self, other: &Rational) -> Lin {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl Add<Lin> for Rational {
    type Output = Lin;

    fn add(self, other: Lin) -> Lin {
        let mut result = other.clone();
        result += &self;
        result
    }
}

impl Add<Lin> for &Rational {
    type Output = Lin;

    fn add(self, other: Lin) -> Lin {
        let mut result = other.clone();
        result += self;
        result
    }
}

impl Add<&Lin> for Rational {
    type Output = Lin;

    fn add(self, other: &Lin) -> Lin {
        let mut result = other.clone();
        result += &self;
        result
    }
}

impl Add<&Lin> for &Rational {
    type Output = Lin;

    fn add(self, other: &Lin) -> Lin {
        let mut result = other.clone();
        result += self;
        result
    }
}

impl SubAssign<Lin> for Lin {
    fn sub_assign(&mut self, other: Lin) {
        for (var, coeff) in &other.vars {
            *self.vars.entry(*var).or_insert(Rational::ZERO) -= coeff;
        }
        self.known_term -= &other.known_term;
    }
}

impl SubAssign<Rational> for Lin {
    fn sub_assign(&mut self, other: Rational) {
        self.known_term -= other;
    }
}

impl SubAssign<&Lin> for Lin {
    fn sub_assign(&mut self, other: &Lin) {
        for (var, coeff) in &other.vars {
            *self.vars.entry(*var).or_insert(Rational::ZERO) -= coeff;
        }
        self.known_term -= &other.known_term;
    }
}

impl SubAssign<&Rational> for Lin {
    fn sub_assign(&mut self, other: &Rational) {
        self.known_term -= other;
    }
}

impl Sub<Lin> for Lin {
    type Output = Lin;

    fn sub(self, other: Lin) -> Lin {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl Sub<Lin> for &Lin {
    type Output = Lin;

    fn sub(self, other: Lin) -> Lin {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl Sub<&Lin> for Lin {
    type Output = Lin;

    fn sub(self, other: &Lin) -> Lin {
        let mut result = self;
        result -= other;
        result
    }
}

impl Sub<&Lin> for &Lin {
    type Output = Lin;

    fn sub(self, other: &Lin) -> Lin {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl Sub<Rational> for Lin {
    type Output = Lin;

    fn sub(self, other: Rational) -> Lin {
        let mut result = self;
        result -= other;
        result
    }
}

impl Sub<Rational> for &Lin {
    type Output = Lin;

    fn sub(self, other: Rational) -> Lin {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl Sub<&Rational> for Lin {
    type Output = Lin;

    fn sub(self, other: &Rational) -> Lin {
        let mut result = self;
        result -= other;
        result
    }
}

impl Sub<&Rational> for &Lin {
    type Output = Lin;

    fn sub(self, other: &Rational) -> Lin {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl Sub<Lin> for Rational {
    type Output = Lin;

    fn sub(self, other: Lin) -> Lin {
        let mut result = other.clone();
        for coeff in result.vars.values_mut() {
            *coeff = -*coeff;
        }
        result.known_term = self - result.known_term;
        result
    }
}

impl Sub<Lin> for &Rational {
    type Output = Lin;

    fn sub(self, other: Lin) -> Lin {
        let mut result = other.clone();
        for coeff in result.vars.values_mut() {
            *coeff = -*coeff;
        }
        result.known_term = self - result.known_term;
        result
    }
}

impl Sub<&Lin> for Rational {
    type Output = Lin;

    fn sub(self, other: &Lin) -> Lin {
        let mut result = other.clone();
        for coeff in result.vars.values_mut() {
            *coeff = -*coeff;
        }
        result.known_term = self - result.known_term;
        result
    }
}

impl Sub<&Lin> for &Rational {
    type Output = Lin;

    fn sub(self, other: &Lin) -> Lin {
        let mut result = other.clone();
        for coeff in result.vars.values_mut() {
            *coeff = -*coeff;
        }
        result.known_term = self - result.known_term;
        result
    }
}

impl MulAssign<Rational> for Lin {
    fn mul_assign(&mut self, other: Rational) {
        for coeff in self.vars.values_mut() {
            *coeff *= other;
        }
        self.known_term *= other;
    }
}

impl MulAssign<&Rational> for Lin {
    fn mul_assign(&mut self, other: &Rational) {
        for coeff in self.vars.values_mut() {
            *coeff *= other;
        }
        self.known_term *= other;
    }
}

impl Mul<Rational> for Lin {
    type Output = Lin;

    fn mul(self, other: Rational) -> Lin {
        let mut result = self;
        result *= other;
        result
    }
}

impl Mul<Rational> for &Lin {
    type Output = Lin;

    fn mul(self, other: Rational) -> Lin {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl Mul<&Rational> for Lin {
    type Output = Lin;

    fn mul(self, other: &Rational) -> Lin {
        let mut result = self;
        result *= other;
        result
    }
}

impl Mul<&Rational> for &Lin {
    type Output = Lin;

    fn mul(self, other: &Rational) -> Lin {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl DivAssign<Rational> for Lin {
    fn div_assign(&mut self, other: Rational) {
        for coeff in self.vars.values_mut() {
            *coeff /= other;
        }
        self.known_term /= other;
    }
}

impl DivAssign<&Rational> for Lin {
    fn div_assign(&mut self, other: &Rational) {
        for coeff in self.vars.values_mut() {
            *coeff /= other;
        }
        self.known_term /= other;
    }
}

impl Div<Rational> for Lin {
    type Output = Lin;

    fn div(self, other: Rational) -> Lin {
        let mut result = self;
        result /= other;
        result
    }
}

impl Div<Rational> for &Lin {
    type Output = Lin;

    fn div(self, other: Rational) -> Lin {
        let mut result = self.clone();
        result /= other;
        result
    }
}

impl Div<&Rational> for Lin {
    type Output = Lin;

    fn div(self, other: &Rational) -> Lin {
        let mut result = self;
        result /= other;
        result
    }
}

impl Div<&Rational> for &Lin {
    type Output = Lin;

    fn div(self, other: &Rational) -> Lin {
        let mut result = self.clone();
        result /= other;
        result
    }
}

impl Neg for Lin {
    type Output = Lin;

    fn neg(self) -> Lin {
        let mut result = self;
        for coeff in result.vars.values_mut() {
            *coeff = -*coeff;
        }
        // Do the same for the known_term
        result.known_term = -result.known_term;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rational::Rational;
    use std::collections::HashMap;

    #[test]
    fn test_new_and_display() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::new(1, 2)), (VarId(2), Rational::new(-3, 4))]), Rational::from(5));

        // Display representation depends on map iteration order
        let s = format!("{}", lin);
        assert!(s == "1/2*x1 - 3/4*x2 + 5" || s == "-3/4*x2 + 1/2*x1 + 5", "Unexpected display: {}", s);
    }

    #[test]
    fn test_add_lin() {
        let lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        let lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(3))]), Rational::from(4));

        let sum = lin1 + lin2;

        let expected = Lin::new(HashMap::from([(VarId(1), Rational::from(3)), (VarId(2), Rational::from(3))]), Rational::from(6));

        assert_eq!(sum, expected);
    }

    #[test]
    fn test_add_rational() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        let sum = lin + Rational::from(3);
        let expected = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(5));

        assert_eq!(sum, expected);
    }

    #[test]
    fn test_sub_lin() {
        let lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        let lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(3))]), Rational::from(4));

        let diff = lin1 - lin2;

        let expected = Lin::new(HashMap::from([(VarId(1), Rational::from(-1)), (VarId(2), Rational::from(-3))]), Rational::from(-2));

        assert_eq!(diff, expected);
    }

    #[test]
    fn test_sub_rational() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        let diff = lin - Rational::from(3);
        let expected = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(-1));

        assert_eq!(diff, expected);
    }

    #[test]
    fn test_mul_rational() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::new(1, 2))]), Rational::new(3, 4));
        let product = lin * Rational::from(2);
        let expected = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::new(3, 2));

        assert_eq!(product, expected);
    }

    #[test]
    fn test_div_rational() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::new(3, 2));
        let quotient = lin / Rational::from(2);
        let expected = Lin::new(HashMap::from([(VarId(1), Rational::new(1, 2))]), Rational::new(3, 4));

        assert_eq!(quotient, expected);
    }

    #[test]
    fn test_neg() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::new(1, 2))]), Rational::new(-3, 4));
        let neg_lin = -lin;
        let expected = Lin::new(HashMap::from([(VarId(1), Rational::new(-1, 2))]), Rational::new(3, 4));

        assert_eq!(neg_lin, expected);
    }

    #[test]
    fn test_substitute() {
        // 2*x1 + 3*x2 + 5
        let mut lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(3))]), Rational::from(5));
        // substitute x1 with (4*x3 + 1)
        let lin_sub = Lin::new(HashMap::from([(VarId(3), Rational::from(4))]), Rational::from(1));
        lin1.substitute(VarId(1), &lin_sub);
        // expected = 3*x2 + 8*x3 + 7
        let expected = Lin::new(HashMap::from([(VarId(2), Rational::from(3)), (VarId(3), Rational::from(8))]), Rational::from(7));

        assert_eq!(lin1, expected);
    }

    #[test]
    fn test_substitute_combine() {
        // 2*x1 + 3*x2
        let mut lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(3))]), Rational::ZERO);
        // substitute x1 with (x2 + 1)
        let lin_sub = Lin::new(HashMap::from([(VarId(2), Rational::from(1))]), Rational::from(1));
        lin1.substitute(VarId(1), &lin_sub);
        // expected = 5*x2 + 2
        let expected = Lin::new(HashMap::from([(VarId(2), Rational::from(5))]), Rational::from(2));

        assert_eq!(lin1, expected);
    }
    #[test]
    fn test_substitute_merge_and_cancel() {
        // Original: 1x + 2y + 0
        let mut expr = Lin::new(HashMap::from([(VarId(1), Rational::from(1)), (VarId(2), Rational::from(2))]), Rational::ZERO);

        // Substitution: x = -2y + 10
        let sub = Lin::new(HashMap::from([(VarId(2), Rational::from(-2))]), Rational::from(10));

        // Result should be: (-2y + 10) + 2y => 0y + 10 => 10
        expr.substitute(VarId(1), &sub);

        // Verify that 'y' (index 2) was removed entirely because its coefficient became 0
        assert!(expr.vars.is_empty());
        assert_eq!(expr.known_term, Rational::from(10));
    }

    #[test]
    #[should_panic]
    fn test_substitute_missing_var() {
        let mut lin = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::ZERO);
        let lin_sub = Lin::new(HashMap::new(), Rational::ZERO);
        // Panic: Variable 2 not in lin
        lin.substitute(VarId(2), &lin_sub);
    }

    #[test]
    fn test_display_edge_cases() {
        // Test with coefficient -1 as first term
        let lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(-1))]), Rational::ZERO);
        assert_eq!(format!("{}", lin1), "-x1");

        // Test with coefficient -1 as non-first term
        let lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(-1))]), Rational::ZERO);
        let s = format!("{}", lin2);
        assert!(s.contains("-x") || s.contains("- x"));

        // Test with negative coefficient (not -1) as first term
        let lin3 = Lin::new(HashMap::from([(VarId(1), Rational::from(-3))]), Rational::ZERO);
        assert_eq!(format!("{}", lin3), "-3*x1");

        // Test with positive coefficient in later terms
        let lin4 = Lin::new(HashMap::from([(VarId(1), Rational::from(1)), (VarId(2), Rational::from(3))]), Rational::ZERO);
        let s = format!("{}", lin4);
        assert!(s.contains("+") || s.contains("x1") && s.contains("x2"));

        // Test with coefficient +1 as non-first positive term (line 108)
        let lin_pos_one = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(1))]), Rational::ZERO);
        let s = format!("{}", lin_pos_one);
        // Should contain "+ x2" (not "+ 1*x2")
        assert!(s.contains("+ x") || s.contains("+x"));

        // Test with negative coefficient (not -1) as non-first term (line 113)
        let lin_neg = Lin::new(HashMap::from([(VarId(1), Rational::from(2)), (VarId(2), Rational::from(-5))]), Rational::ZERO);
        let s = format!("{}", lin_neg);
        // Should contain "- 5*x" format
        assert!(s.contains("- 5*x") || s.contains("-5*x"));

        // Test with constant term only
        let lin5 = Lin::new(HashMap::new(), Rational::from(5));
        assert_eq!(format!("{}", lin5), "5");

        // Test with positive constant term
        let lin6 = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));
        let s = format!("{}", lin6);
        assert!(s.contains("+ 3"));

        // Test with negative constant term
        let lin7 = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(-3));
        let s = format!("{}", lin7);
        assert!(s.contains("- 3"));

        // Test expression with zero constant
        let lin8 = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::ZERO);
        let s = format!("{}", lin8);
        assert!(!s.contains("+ 0") && !s.contains("- 0"));
    }

    #[test]
    fn test_add_lin_variations() {
        let lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        let lin2 = Lin::new(HashMap::from([(VarId(2), Rational::from(3))]), Rational::from(4));

        // Test Lin + Lin
        let res1 = lin1.clone() + lin2.clone();
        assert_eq!(res1.vars.get(&VarId(1)), Some(&Rational::from(1)));
        assert_eq!(res1.vars.get(&VarId(2)), Some(&Rational::from(3)));
        assert_eq!(res1.known_term, Rational::from(6));

        // Test &Lin + Lin
        let res2 = &lin1 + lin2.clone();
        assert_eq!(res2.known_term, Rational::from(6));

        // Test Lin + &Lin
        let res3 = lin1.clone() + &lin2;
        assert_eq!(res3.known_term, Rational::from(6));

        // Test &Lin + &Lin
        let res4 = &lin1 + &lin2;
        assert_eq!(res4.known_term, Rational::from(6));
    }

    #[test]
    fn test_add_rational_variations() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        let rat_val = Rational::from(3);

        // Test Lin + Rational
        let res1 = lin.clone() + rat_val;
        assert_eq!(res1.known_term, Rational::from(5));

        // Test &Lin + Rational
        let res2 = &lin + rat_val;
        assert_eq!(res2.known_term, Rational::from(5));

        // Test Lin + &Rational
        let res3 = lin.clone() + &rat_val;
        assert_eq!(res3.known_term, Rational::from(5));

        // Test &Lin + &Rational
        let res4 = &lin + &rat_val;
        assert_eq!(res4.known_term, Rational::from(5));

        // Test Rational + Lin
        let res5 = rat_val + lin.clone();
        assert_eq!(res5.known_term, Rational::from(5));

        // Test Rational + &Lin
        let res6 = rat_val + &lin;
        assert_eq!(res6.known_term, Rational::from(5));

        // Test &Rational + Lin
        let res7 = &rat_val + lin.clone();
        assert_eq!(res7.known_term, Rational::from(5));

        // Test &Rational + &Lin
        let res8 = &rat_val + &lin;
        assert_eq!(res8.known_term, Rational::from(5));
    }

    #[test]
    fn test_sub_lin_variations() {
        let lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(5))]), Rational::from(10));
        let lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));

        // Test Lin - Lin
        let res1 = lin1.clone() - lin2.clone();
        assert_eq!(res1.vars.get(&VarId(1)), Some(&Rational::from(3)));
        assert_eq!(res1.known_term, Rational::from(7));

        // Test &Lin - Lin
        let res2 = &lin1 - lin2.clone();
        assert_eq!(res2.known_term, Rational::from(7));

        // Test Lin - &Lin
        let res3 = lin1.clone() - &lin2;
        assert_eq!(res3.known_term, Rational::from(7));

        // Test &Lin - &Lin
        let res4 = &lin1 - &lin2;
        assert_eq!(res4.known_term, Rational::from(7));
    }

    #[test]
    fn test_sub_rational_variations() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(10));
        let rat_val = Rational::from(3);

        // Test Lin - Rational
        let res1 = lin.clone() - rat_val;
        assert_eq!(res1.known_term, Rational::from(7));

        // Test &Lin - Rational
        let res2 = &lin - rat_val;
        assert_eq!(res2.known_term, Rational::from(7));

        // Test Lin - &Rational
        let res3 = lin.clone() - &rat_val;
        assert_eq!(res3.known_term, Rational::from(7));

        // Test &Lin - &Rational
        let res4 = &lin - &rat_val;
        assert_eq!(res4.known_term, Rational::from(7));

        // Test Rational - Lin (coefficients should be negated)
        let res5 = rat_val - lin.clone();
        assert_eq!(res5.vars.get(&VarId(1)), Some(&Rational::from(-1)));
        assert_eq!(res5.known_term, Rational::from(-7));

        // Test Rational - &Lin
        let res6 = rat_val - &lin;
        assert_eq!(res6.vars.get(&VarId(1)), Some(&Rational::from(-1)));
        assert_eq!(res6.known_term, Rational::from(-7));

        // Test &Rational - Lin
        let res7 = &rat_val - lin.clone();
        assert_eq!(res7.vars.get(&VarId(1)), Some(&Rational::from(-1)));
        assert_eq!(res7.known_term, Rational::from(-7));

        // Test &Rational - &Lin
        let res8 = &rat_val - &lin;
        assert_eq!(res8.vars.get(&VarId(1)), Some(&Rational::from(-1)));
        assert_eq!(res8.known_term, Rational::from(-7));
    }

    #[test]
    fn test_mul_rational_variations() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));
        let rat_val = Rational::from(4);

        // Test Lin * Rational
        let res1 = lin.clone() * rat_val;
        assert_eq!(res1.vars.get(&VarId(1)), Some(&Rational::from(8)));
        assert_eq!(res1.known_term, Rational::from(12));

        // Test &Lin * Rational
        let res2 = &lin * rat_val;
        assert_eq!(res2.known_term, Rational::from(12));

        // Test Lin * &Rational
        let res3 = lin.clone() * &rat_val;
        assert_eq!(res3.known_term, Rational::from(12));

        // Test &Lin * &Rational
        let res4 = &lin * &rat_val;
        assert_eq!(res4.known_term, Rational::from(12));
    }

    #[test]
    fn test_div_rational_variations() {
        let lin = Lin::new(HashMap::from([(VarId(1), Rational::from(8))]), Rational::from(12));
        let rat_val = Rational::from(4);

        // Test Lin / Rational
        let res1 = lin.clone() / rat_val;
        assert_eq!(res1.vars.get(&VarId(1)), Some(&Rational::from(2)));
        assert_eq!(res1.known_term, Rational::from(3));

        // Test &Lin / Rational
        let res2 = &lin / rat_val;
        assert_eq!(res2.known_term, Rational::from(3));

        // Test Lin / &Rational
        let res3 = lin.clone() / &rat_val;
        assert_eq!(res3.known_term, Rational::from(3));

        // Test &Lin / &Rational
        let res4 = &lin / &rat_val;
        assert_eq!(res4.known_term, Rational::from(3));
    }

    #[test]
    fn test_add_assign_variations() {
        // Test AddAssign<Lin>
        let mut lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        lin1 += Lin::new(HashMap::from([(VarId(2), Rational::from(3))]), Rational::from(4));
        assert_eq!(lin1.known_term, Rational::from(6));

        // Test AddAssign<&Lin>
        let mut lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        lin2 += &Lin::new(HashMap::from([(VarId(2), Rational::from(3))]), Rational::from(4));
        assert_eq!(lin2.known_term, Rational::from(6));

        // Test AddAssign<Rational>
        let mut lin3 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        lin3 += Rational::from(5);
        assert_eq!(lin3.known_term, Rational::from(7));

        // Test AddAssign<&Rational>
        let mut lin4 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(2));
        lin4 += &Rational::from(5);
        assert_eq!(lin4.known_term, Rational::from(7));
    }

    #[test]
    fn test_sub_assign_variations() {
        // Test SubAssign<Lin>
        let mut lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(5))]), Rational::from(10));
        lin1 -= Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));
        assert_eq!(lin1.vars.get(&VarId(1)), Some(&Rational::from(3)));
        assert_eq!(lin1.known_term, Rational::from(7));

        // Test SubAssign<&Lin>
        let mut lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(5))]), Rational::from(10));
        lin2 -= &Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));
        assert_eq!(lin2.known_term, Rational::from(7));

        // Test SubAssign<Rational>
        let mut lin3 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(10));
        lin3 -= Rational::from(3);
        assert_eq!(lin3.known_term, Rational::from(7));

        // Test SubAssign<&Rational>
        let mut lin4 = Lin::new(HashMap::from([(VarId(1), Rational::from(1))]), Rational::from(10));
        lin4 -= &Rational::from(3);
        assert_eq!(lin4.known_term, Rational::from(7));
    }

    #[test]
    fn test_mul_assign_variations() {
        // Test MulAssign<Rational>
        let mut lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));
        lin1 *= Rational::from(4);
        assert_eq!(lin1.vars.get(&VarId(1)), Some(&Rational::from(8)));
        assert_eq!(lin1.known_term, Rational::from(12));

        // Test MulAssign<&Rational>
        let mut lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(2))]), Rational::from(3));
        lin2 *= &Rational::from(4);
        assert_eq!(lin2.known_term, Rational::from(12));
    }

    #[test]
    fn test_div_assign_variations() {
        // Test DivAssign<Rational>
        let mut lin1 = Lin::new(HashMap::from([(VarId(1), Rational::from(8))]), Rational::from(12));
        lin1 /= Rational::from(4);
        assert_eq!(lin1.vars.get(&VarId(1)), Some(&Rational::from(2)));
        assert_eq!(lin1.known_term, Rational::from(3));

        // Test DivAssign<&Rational>
        let mut lin2 = Lin::new(HashMap::from([(VarId(1), Rational::from(8))]), Rational::from(12));
        lin2 /= &Rational::from(4);
        assert_eq!(lin2.known_term, Rational::from(3));
    }
}
