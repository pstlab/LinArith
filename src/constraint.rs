use crate::Lin;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstraintId(pub usize);

impl fmt::Display for ConstraintId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "c{}", self.0)
    }
}

pub enum Constraint {
    Lt { lhs: Lin, rhs: Lin },
    LEq { lhs: Lin, rhs: Lin },
    Eq { lhs: Lin, rhs: Lin },
    GEq { lhs: Lin, rhs: Lin },
    Gt { lhs: Lin, rhs: Lin },
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Lt { lhs, rhs } => write!(f, "{} < {}", lhs, rhs),
            Constraint::LEq { lhs, rhs } => write!(f, "{} <= {}", lhs, rhs),
            Constraint::Eq { lhs, rhs } => write!(f, "{} == {}", lhs, rhs),
            Constraint::GEq { lhs, rhs } => write!(f, "{} >= {}", lhs, rhs),
            Constraint::Gt { lhs, rhs } => write!(f, "{} > {}", lhs, rhs),
        }
    }
}
