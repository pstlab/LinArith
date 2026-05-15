use std::{fmt, ops::Deref};

#[derive(Debug, Clone, Copy, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct VarId(usize);

impl VarId {
    pub(crate) fn new(index: usize) -> Self {
        VarId(index)
    }
}

impl Deref for VarId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}
