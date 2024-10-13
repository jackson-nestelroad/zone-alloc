use core::{
    error::Error,
    fmt::Display,
};

/// A borrow error.
#[derive(Debug, PartialEq, Eq)]
pub enum BorrowError {
    /// The element is out of bounds.
    OutOfBounds,
    /// The element is already borrowed mutably.
    AlreadyBorrowedMutably,
    /// The element is already borrowed immutably.
    AlreadyBorrowed,
}

impl Display for BorrowError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::OutOfBounds => write!(f, "element is out of bounds"),
            Self::AlreadyBorrowedMutably => write!(f, "element is already borrowed mutably"),
            Self::AlreadyBorrowed => write!(f, "element is already borrowed"),
        }
    }
}

impl Error for BorrowError {}
