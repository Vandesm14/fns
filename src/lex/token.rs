//!

use core::{
    fmt::{self, Write},
    ops::{Deref, DerefMut},
};

use lasso::Key;

///
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Token<K> {
    /// An [`Ident`].
    Ident(Ident<K>),
    /// A bracket: `(` or `)`.
    Bracket(Side),
}

impl<K> fmt::Display for Token<K>
where
    K: Key,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(ident) => fmt::Display::fmt(ident, f),
            Self::Bracket(side) => match side {
                Side::Left => f.write_char('('),
                Side::Right => f.write_char(')'),
            },
        }
    }
}

/// An identifier: `def`, `!`, `<=`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Ident<K>(pub K);

impl<K> Deref for Ident<K> {
    type Target = K;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K> DerefMut for Ident<K> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K> fmt::Display for Ident<K>
where
    K: Key,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<ident:{}>", self.into_usize())
    }
}

/// Represents either a [`Left`] or [`Right`] side.
///
/// [`Left`]: Self::Left
/// [`Right`]: Self::Right
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Side {
    /// Left-hand side.
    Left,
    /// Right-hand side.
    Right,
}
