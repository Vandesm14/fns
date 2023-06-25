//!

use core::{
    fmt::{self, Write},
    iter,
    ops::{Deref, DerefMut},
};

use lasso::Key;

use crate::lex::token::Ident;

/// A top-level statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Stmt<K, S> {
    /// An invalid [`Stmt`].
    Error,
    /// A [`List`].
    List((List<K, S>, S)),
}

impl<K, S> fmt::Display for Stmt<K, S>
where
    K: Key,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => f.write_str("<error>"),
            Self::List((list, _)) => fmt::Display::fmt(list, f),
        }
    }
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expr<K, S> {
    /// An invalid [`Expr`].
    Error,
    /// An [`Ident`].
    Ident((Ident<K>, S)),
    /// A [`List`].
    List((List<K, S>, S)),
}

impl<K, S> fmt::Display for Expr<K, S>
where
    K: Key,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => f.write_str("<error>"),
            Self::Ident((ident, _)) => fmt::Display::fmt(ident, f),
            Self::List((list, _)) => fmt::Display::fmt(list, f),
        }
    }
}

/// A sequence of [`Expr`]s.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct List<K, S>(pub Vec<(Expr<K, S>, S)>);

impl<K, S> Deref for List<K, S> {
    type Target = Vec<(Expr<K, S>, S)>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, S> DerefMut for List<K, S> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, S> fmt::Display for List<K, S>
where
    K: Key,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char('(')?;
        self.iter()
            .zip(iter::once("").chain(iter::repeat(" ")))
            .try_for_each(|((expr, _), sep)| {
                f.write_str(sep)?;
                fmt::Display::fmt(expr, f)
            })?;
        f.write_char(')')
    }
}
