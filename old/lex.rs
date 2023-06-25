//!

use core::{
    fmt::{self, Write},
    ops::{Deref, DerefMut},
};

use chumsky::{
    container::Container, error::Error, input::StrInput, prelude::*,
};
use lasso::{Interner, Key};

///
pub fn lexer<'source, K, S, I, O, E>(
) -> impl Parser<'source, I, O, extra::Full<E, S, ()>> + Clone
where
    K: Key,
    S: 'source + Interner<K>,
    I: StrInput<'source, char>,
    O: Container<(Token<K>, I::Span)>,
    E: 'source + Error<'source, I>,
{
    let bracket = choice((just('(').to(Side::Left), just(')').to(Side::Right)))
        .map(Token::Bracket);

    let ident = {
        let ident = text::unicode::ident();

        let float = {
            let exp = one_of("eE")
                .then(one_of("+-").or_not())
                .then(text::digits(10))
                .slice();

            text::int(10)
                .then(just('.').then(text::digits(10)))
                .then(exp.or_not())
                .slice()
        };

        let int = text::int(10).slice();

        choice((one_of("`!$%^&*_-+=:;@'~#<,>.?/").slice(), ident, float, int))
            .repeated()
            .at_least(1)
            .slice()
            .map_with_state(|s, _, state: &mut S| Ident(state.get_or_intern(s)))
    };

    let token = bracket.or(ident.map(Token::Ident));

    let comment = just(';')
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    token
        .map_with_span(|token, span| (token, span))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

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
