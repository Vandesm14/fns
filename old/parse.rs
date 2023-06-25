//!

use core::{ops::{Deref, DerefMut}, fmt::{self, Write}, iter};

use chumsky::{
    prelude::*,
    container::Container,
    error::Error,
    input::{SpannedInput, ValueInput},
};
use lasso::{Interner, Key};

use crate::lex::{Ident, Side, Token};

///
pub fn parser<'source, K, S, I, O, E>(
) -> impl Parser<'source, I, O, extra::Full<E, S, ()>> + Clone
where
    K: 'source + Key,
    S: 'source + Interner<K>,
    I: ValueInput<'source, Token = Token<K>>,
    O: Container<(Stmt<K, I::Span>, I::Span)>,
    E: 'source + Error<'source, I>,
{
    let ident = select! { Token::Ident(ident) => ident };

    let expr = recursive(|expr| {
        let list_item = ident
            .clone()
            .map_with_span(|ident, span| (ident, span))
            .map(Expr::Ident)
            .map_with_span(|expr, span| (expr, span))
            .or(expr);

        let list = list_item
            .repeated()
            .collect()
            .delimited_by(
                just(Token::Bracket(Side::Left)),
                just(Token::Bracket(Side::Right)),
            )
            .map(List);

        list.map_with_span(|list, span| (list, span))
            .map(Expr::List)
            .map_with_span(|expr, span| (expr, span))
            .recover_with(via_parser(nested_delimiters(
                Token::Bracket(Side::Left),
                Token::Bracket(Side::Right),
                [],
                |span| (Expr::Error, span),
            )))
    });

    let list_item = ident
        .map_with_span(|ident, span| (ident, span))
        .map(Expr::Ident)
        .map_with_span(|expr, span| (expr, span))
        .or(expr);

    let list = list_item
        .repeated()
        .collect()
        .delimited_by(
            just(Token::Bracket(Side::Left)),
            just(Token::Bracket(Side::Right)),
        )
        .map(List);

    let stmt = list
        .map_with_span(|list, span| (list, span))
        .map(Stmt::List)
        .map_with_span(|stmt, span| (stmt, span))
        .recover_with(via_parser(nested_delimiters(
            Token::Bracket(Side::Left),
            Token::Bracket(Side::Right),
            [],
            |span| (Stmt::Error, span),
        )));

    stmt.recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

///
pub type ParserInput<'source, 'tokens, K, S> =
    SpannedInput<Token<K>, S, &'tokens [(Token<K>, S)]>;

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
    type Target = [(Expr<K, S>, S)];

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
