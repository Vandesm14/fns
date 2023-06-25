//!

use chumsky::{
    container::Container,
    input::{SpannedInput, ValueInput},
    prelude::*,
};
use lasso::{Interner, Key};

use crate::lex::token::{Side, Token};

use self::{
    ast::{Expr, List, Stmt},
    error::Error,
};

pub mod ast;
pub mod error;

///
pub fn parser<'source, K, S, I, O>(
) -> impl Parser<'source, I, O, extra::Full<Error<'source, K, I>, S, ()>> + Clone
where
    K: 'source + Key,
    S: 'source + Interner<K>,
    I: ValueInput<'source, Token = Token<K>>,
    O: Container<(Stmt<K, I::Span>, I::Span)>,
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
