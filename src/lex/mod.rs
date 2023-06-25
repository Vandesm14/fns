//!

use chumsky::{container::Container, input::StrInput, prelude::*};
use lasso::{Interner, Key};

use self::{
    error::Error,
    token::{Ident, Side, Token},
};

pub mod error;
pub mod token;

///
pub fn lexer<'source, K, S, I, O>(
) -> impl Parser<'source, I, O, extra::Full<Error<'source, I>, S, ()>> + Clone
where
    K: Key,
    S: 'source + Interner<K>,
    I: StrInput<'source, char>,
    O: Container<(Token<K>, I::Span)>,
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
            .try_map_with_state(|s, _, state: &mut S| {
                state.try_get_or_intern(s).map_err(Error::CannotIntern)
            })
            .map(Ident)
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
