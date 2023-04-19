use chumsky::{
  container::Container, error::Error, input::StrInput, prelude::*, util::Maybe,
};
use lasso::{Interner, Key};

pub fn lexer<'source, K, S, I, O, E>(
) -> impl Parser<'source, I, O, extra::Full<E, S, ()>> + Clone
where
  K: Key,
  S: 'source + Interner<K>,
  I: StrInput<'source, char>,
  O: Container<(Token<K>, I::Span)>,
  E: 'source + Error<'source, I>,
{
  let nil = text::keyword("nil").to(Token::Nil);

  let r#bool = choice((
    text::keyword("true").to(Token::Bool(true)),
    text::keyword("false").to(Token::Bool(false)),
  ));

  let int = just('-')
    .or_not()
    .then(text::int(10))
    .slice()
    .try_map(|s, span| {
      str::parse(s).map_err(|_| {
        E::expected_found(
          [Some(Maybe::Val('0'))],
          s.chars().next().map(Maybe::Val),
          span,
        )
      })
    })
    .map(Token::Int);

  let float = just('-')
    .or_not()
    .then(text::int(10))
    .then(
      just('.').then(text::digits(10)).then(
        one_of("eE")
          .then(one_of("+-").or_not())
          .then(text::digits(10))
          .or_not(),
      ),
    )
    .slice()
    .try_map(|s, span| {
      str::parse(s).map_err(|_| {
        E::expected_found(
          [Some(Maybe::Val('0'))],
          s.chars().next().map(Maybe::Val),
          span,
        )
      })
    })
    .map(Token::Float);

  let r#str = {
    let escape = just('\\')
      .then(choice((
        just('\\'),
        just('/'),
        just('"'),
        just('b').to('\x08'),
        just('f').to('\x0c'),
        just('n').to('\n'),
        just('r').to('\r'),
        just('t').to('\t'),
        just('u').ignore_then(text::digits(16).exactly(4).slice().validate(
          |s, span, emitter| {
            char::from_u32(u32::from_str_radix(s, 16).unwrap()).unwrap_or_else(
              || {
                emitter.emit(E::expected_found(
                  [Some(Maybe::Val('0')), Some(Maybe::Val('a'))],
                  s.chars().next().map(Maybe::Val),
                  span,
                ));
                '\u{fffd}' // unicode replacement character
              },
            )
          },
        )),
      )))
      .ignored()
      .boxed();

    none_of("\\\"\n")
      .ignored()
      .or(escape)
      .repeated()
      .slice()
      .map_with_state(|s, _, state: &mut S| Token::Str(state.get_or_intern(s)))
      .delimited_by(just('"'), just('"'))
  };

  const IDENT_CHARS: &str = "_.+-*/=<>!";

  let ident = any()
    .filter(|&ch: &char| ch.is_alphabetic() || IDENT_CHARS.contains(ch))
    .then(
      any()
        .filter(|&ch: &char| ch.is_alphanumeric() || IDENT_CHARS.contains(ch))
        .repeated(),
    )
    .slice()
    .map_with_state(|s, _, state: &mut S| Token::Ident(state.get_or_intern(s)));

  let ctrl = choice((
    just('(').to(Token::LParen),
    just(')').to(Token::RParen),
    just('[').to(Token::LBracket),
    just(']').to(Token::RBracket),
    just('\'').to(Token::Apostrophe),
  ));

  let token = float
    .or(int)
    .or(r#str)
    .or(ctrl)
    .or(r#bool)
    .or(nil)
    .or(ident);

  let comment = just(";;")
    .then(any().and_is(just('\n').not()).repeated())
    .padded();

  token
    .map_with_span(|tok, span| (tok, span))
    .padded()
    .padded_by(comment.repeated())
    .recover_with(skip_then_retry_until(any().ignored(), end()))
    .repeated()
    .collect()
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Token<K> {
  Nil,
  Bool(bool),
  Int(i64),
  Float(f64),
  Str(K),

  Ident(K),

  LParen,
  RParen,
  LBracket,
  RBracket,
  Apostrophe,
}
