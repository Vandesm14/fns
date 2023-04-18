use chumsky::{container::Container, error::Error, prelude::*, util::Maybe};
use core::fmt;
use lasso::{Rodeo, Spur};

use crate::Spanned;

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
  Nil,
  Bool(bool),
  Num(f64),
  Str(Spur),
  Symbol(Spur),
  LBracket,
  RBracket,
  LParen,
  RParen,
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Token::Nil => write!(f, "nil"),
      Token::Bool(x) => write!(f, "{}", x),
      Token::Num(n) => write!(f, "{}", n),
      // TODO: implement a proper formatter
      Token::Str(s) => write!(f, "<string {:?}>", s),
      // TODO: implement a proper formatter
      Token::Symbol(s) => write!(f, "<symbol {:?}>", s),
      Token::LBracket => write!(f, "["),
      Token::RBracket => write!(f, "]"),
      Token::LParen => write!(f, "("),
      Token::RParen => write!(f, ")"),
    }
  }
}

/// Performs lexical analysis on the source code and returns a list of tokens.
pub fn lexer<'source, O, E>(
) -> impl Parser<'source, &'source str, O, extra::Full<E, Rodeo, ()>> + Clone
where
  O: Container<Spanned<Token>>,
  E: 'source + Error<'source, &'source str>,
{
  // A parser for Nil
  let nil = text::keyword("nil").to(Token::Nil);

  // A parser for Booleans
  let boolean = choice((
    text::keyword("true").to(Token::Bool(true)),
    text::keyword("false").to(Token::Bool(false)),
  ));

  // A parser for Numbers
  let num = text::int(10)
    .then(
      just('.')
        .then(text::digits(10))
        .then(
          one_of("eE")
            .then(one_of("+-").or_not())
            .then(text::digits(10))
            .or_not(),
        )
        .or_not(),
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
    .map(Token::Num);

  // A parser for Strings
  let string = {
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
      .map_with_state(|s, _, state: &mut Rodeo| {
        Token::Str(state.get_or_intern(s))
      })
      .delimited_by(just('"'), just('"'))
  };

  // A parser for Symbols
  // let symbol = any()
  //   .filter(|ch: &char| {
  //     (ch.is_alphabetic() || ch.is_ascii_graphic() || ch.is_ascii_punctuation())
  //       && !"()[]\"".contains(*ch)
  //   })
  //   .repeated()
  //   .at_least(1)
  //   .slice()
  //   .map(Token::Symbol);

  const SYMBOL_CHARS: &str = "_.+-*/=<>!";

  let symbol = any()
    .filter(|&ch: &char| ch.is_alphabetic() || SYMBOL_CHARS.contains(ch))
    .then(
      any()
        .filter(|&ch: &char| ch.is_alphanumeric() || SYMBOL_CHARS.contains(ch))
        .repeated(),
    )
    .slice()
    .map_with_state(|s, _, state: &mut Rodeo| {
      Token::Symbol(state.get_or_intern(s))
    });

  // A parser for control characters
  let ctrl = choice((
    just('(').to(Token::LParen),
    just(')').to(Token::RParen),
    just('[').to(Token::LBracket),
    just(']').to(Token::RBracket),
  ));

  let token = num.or(string).or(ctrl).or(boolean).or(nil).or(symbol);

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
