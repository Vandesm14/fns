use chumsky::{
  container::Container,
  error::Error,
  input::{SpannedInput, ValueInput},
  prelude::*,
};
use lasso::{Interner, Key};

use crate::lex::Token;

pub fn parser<'source, K, S, I, O, E>(
) -> impl Parser<'source, I, O, extra::Full<E, S, ()>>
where
  K: 'source + Key,
  S: 'source + Interner<K>,
  I: ValueInput<'source, Token = Token<K>>,
  // TODO: make this (Expr<K>, I::Span)
  O: Container<Expr<K>>,
  E: 'source + Error<'source, I>,
{
  recursive(|expr| {
    let basic = select! {
      Token::Nil => Expr::Nil,
      Token::Bool(x) => Expr::Bool(x),
      Token::Int(x) => Expr::Int(x),
      Token::Float(x) => Expr::Float(x),
      Token::Ident(x) => Expr::Ident(x),
    };

    let r#str = select! { Token::Str(x) => x }
      .map_with_state(|s, _, state: &mut S| state.resolve(&s).to_string())
      .map(|s| Expr::Array(s.bytes().map(|b| Expr::Int(b as i64)).collect()));

    let array = expr
      .clone()
      .repeated()
      .collect()
      .delimited_by(just(Token::LBracket), just(Token::RBracket))
      .map(Expr::Array);

    let list = expr
      .repeated()
      .collect()
      .delimited_by(just(Token::LParen), just(Token::RParen));

    let call = list.clone().map(Expr::Call);

    let list = just(Token::Apostrophe).ignore_then(list).map(Expr::List);

    basic
      .or(r#str)
      .or(array)
      .or(list)
      .or(call)
      // .map_with_span(|expr, span| (expr, span))
      .recover_with(via_parser(nested_delimiters(
        Token::LParen,
        Token::RParen,
        [(Token::LBracket, Token::RBracket)],
        |_| Expr::Error,
        // |span| (Expr::Error, span),
      )))
      .recover_with(via_parser(nested_delimiters(
        Token::LBracket,
        Token::RBracket,
        [(Token::LParen, Token::RParen)],
        |_| Expr::Error,
        // |span| (Expr::Error, span),
      )))
  })
  .recover_with(skip_then_retry_until(any().ignored(), end()))
  .repeated()
  .collect()
}

pub type ParserInput<'source, 'tokens, K, S> =
  SpannedInput<Token<K>, S, &'tokens [(Token<K>, S)]>;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<K> {
  Nil,
  Bool(bool),
  Int(i64),
  Float(f64),

  Ident(K),

  Array(Vec<Self>),
  List(Vec<Self>),
  Call(Vec<Self>),

  Error,
}
