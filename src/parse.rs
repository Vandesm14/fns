use chumsky::{
  container::Container, error::Error, input::SpannedInput, prelude::*,
};
use core::fmt;
use lasso::{Rodeo, Spur};

use crate::{lex::Token, Spanned};

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
  Nil,
  Bool(bool),
  Num(f64),
  Str(Spur),
  Symbol(Spur),
  List(Vec<Spanned<Self>>),
  Array(Vec<Spanned<Self>>),
  Break,
  Error,

  /// A group of expressions that should be evaluated together.
  Group(Vec<Self>),
}

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Expr::Nil => write!(f, "nil"),
      Expr::Bool(x) => write!(f, "{}", x),
      Expr::Num(n) => write!(f, "{}", n),
      // TODO: implement a proper formatter
      Expr::Str(s) => write!(f, "<string {:?}>", s),
      // TODO: implement a proper formatter
      Expr::Symbol(s) => write!(f, "<symbol {:?}>", s),
      Expr::List(xs) => {
        write!(f, "(")?;
        for (i, x) in xs.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          write!(f, "{}", x.0)?;
        }
        write!(f, ")")
      }
      Expr::Array(xs) => {
        write!(f, "[")?;
        for (i, x) in xs.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          write!(f, "{}", x.0)?;
        }
        write!(f, "]")
      }
      Expr::Break => write!(f, "break"),
      Expr::Error => write!(f, "error"),
      Expr::Group(xs) => {
        write!(f, "(")?;
        for (i, x) in xs.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          write!(f, "{}", x)?;
        }
        write!(f, ")")
      }
    }
  }
}

/// Convenience type for a <code>[SpannedInput]\<[Token]\></code>.
pub type ParserInput<'source, 'tokens> =
  SpannedInput<Token, SimpleSpan, &'tokens [Spanned<Token>]>;

/// Creates a parser which transforms [`Token`]s into [`Expr`]s.
pub fn parser<'source, 'tokens, O, E>() -> impl Parser<
  'tokens,
  ParserInput<'source, 'tokens>,
  O,
  extra::Full<E, Rodeo, ()>,
> + Clone
where
  'source: 'tokens,
  O: Container<Spanned<Expr>>,
  E: 'tokens + Error<'tokens, ParserInput<'source, 'tokens>>,
{
  recursive(|expr| {
    let atom = select! {
      Token::Nil => Expr::Nil,
      Token::Bool(b) => Expr::Bool(b),
      Token::Num(n) => Expr::Num(n),
      Token::Str(s) => Expr::Str(s),
      Token::Symbol(s) => Expr::Symbol(s),
    };

    let list = expr
      .clone()
      .repeated()
      .collect()
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .map(Expr::List)
      .boxed();

    let array = expr
      .repeated()
      .collect()
      .delimited_by(just(Token::LBracket), just(Token::RBracket))
      .map(Expr::Array)
      .boxed();

    atom
      .or(list)
      .or(array)
      .map_with_span(|expr, span| (expr, span))
      .recover_with(via_parser(nested_delimiters(
        Token::LParen,
        Token::RParen,
        [(Token::LBracket, Token::RBracket)],
        |span| (Expr::Error, span),
      )))
      .recover_with(via_parser(nested_delimiters(
        Token::LBracket,
        Token::RBracket,
        [(Token::LParen, Token::RParen)],
        |span| (Expr::Error, span),
      )))
      .boxed()
  })
  .recover_with(skip_then_retry_until(any().ignored(), end()))
  .repeated()
  .collect()
}
