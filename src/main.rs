// use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{container::Container, error::Error, prelude::*, util::Maybe};
use std::fmt;

/*
  # Primitives

  ## Language

  Expressions: `(...)`
  Lists/Arrays/Sequences: `[...]`
  Strings: `"..."`
  Numbers: `1` `1.0` `-1` `-1.0`
  Booleans: `true` `false`
  Nil: `nil`
  Symbols: `/[a-zA-Z_-][a-zA-Z0-9_-]*`

  Variables: `(def x 2)` (use `def` to re-assign a variable)
  Functions: `(defn add [x y] (+ x y))`
  Conditionals: `(if (eq x 2)) "x is 2" "x is not 2")` `(if (eq x 2) "x is 2")`
  Loops: `(while (lt x 10) (println x) (set x (+ x 1)))`

  Arithmetic: `(+ 1 2)` `(- 1 2)` `(* 1 2)` `(/ 1 2)`
  Comparison: `(eq 1 2)` `(neq 1 2)` `(gt 1 2)` `(gte 1 2)` `(lt 1 2)` `(lte 1 2)`
  Arrays: `(def x [1 2 3])` `(get x 0)` `(set x 0 4)` `(len x)` `(push x 4)` `(pop x)`
*/

pub type Span = std::ops::Range<usize>;

#[derive(Clone, Debug, PartialEq)]
enum Token<'a> {
  Nil,
  Bool(bool),
  Num(f64),
  Str(&'a str),
  Symbol(&'a str),
  Ctrl(char),
}

impl<'a> fmt::Display for Token<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Token::Nil => write!(f, "nil"),
      Token::Bool(x) => write!(f, "{}", x),
      Token::Num(n) => write!(f, "{}", n),
      Token::Str(s) => write!(f, "{}", s),
      Token::Symbol(s) => write!(f, "{}", s),
      Token::Ctrl(c) => write!(f, "{}", c),
    }
  }
}

fn lexer<'source, O, E>(
) -> impl Parser<'source, &'source str, O, extra::Err<E>> + Clone
where
  O: Container<(Token<'source>, SimpleSpan)>,
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
      .ignored();

    none_of("\\\"")
      .ignored()
      .or(escape)
      .repeated()
      .slice()
      .map(Token::Str)
      .delimited_by(just('"'), just('"'))
  };

  // A parser for Symbols
  let symbol = any()
    .filter(|ch: &char| {
      ch.is_alphabetic() | ch.is_ascii_graphic() | ch.is_ascii_punctuation()
    })
    .repeated()
    .at_least(1)
    .slice()
    .map(Token::Symbol);

  // A parser for control characters
  let ctrl = one_of("()[]").map(Token::Ctrl);

  let token = num.or(string).or(ctrl).or(boolean).or(nil).or(symbol);

  token
    .map_with_span(|tok, span| (tok, span))
    .padded()
    .recover_with(skip_then_retry_until(any().ignored(), end()))
    .repeated()
    .collect()
}

fn main() {
  const CODE: &str = "(def x 2)\n(def x (+ x 1))";
  let (tokens, errs) =
    lexer::<Vec<_>, Rich<_>>().parse(CODE).into_output_errors();

  errs.into_iter().for_each(|err| {
    eprintln!("{}", err);
  });
  println!("Tokens: {:?}", tokens.unwrap());
}
