// use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, stream::Stream, Error};
use std::{collections::HashMap, env, fmt, fs};

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

  Variables: `(def x 2)` `(set x 3)`
  Functions: `(defn add [x y] (+ x y))`
  Conditionals: `(if (eq x 2)) "x is 2" "x is not 2")` `(if (eq x 2) "x is 2")`
  Loops: `(while (lt x 10) (println x) (set x (+ x 1)))`

  Arithmetic: `(+ 1 2)` `(- 1 2)` `(* 1 2)` `(/ 1 2)`
  Comparison: `(eq 1 2)` `(neq 1 2)` `(gt 1 2)` `(gte 1 2)` `(lt 1 2)` `(lte 1 2)`
  Arrays: `(def x [1 2 3])` `(get x 0)` `(set x 0 4)` `(len x)` `(push x 4)` `(pop x)`
*/

pub type Span = std::ops::Range<usize>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Token {
  Nil,
  Bool(bool),
  Num(String),
  Str(String),
  Symbol(String),
  Ctrl(char),
}

impl fmt::Display for Token {
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

fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
  // A parser for Nil
  let nil = just("nil").map(|_| Token::Nil);

  // A parser for Booleans
  let boolean = just("true").or(just("false")).map(|s| {
    if s == "true" {
      Token::Bool(true)
    } else {
      Token::Bool(false)
    }
  });

  // A parser for Numbers
  let num = text::int(10)
    .chain::<char, _, _>(just('.').chain(text::digits(10)).or_not().flatten())
    .collect::<String>()
    .map(Token::Num);

  // A parser for Strings
  let string = just('"')
    .ignore_then(filter(|c| *c != '"').repeated())
    .then_ignore(just('"'))
    .collect::<String>()
    .map(Token::Str);

  let ALPHA =
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string();
  let SYMBOLS = "+-*/=<>!&|".to_string();
  let NUMBERS = "0123456789".to_string();

  let SYMBOL = ALPHA + &SYMBOLS;

  // A parser for Symbols
  let symbol = one_of(SYMBOL.clone())
    .chain(one_of(SYMBOL + &NUMBERS).repeated())
    .collect::<String>()
    .map(Token::Symbol);

  // A parser for control characters
  let ctrl = one_of("()[]").map(|c| Token::Ctrl(c));

  let token = num
    .or(string)
    .or(ctrl)
    .or(boolean)
    .or(nil)
    .or(symbol)
    .recover_with(skip_then_retry_until([]));

  token
    .map_with_span(|tok, span| (tok, span))
    .padded()
    .repeated()
}

fn main() {
  const code: &str = "(+ 1 2)";
  let (tokens, errs) = lexer().parse_recovery(code);

  println!("Tokens: {:?}", tokens);
}
