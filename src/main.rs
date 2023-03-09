// use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{
  container::Container, error::Error, input::SpannedInput, prelude::*,
  util::Maybe,
};
use std::{
  collections::{HashMap, HashSet},
  fmt,
};

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

  ## Builtins

  Variables: `(def x 2)` (use `def` to re-assign a variable)
  Functions: `(defn add [x y] (+ x y))`
  Conditionals: `(if (eq x 2)) "x is 2" "x is not 2")` `(if (eq x 2) "x is 2")`
  Loops: `(while (lt x 10) (println x) (set x (+ x 1)))`

  Arithmetic: `(+ 1 2)` `(- 1 2)` `(* 1 2)` `(/ 1 2)`
  Comparison: `(eq 1 2)` `(neq 1 2)` `(gt 1 2)` `(gte 1 2)` `(lt 1 2)` `(lte 1 2)`
  Arrays: `(def x [1 2 3])` `(get x 0)` `(set x 0 4)` `(len x)` `(push x 4)` `(pop x)`
*/

#[derive(Clone, Debug, PartialEq)]
enum Token<'a> {
  Nil,
  Bool(bool),
  Num(f64),
  Str(&'a str),
  Symbol(&'a str),
  LBracket,
  RBracket,
  LParen,
  RParen,
}

impl<'a> fmt::Display for Token<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Token::Nil => write!(f, "nil"),
      Token::Bool(x) => write!(f, "{}", x),
      Token::Num(n) => write!(f, "{}", n),
      Token::Str(s) => write!(f, "{}", s),
      Token::Symbol(s) => write!(f, "{}", s),
      Token::LBracket => write!(f, "["),
      Token::RBracket => write!(f, "]"),
      Token::LParen => write!(f, "("),
      Token::RParen => write!(f, ")"),
    }
  }
}

pub type Spanned<T> = (T, SimpleSpan);

#[derive(Clone, Debug, PartialEq)]
enum Expr<'a> {
  Nil,
  Bool(bool),
  Num(f64),
  Str(&'a str),
  Symbol(&'a str),
  List(Vec<Spanned<Self>>),
  Array(Vec<Spanned<Self>>),
  Error,
}

impl<'a> fmt::Display for Expr<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Expr::Nil => write!(f, "nil"),
      Expr::Bool(x) => write!(f, "{}", x),
      Expr::Num(n) => write!(f, "{}", n),
      Expr::Str(s) => write!(f, "{}", s),
      Expr::Symbol(s) => write!(f, "{}", s),
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
      Expr::Error => write!(f, "error"),
    }
  }
}

/// Performs lexical analysis on the source code and returns a list of tokens.
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
      ch.is_alphabetic() || ch.is_ascii_graphic() || ch.is_ascii_punctuation()
    })
    .repeated()
    .at_least(1)
    .slice()
    .map(Token::Symbol);

  // A parser for control characters
  let ctrl = choice((
    just('(').to(Token::LParen),
    just(')').to(Token::RParen),
    just('[').to(Token::LBracket),
    just(']').to(Token::RBracket),
  ));

  let token = num.or(string).or(ctrl).or(boolean).or(nil).or(symbol);

  token
    .map_with_span(|tok, span| (tok, span))
    .padded()
    .recover_with(skip_then_retry_until(any().ignored(), end()))
    .repeated()
    .collect()
}

/// Convenience type for a <code>[SpannedInput]\<[Token]\></code>.
type ParserInput<'source, 'tokens> =
  SpannedInput<Token<'source>, SimpleSpan, &'tokens [Spanned<Token<'source>>]>;

/// Creates a parser which transforms [`Token`]s into [`Expr`]s.
fn parser<'source, 'tokens, O, E>(
) -> impl Parser<'tokens, ParserInput<'source, 'tokens>, O, extra::Err<E>> + Clone
where
  'source: 'tokens,
  O: Container<Spanned<Expr<'source>>>,
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
      .map(Expr::List);

    let array = expr
      .repeated()
      .collect()
      .delimited_by(just(Token::LBracket), just(Token::RBracket))
      .map(Expr::Array);

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

#[derive(Debug, Clone, PartialEq, Default)]
struct Function<'a> {
  expr: Vec<Token<'a>>,
  args: HashSet<String>,
}

#[derive(Clone)]
struct BuiltinFunction<'a> {
  r#fn: fn(&mut Program<'a>, Vec<Expr<'a>>) -> Expr<'a>,
  args: HashSet<String>,
}

#[derive(Default)]
struct Program<'a> {
  vars: HashMap<String, Expr<'a>>,
  fns: HashMap<String, Function<'a>>,
  built_ins: HashMap<String, BuiltinFunction<'a>>,
}

impl fmt::Debug for Program<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "Program {{ vars: {}, fns: {} }}",
      self
        .vars
        .clone()
        .into_iter()
        .map(|(k, v)| format!("{}: {:?}", k, v))
        .collect::<Vec<String>>()
        .join(", "),
      self
        .fns
        .clone()
        .into_iter()
        .map(|(k, v)| format!("{}: {:?}", k, v))
        .collect::<Vec<String>>()
        .join(", "),
    )
  }
}

impl<'a> Program<'a> {
  fn new() -> Self {
    Self {
      vars: HashMap::new(),
      fns: HashMap::new(),
      built_ins: HashMap::from_iter([(
        "def".to_string(),
        BuiltinFunction {
          args: HashSet::from_iter(["name".to_string(), "val".to_string()]),
          r#fn: |prog, args| {
            if let Expr::Symbol(name) = &args[0] {
              if let Some(val) = args.get(1) {
                prog.set_var(name.to_string(), val.clone());
              }
            }
            Expr::Nil
          },
        },
      )]),
    }
  }

  fn set_var(&mut self, name: String, val: Expr<'a>) {
    self.vars.insert(name, val);
  }

  fn get_var(&self, name: &str) -> Option<&Expr<'a>> {
    self.vars.get(name)
  }

  fn set_fn(
    &mut self,
    name: String,
    expr: Vec<Token<'a>>,
    args: HashSet<String>,
  ) {
    self.fns.insert(name, Function { expr, args });
  }

  fn get_fn(&self, name: &str) -> Option<&Function<'a>> {
    self.fns.get(name)
  }

  fn get_builtin(&self, name: &str) -> Option<BuiltinFunction<'a>> {
    self.built_ins.get(name).cloned()
  }

  fn eval_expr(&mut self, expr: Expr<'a>) -> Option<Expr<'a>> {
    match expr {
      Expr::List(exprs) => {
        let mut iter = exprs.iter().map(|(expr, _)| expr);
        let first = iter.next();

        match first {
          Some(Expr::Symbol(name)) => {
            if let Some(builtin) = self.get_builtin(name) {
              let args = iter
                .take(builtin.args.len())
                .map(|arg| self.eval_expr(arg.clone()))
                .collect::<Vec<_>>();

              println!("Calling {:?} with {:?}", name, args);

              Some((builtin.r#fn)(
                self,
                args.into_iter().map(|arg| arg.unwrap()).collect(),
              ))
            } else {
              panic!("Unknown symbol: {}", name);
            }
          }
          first => first.cloned(),
        }
      }
      expr => Some(expr),
    }
  }

  fn eval(&mut self, exprs: Vec<Expr<'a>>) -> Option<Expr<'a>> {
    exprs
      .into_iter()
      .map(|expr| self.eval_expr(expr))
      .last()
      .unwrap()
  }
}

fn main() {
  const CODE: &str = "(def x 2)";
  let mut program = Program::new();

  let (tokens, errs) =
    lexer::<Vec<_>, Rich<_>>().parse(CODE).into_output_errors();

  errs.into_iter().for_each(|err| {
    eprintln!("{}", err);
  });

  let tokens = tokens.unwrap();

  let (exprs, errs) = parser::<Vec<_>, Rich<_>>()
    .parse(tokens.as_slice().spanned((CODE.len()..CODE.len()).into()))
    .into_output_errors();

  errs.into_iter().for_each(|err| {
    eprintln!("{}", err);
  });

  let exprs = exprs.unwrap();

  println!("Exprs: {:?}", exprs);

  program.eval(exprs.into_iter().map(|(tok, _)| tok).collect());

  println!("Program: {:?}", program);
}
