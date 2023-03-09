use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use core::fmt;
use std::collections::{HashMap, HashSet};

use crate::{
  lex::{lexer, Token},
  parse::{parser, Expr},
  Spanned,
};

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Function<'a> {
  expr: Vec<Token<'a>>,
  args: HashSet<String>,
}

#[derive(Default)]
pub struct Program<'a> {
  vars: HashMap<String, Expr<'a>>,
  fns: HashMap<String, Function<'a>>,
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
  pub fn new() -> Self {
    Self {
      vars: HashMap::new(),
      fns: HashMap::new(),
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

  pub fn eval_expr(&mut self, expr: Expr<'a>) -> Option<Expr<'a>> {
    match expr {
      Expr::List(exprs) => {
        let mut iter = exprs.iter();
        let (fn_name, span) = iter.next().unwrap();

        match fn_name {
          Expr::Symbol(name) => match *name {
            // Functions that are built into the language (starts with fns with weird args)
            "def" => {
              let name = iter.next().unwrap().0.clone();
              let val = self.eval_expr(iter.next().unwrap().0.clone()).unwrap();

              if let Expr::Symbol(name) = name {
                self.set_var(name.to_string(), val.clone());

                Some(val)
              } else {
                panic!("Expected symbol for name {}", span);
              }
            }

            // Functions that are built into the language (fns with two args)
            _ => {
              let lhs = self.eval_expr(iter.next().unwrap().0.clone()).unwrap();
              let rhs = self.eval_expr(iter.next().unwrap().0.clone()).unwrap();

              match *name {
                "+" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Num(lhs + rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                "-" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Num(lhs - rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                "*" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Num(lhs * rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                "/" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Num(lhs / rhs))
                  }
                  _ => Some(Expr::Nil),
                },

                "=" => Some(Expr::Bool(lhs == rhs)),
                "!=" => Some(Expr::Bool(lhs != rhs)),
                ">" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Bool(lhs > rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                ">=" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Bool(lhs >= rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                "<" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Bool(lhs < rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                "<=" => match (lhs, rhs) {
                  (Expr::Num(lhs), Expr::Num(rhs)) => {
                    Some(Expr::Bool(lhs <= rhs))
                  }
                  _ => Some(Expr::Nil),
                },

                "str" => match (lhs, rhs) {
                  (Expr::Str(lhs), Expr::Str(rhs)) => {
                    Some(Expr::Str(lhs + &rhs))
                  }
                  _ => Some(Expr::Nil),
                },
                _ => todo!("Runtime functions not yet implemented {}", span),
              }
            }
          },
          first => Some(first.clone()),
        }
      }
      Expr::Symbol(name) => self.get_var(name).cloned(),
      expr => Some(expr),
    }
  }

  pub fn eval(&mut self, exprs: Vec<Expr<'a>>) -> Option<Expr<'a>> {
    exprs
      .into_iter()
      .map(|expr| self.eval_expr(expr))
      .last()
      .unwrap()
  }
}

pub fn eval<'a>(
  source: &'a str,
  program: &mut Program<'a>,
  filename: String,
) -> (Option<Expr<'a>>, Vec<Spanned<Expr<'a>>>) {
  let (tokens, errs) = lexer::<Vec<_>, Rich<_>>()
    .parse(source)
    .into_output_errors();

  let tokens = tokens.unwrap();

  let (exprs, parse_errs) = parser::<Vec<_>, Rich<_>>()
    .parse(
      tokens
        .as_slice()
        .spanned((source.len()..source.len()).into()),
    )
    .into_output_errors();

  errs
    .into_iter()
    .map(|e| e.map_token(|c| c.to_string()))
    .chain(
      parse_errs
        .into_iter()
        .map(|e| e.map_token(|tok| tok.to_string())),
    )
    .for_each(|e| {
      Report::build(ReportKind::Error, filename.clone(), e.span().start)
        .with_message(e.to_string())
        .with_label(
          Label::new((filename.clone(), e.span().into_range()))
            .with_message(e.reason().to_string())
            .with_color(Color::Red),
        )
        .finish()
        .eprint(sources([(filename.to_owned(), source.to_owned())]))
        .unwrap()
    });

  let exprs = exprs.unwrap();

  let result =
    program.eval(exprs.clone().into_iter().map(|(tok, _)| tok).collect());

  (result, exprs)
}

fn eval_in_mem<'a>(
  source: &'a str,
  program: &mut Program<'a>,
) -> (Option<Expr<'a>>, Vec<Spanned<Expr<'a>>>) {
  eval(source, program, file!().to_string())
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_def() {
    let mut program = Program::new();

    let (result, _) =
      eval_in_mem("(def a 1)\n(def b 2)\n(def c (* 2 (+ a b)))", &mut program);

    assert_eq!(result, Some(Expr::Num(6.0)));
    assert_eq!(program.vars.len(), 3);
    assert_eq!(program.vars.get("a"), Some(&Expr::Num(1.0)));
    assert_eq!(program.vars.get("b"), Some(&Expr::Num(2.0)));
    assert_eq!(program.vars.get("c"), Some(&Expr::Num(6.0)));
  }

  #[test]
  fn test_equality() {
    let mut program = Program::new();

    let (result, _) = eval_in_mem("(= 1 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));

    let (result, _) = eval_in_mem("(= 1 2)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));

    let (result, _) = eval_in_mem("(= true true)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));

    let (result, _) = eval_in_mem("(= true false)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));

    let (result, _) = eval_in_mem("(= \"foo\" \"foo\")", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));
  }

  #[test]
  fn test_inequality() {
    let mut program = Program::new();

    let (result, _) = eval_in_mem("(!= 1 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));
    let (result, _) = eval_in_mem("(!= 1 2)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));

    let (result, _) = eval_in_mem("(> 1 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));
    let (result, _) = eval_in_mem("(> 1 2)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));
    let (result, _) = eval_in_mem("(> 2 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));

    let (result, _) = eval_in_mem("(>= 1 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));
    let (result, _) = eval_in_mem("(>= 1 2)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));
    let (result, _) = eval_in_mem("(>= 2 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));

    let (result, _) = eval_in_mem("(< 1 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));
    let (result, _) = eval_in_mem("(< 1 2)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));
    let (result, _) = eval_in_mem("(< 2 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));

    let (result, _) = eval_in_mem("(<= 1 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));
    let (result, _) = eval_in_mem("(<= 1 2)", &mut program);
    assert_eq!(result, Some(Expr::Bool(true)));
    let (result, _) = eval_in_mem("(<= 2 1)", &mut program);
    assert_eq!(result, Some(Expr::Bool(false)));
  }
}
