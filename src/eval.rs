use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use core::fmt;
use std::collections::{HashMap, HashSet};

use crate::{
  lex::lexer,
  parse::{parser, Expr},
  Spanned,
};

#[derive(Debug, Clone, PartialEq)]
pub struct Function<'a> {
  expr: Expr<'a>,
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

  fn var(&self, name: &str) -> Option<&Expr<'a>> {
    self.vars.get(name)
  }

  fn set_fn(&mut self, name: String, expr: Expr<'a>, args: HashSet<String>) {
    self.fns.insert(name, Function { expr, args });
  }

  fn r#fn(&self, name: &str) -> Option<&Function<'a>> {
    self.fns.get(name)
  }

  pub fn eval_expr(&mut self, expr: Expr<'a>) -> Expr<'a> {
    match expr {
      Expr::List(exprs) => {
        let mut iter = exprs.iter();
        let (fn_name, span) = iter.next().unwrap();

        let mut eval_next = || self.eval_expr(iter.next().unwrap().0.clone());

        match fn_name {
          Expr::Symbol(name) => match *name {
            // Variables and Functions
            "def" => {
              let name = iter.next().unwrap().0.clone();
              let val = self.eval_expr(iter.next().unwrap().0.clone());

              if let Expr::Symbol(name) = name {
                self.set_var(name.to_string(), val.clone());

                val
              } else {
                panic!("Expected symbol for name {}", span);
              }
            }
            "defn" => {
              let name = iter.next().unwrap().0.clone();
              let args = iter.next().unwrap().0.clone();
              let expr = iter.next().unwrap().0.clone();

              if let Expr::Symbol(name) = name {
                if let Expr::Array(args) = args {
                  let args = args
                    .into_iter()
                    .map(|(arg, _)| {
                      if let Expr::Symbol(arg) = arg {
                        arg.to_string()
                      } else {
                        panic!("Expected symbol for arg {}", span);
                      }
                    })
                    .collect();

                  self.set_fn(name.to_string(), expr, args);

                  Expr::Nil
                } else {
                  panic!("Expected array for args {}", span);
                }
              } else {
                panic!("Expected symbol for name {}", span);
              }
            }

            // Conditionals
            "if" => match eval_next() {
              Expr::Bool(true) => eval_next(),
              Expr::Bool(false) => match iter.nth(1) {
                Some(expr) => self.eval_expr(expr.0.clone()),
                None => Expr::Nil,
              },
              _ => panic!("Expected bool for if condition {}", span),
            },

            // Loops
            "while" => {
              let lhs = iter.next().unwrap().0.clone();
              let initial_bool = match self.eval_expr(lhs.clone()) {
                Expr::Bool(b) => b,
                _ => panic!("Expected bool for while condition {}", span),
              };

              if !initial_bool {
                return Expr::Nil;
              }

              let while_body =
                iter.map(|expr| expr.0.clone()).collect::<Vec<Expr>>();

              while let Expr::Bool(true) = self.eval_expr(lhs.clone()) {
                let mut has_broken = false;

                while_body.iter().for_each(|expr| {
                  if !has_broken {
                    let result = self.eval_expr(expr.clone());

                    if let Expr::Break = result {
                      has_broken = true;
                    }
                  };
                });

                if has_broken {
                  break;
                }
              }

              Expr::Nil
            }
            "break" => match iter.next() {
              Some(_) => panic!("break does not take any arguments {}", span),
              None => Expr::Break,
            },

            // Arithmetic
            "+" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs + rhs),
              _ => Expr::Nil,
            },
            "-" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs - rhs),
              _ => Expr::Nil,
            },
            "*" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs * rhs),
              _ => Expr::Nil,
            },
            "/" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs / rhs),
              _ => Expr::Nil,
            },
            "mod" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs % rhs),
              _ => Expr::Nil,
            },

            // Comparison
            "=" => Expr::Bool(eval_next() == eval_next()),
            "!=" => Expr::Bool(eval_next() != eval_next()),
            ">" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs > rhs),
              _ => Expr::Nil,
            },
            ">=" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs >= rhs),
              _ => Expr::Nil,
            },
            "<" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs < rhs),
              _ => Expr::Nil,
            },
            "<=" => match (eval_next(), eval_next()) {
              (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs <= rhs),
              _ => Expr::Nil,
            },

            // Strings
            "str" => {
              let lhs = eval_next();
              let mut lhs = match lhs {
                Expr::Str(lhs) => lhs,
                _ => lhs.to_string(),
              };

              let rhs = iter
                .map(|expr| self.eval_expr(expr.0.clone()))
                .collect::<Vec<Expr>>();

              rhs
                .iter()
                .map(|expr| match expr {
                  Expr::Str(expr) => expr.to_string(),
                  _ => expr.to_string(),
                })
                .for_each(|expr| {
                  lhs.push_str(&expr);
                });

              Expr::Str(lhs)
            }
            "explode" => match eval_next() {
              Expr::Str(lhs) => Expr::Array(
                lhs
                  .chars()
                  .map(|c| (Expr::Str(c.to_string()), SimpleSpan::new(0, 0)))
                  .collect::<Vec<_>>(),
              ),
              _ => Expr::Nil,
            },
            "print" => {
              let val = eval_next();

              println!("{}", val);

              val
            }

            // Runtime Functions
            _ => {
              let r#fn = self.r#fn(name).cloned();

              match r#fn {
                Some(r#fn) => {
                  let args = r#fn
                    .args
                    .clone()
                    .into_iter()
                    .map(|arg| {
                      (arg, self.eval_expr(iter.next().unwrap().0.clone()))
                    })
                    .collect::<Vec<_>>();

                  for (name, val) in args {
                    self.set_var(name, val);
                  }

                  let result = self.eval_expr(r#fn.expr);

                  for arg in r#fn.args {
                    self.vars.remove(&arg);
                  }

                  result
                }
                None => panic!("Unknown function {}", name),
              }
            }
          },
          first => first.clone(),
        }
      }
      Expr::Symbol(name) => match self.var(name).cloned() {
        Some(val) => val,
        None => Expr::Symbol(name),
      },
      expr => expr,
    }
  }

  pub fn eval(&mut self, exprs: Vec<Expr<'a>>) -> Expr<'a> {
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
) -> (Expr<'a>, Vec<Spanned<Expr<'a>>>) {
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
