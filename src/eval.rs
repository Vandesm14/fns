use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use core::fmt;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

use crate::{
  lex::lexer,
  parse::{parser, Expr},
  Spanned,
};

#[derive(Debug, Clone, PartialEq)]
pub struct Function<'a> {
  args: HashSet<String>,
  body: Expr<'a>,
}

#[derive(Debug, Clone, PartialEq)]
enum ScopeItem<'a> {
  Var(Expr<'a>),
  Fn(Function<'a>),
}

type Scope<'a> = HashMap<String, ScopeItem<'a>>;

#[derive(Debug, Clone, PartialEq, Default)]
struct Scopes<'a> {
  scopes: Vec<Scope<'a>>,
}

impl<'a> Scopes<'a> {
  fn new() -> Self {
    Self {
      scopes: vec![Scope::new()],
    }
  }

  fn get(&self, key: &str) -> Option<&ScopeItem<'a>> {
    self.scopes.iter().rev().find_map(|scope| scope.get(key))
  }

  fn get_mut(&mut self, key: &str) -> Option<&mut ScopeItem<'a>> {
    self
      .scopes
      .iter_mut()
      .rev()
      .find_map(|scope| scope.get_mut(key))
  }

  fn insert(
    &mut self,
    key: String,
    item: ScopeItem<'a>,
  ) -> Option<ScopeItem<'a>> {
    self
      .scopes
      .last_mut()
      .and_then(|scope| scope.insert(key, item))
  }

  fn remove(&mut self, key: &str) -> Option<ScopeItem<'a>> {
    self.scopes.last_mut().and_then(|scope| scope.remove(key))
  }

  fn var(&self, key: &str) -> Option<&Expr<'a>> {
    self.get(key).and_then(|item| match item {
      ScopeItem::Var(var) => Some(var),
      _ => None,
    })
  }

  fn set_var(&mut self, key: String, var: Expr<'a>) -> Option<ScopeItem<'a>> {
    self.insert(key, ScopeItem::Var(var))
  }

  fn r#fn(&self, key: &str) -> Option<&Function<'a>> {
    self.get(key).and_then(|item| match item {
      ScopeItem::Fn(r#fn) => Some(r#fn),
      _ => None,
    })
  }

  fn set_fn(
    &mut self,
    key: String,
    r#fn: Function<'a>,
  ) -> Option<ScopeItem<'a>> {
    self.insert(key, ScopeItem::Fn(r#fn))
  }
}

type BuiltinFn<'a> = fn(
  scopes: &'a mut Scopes<'a>,
  args: Vec<Expr<'a>>,
) -> Result<Expr<'a>, Error<'a>>;

macro_rules! builtin_two {
  (($lhs:pat, $rhs:pat) => $expr:expr) => {
    |scope, exprs| {
      let mut exprs = exprs.into_iter();
      let mut next_expr = || exprs.next().ok_or(Error::ExpectedAny);

      let lhs = next_expr()?;
      let rhs = next_expr()?;

      match (lhs, rhs) {
        ($lhs, $rhs) => Ok($expr),
        (lhs, _) => Err(Error::Unexpected(lhs)),
      }
    }
  };
}

fn create_builtins<'a>() -> HashMap<&'a str, BuiltinFn<'a>> {
  let mut builtins: HashMap<&str, BuiltinFn<'a>> = HashMap::new();

  builtins.insert("def", |scopes, exprs| {
    let mut exprs = exprs.into_iter();
    let mut next_expr = || exprs.next().ok_or(Error::ExpectedAny);

    let lhs = next_expr()?;
    let rhs = next_expr()?;

    match (lhs, rhs) {
      (Expr::Symbol(symbol), rhs) => {
        scopes.set_var(symbol.to_string(), rhs);
        Ok(Expr::Nil)
      }
      (lhs, _) => Err(Error::Unexpected(lhs)),
    }
  });

  builtins.insert("defn", |scopes, exprs| {
    let mut exprs = exprs.into_iter();
    let mut next_expr = || exprs.next().ok_or(Error::ExpectedAny);

    let name = next_expr()?;
    let fn_args = next_expr()?;
    let body = next_expr()?;

    match (name, fn_args, body) {
      (Expr::Symbol(symbol), Expr::Array(fn_args), body) => {
        let fn_args = fn_args
          .into_iter()
          .map(|(arg, _)| {
            if let Expr::Symbol(arg) = arg {
              Ok(arg.to_string())
            } else {
              Err(Error::Unexpected(arg))
            }
          })
          .try_fold(HashSet::new(), |mut vec, arg| {
            vec.insert(arg?);
            Ok(vec)
          })?;

        scopes.set_fn(
          name.to_string(),
          Function {
            body,
            args: fn_args,
          },
        );
        Ok(Expr::Nil)
      }
      (lhs, _, _) => Err(Error::Unexpected(lhs)),
    }
  });

  builtins.insert(
    "+",
    builtin_two!((Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs + rhs)),
  );
  builtins.insert(
    "-",
    builtin_two!((Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs - rhs)),
  );
  builtins.insert(
    "*",
    builtin_two!((Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs * rhs)),
  );
  builtins.insert(
    "/",
    builtin_two!((Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs / rhs)),
  );
  builtins.insert(
    "mod",
    builtin_two!((Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs % rhs)),
  );

  builtins
}

fn default_arithmetic_fns() {}
fn default_compat_fns() {}

fn eval<'a>(
  builtins: &'a mut HashMap<&'a str, BuiltinFn<'a>>,
  scopes: &'a mut Scopes<'a>,
  expr: Expr<'a>,
) -> Result<Expr<'a>, Error<'a>> {
  match expr {
    Expr::Nil
    | Expr::Bool(_)
    | Expr::Num(_)
    | Expr::Str(_)
    | Expr::Array(_)
    | Expr::Symbol(_) => Ok(expr),
    Expr::List(exprs) => {
      let mut exprs = exprs.into_iter().map(|(expr, _)| expr);

      let r#fn = match exprs.next() {
        Some(Expr::Symbol(symbol)) => symbol,
        Some(expr) => Err(Error::Unexpected(expr))?,
        None => Err(Error::Expected(vec![Expr::Symbol("symbol")]))?,
      };

      let exprs: Vec<_> = exprs.collect();

      if let Some(r#fn) = builtins.get(r#fn).copied() {
        // let exprs = exprs.map(|expr| ).collect();
        let mut args = vec![];
        for expr in exprs {
          args.push(eval(builtins, scopes, expr)?);
        }
        r#fn(scopes, args)
      } else {
        // let mut exprs = exprs.into_iter();
        // let mut next_expr = || exprs.next().ok_or(Error::ExpectedAny);

        // let lhs = next_expr()??;
        // let rhs = next_expr()??;

        todo!()
      }
    }
    Expr::Error => todo!(),
  }
}

#[derive(Debug, Clone, PartialEq, Error)]
pub enum Error<'a> {
  /// Unexprected [`Expr`].
  #[error("unexpected expression {0:?}")]
  Unexpected(Expr<'a>),
  /// Expected an specific [`Expr`].
  #[error("expected expression {0:?}")]
  Expected(Vec<Expr<'a>>),
  /// Expected any [`Expr`].
  #[error("expected primitive expression")]
  ExpectedAny,
}

////////////////////////////////////////////////////////////////////////////////

// pub struct Program<'a> {
//   scopes: Scopes<'a>,
// }

// impl fmt::Debug for Program<'_> {
//   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//     f.debug_struct("Program")
//       .field("scopes", &self.scopes)
//       .finish()
//   }
// }

// impl<'a> Program<'a> {
//   pub fn new() -> Self {
//     Self {
//       scopes: Scopes::new(),
//     }
//   }

// pub fn eval_expr(&'a mut self, expr: Expr<'a>) -> Expr<'a> {
//   match expr {
//     Expr::List(exprs) => {
//       let mut iter = exprs.iter();
//       let (fn_name, span) = iter.next().unwrap();

//       let mut eval_next = || self.eval_expr(iter.next().unwrap().0.clone());

//       match fn_name {
//         Expr::Symbol(name) => match *name {
//           // Functions that are built into the language (starts with fns with weird args)
//           "def" => {
//             let name = iter.next().unwrap().0.clone();
//             let val = self.eval_expr(iter.next().unwrap().0.clone());

//             if let Expr::Symbol(name) = name {
//               self.scopes.set_var(name.to_string(), val.clone());

//               val
//             } else {
//               panic!("Expected symbol for name {}", span);
//             }
//           }
//           "defn" => {
//             let name = iter.next().unwrap().0.clone();
//             let args = iter.next().unwrap().0.clone();
//             let expr = iter.next().unwrap().0.clone();

//             if let Expr::Symbol(name) = name {
//               if let Expr::Array(args) = args {
//                 let args = args
//                   .into_iter()
//                   .map(|(arg, _)| {
//                     if let Expr::Symbol(arg) = arg {
//                       arg.to_string()
//                     } else {
//                       panic!("Expected symbol for arg {}", span);
//                     }
//                   })
//                   .collect();

//                 self.scopes.set_fn(name.to_string(), expr, args);

//                 Expr::Nil
//               } else {
//                 panic!("Expected array for args {}", span);
//               }
//             } else {
//               panic!("Expected symbol for name {}", span);
//             }
//           }

//           "+" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs + rhs),
//             _ => Expr::Nil,
//           },
//           "-" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs - rhs),
//             _ => Expr::Nil,
//           },
//           "*" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs * rhs),
//             _ => Expr::Nil,
//           },
//           "/" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs / rhs),
//             _ => Expr::Nil,
//           },

//           "=" => Expr::Bool(eval_next() == eval_next()),
//           "!=" => Expr::Bool(eval_next() != eval_next()),
//           ">" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs > rhs),
//             _ => Expr::Nil,
//           },
//           ">=" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs >= rhs),
//             _ => Expr::Nil,
//           },
//           "<" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs < rhs),
//             _ => Expr::Nil,
//           },
//           "<=" => match (eval_next(), eval_next()) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs <= rhs),
//             _ => Expr::Nil,
//           },

//           "str" => match (eval_next(), eval_next()) {
//             (Expr::Str(lhs), Expr::Str(rhs)) => Expr::Str(lhs + &rhs),
//             _ => Expr::Nil,
//           },
//           _ => {
//             let r#fn = self.scopes.r#fn(name).cloned();

//             match r#fn {
//               Some(r#fn) => {
//                 let args = r#fn
//                   .args
//                   .clone()
//                   .into_iter()
//                   .map(|arg| {
//                     (arg, self.eval_expr(iter.next().unwrap().0.clone()))
//                   })
//                   .collect::<Vec<_>>();

//                 for (name, val) in args {
//                   self.scopes.set_var(name, val);
//                 }

//                 let result = self.eval_expr(r#fn.expr);

//                 for arg in r#fn.args {
//                   self.scopes.remove(&arg);
//                 }

//                 result
//               }
//               None => panic!("Unknown function {}", name),
//             }
//           }
//         },
//         first => first.clone(),
//       }
//     }
//     Expr::Symbol(name) => match self.scopes.var(name).cloned() {
//       Some(val) => val,
//       None => Expr::Symbol(name),
//     },
//     expr => expr,
//   }
// }

//   pub fn eval(&mut self, exprs: Vec<Expr<'a>>) -> Expr<'a> {
//     exprs
//       .into_iter()
//       .map(|expr| self.eval_expr(expr))
//       .last()
//       .unwrap()
//   }
// }

// pub fn eval<'a>(
//   source: &'a str,
//   program: &mut Program<'a>,
//   filename: String,
// ) -> (Expr<'a>, Vec<Spanned<Expr<'a>>>) {
//   let (tokens, errs) = lexer::<Vec<_>, Rich<_>>()
//     .parse(source)
//     .into_output_errors();

//   let tokens = tokens.unwrap();

//   let (exprs, parse_errs) = parser::<Vec<_>, Rich<_>>()
//     .parse(
//       tokens
//         .as_slice()
//         .spanned((source.len()..source.len()).into()),
//     )
//     .into_output_errors();

//   errs
//     .into_iter()
//     .map(|e| e.map_token(|c| c.to_string()))
//     .chain(
//       parse_errs
//         .into_iter()
//         .map(|e| e.map_token(|tok| tok.to_string())),
//     )
//     .for_each(|e| {
//       Report::build(ReportKind::Error, filename.clone(), e.span().start)
//         .with_message(e.to_string())
//         .with_label(
//           Label::new((filename.clone(), e.span().into_range()))
//             .with_message(e.reason().to_string())
//             .with_color(Color::Red),
//         )
//         .finish()
//         .eprint(sources([(filename.to_owned(), source.to_owned())]))
//         .unwrap()
//     });

//   let exprs = exprs.unwrap();

//   let result =
//     program.eval(exprs.clone().into_iter().map(|(tok, _)| tok).collect());

//   (result, exprs)
// }

// #[cfg(test)]
// mod test {
//   use super::*;

//   fn eval_in_mem<'a>(source: &'a str, program: &mut Program<'a>) -> Expr<'a> {
//     let (result, _) = eval(source, program, file!().to_string());

//     result
//   }

//   // TODO: Add integration tests
//   // We don't need the bloat of a full unit test suite
// }
