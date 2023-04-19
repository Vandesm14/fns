use core::{fmt, hash::Hash, iter, marker::PhantomData};
use std::collections::HashMap;

use lasso::{Interner, Key};
use thiserror::Error;

use crate::parse::Expr;

#[derive(Debug, Clone, Default)]
pub struct Scope<K, I>
where
  K: Key + Hash,
  I: Interner<K>,
{
  pub interner: I,
  pub vars: HashMap<K, Expr<K>>,
  _phantom: PhantomData<K>,
}

impl<K, I> Scope<K, I>
where
  K: Key + Hash,
  I: Interner<K>,
{
  #[inline]
  pub fn var(&self, k: &K) -> &Expr<K> {
    self.vars.get(k).unwrap_or(&Expr::Nil)
  }
}

pub fn eval<K, I>(
  exprs: impl Iterator<Item = Expr<K>>,
  scope: &mut Scope<K, I>,
) -> Result<Expr<K>, Error<K>>
where
  K: Key + Hash,
  I: Interner<K> + Clone,
{
  let mut last: Result<Expr<K>, Error<K>> = Ok(Expr::Nil);
  for expr in exprs {
    // TODO: implement a way to return
    last = eval_expr(expr, scope);
  }
  return last;
}

pub fn eval_expr<K, I>(
  expr: Expr<K>,
  scope: &mut Scope<K, I>,
) -> Result<Expr<K>, Error<K>>
where
  K: Key + Hash,
  I: Interner<K> + Clone,
{
  match expr {
    Expr::Call(callee_exprs) => {
      let mut callee_exprs = callee_exprs.into_iter();

      match callee_exprs.next() {
        Some(fn_expr) => match fn_expr {
          Expr::List(fn_exprs) => {
            eval_call_list(fn_exprs.into_iter(), callee_exprs, scope)
          }
          Expr::Ident(fn_ident) => {
            let fn_ident_str = scope.interner.resolve(&fn_ident);

            match fn_ident_str {
              "print" => {
                callee_exprs
                  .map(|expr| eval_expr(expr, scope))
                  .collect::<Vec<_>>()
                  .into_iter()
                  .try_for_each(|expr| {
                    let expr = expr?;
                    println!(
                      "{}",
                      ExprFormatter {
                        interner: &scope.interner,
                        expr: &expr,
                      }
                    );
                    Ok::<_, Error<_>>(())
                  })?;
                Ok(Expr::Nil)
              }
              "def" => match (callee_exprs.next(), callee_exprs.next()) {
                (Some(Expr::Ident(ident)), Some(expr)) => {
                  let expr = eval_expr(expr, scope)?;
                  scope.vars.insert(ident, expr);
                  Ok(Expr::Nil)
                }
                (Some(expr), _) => {
                  Err(Error::InvalidFunctionArgumentType(expr))
                }
                _ => Err(Error::InvalidFunctionArgumentType(Expr::Nil)),
              },
              // "defn" => match (callee_exprs.next(), callee_exprs.next(), callee_exprs.collect::<Vec<_>>()) {
              //   (Some(Expr::Ident(ident)), Some(Expr::Array(args)), body) => {
              //     scope.vars.insert(ident, Expr::List(vec![Expr::Array(args), Expr::List(body)]));
              //     Ok(Expr::Nil)
              //   }
              //   _ => Err(Error::InvalidFunctionLayout),
              // }
              "+" => match (callee_exprs.next(), callee_exprs.next()) {
                (Some(Expr::Int(a)), Some(Expr::Int(b))) => Ok(Expr::Int(a + b)),
                (Some(a), Some(b)) => Err(Error::InvalidFunctionArgumentType(Expr::List(vec![a, b]))),
                _ => Err(Error::InvalidFunctionArgumentType(Expr::Nil)),
              },
              _ => match scope.var(&fn_ident).clone() {
                Expr::List(fn_exprs) => {
                  eval_call_list(fn_exprs.into_iter(), callee_exprs, scope)
                }
                expr => Err(Error::InvalidFunctionArgumentType(expr)),
              },
            }
          }
          _ => Ok(fn_expr),
        },
        None => Ok(Expr::Nil),
      }
    }
    _ => Ok(expr),
  }
}

pub fn eval_call_list<K, I>(
  mut fn_exprs: impl Iterator<Item = Expr<K>>,
  callee_exprs: impl Iterator<Item = Expr<K>>,
  scope: &mut Scope<K, I>,
) -> Result<Expr<K>, Error<K>>
where
  K: Key + Hash,
  I: Interner<K> + Clone,
{
  match fn_exprs.next() {
    Some(Expr::Array(fn_args)) => {
      let fn_args =
        fn_args
          .into_iter()
          .try_fold(vec![], |mut v, expr| match expr {
            Expr::Ident(ident) => {
              v.push(ident);
              Ok(v)
            }
            _ => Err(Error::InvalidFunctionArgumentType(expr)),
          })?;

      // TODO: this is a very temporary function scope
      let mut fn_scope = scope.clone();
      scope.vars.extend(fn_args.into_iter().zip(callee_exprs));

      eval(fn_exprs, &mut fn_scope)
    }
    _ => Err(Error::InvalidFunctionLayout),
  }
}

#[derive(Debug, Clone, PartialEq, Error)]
pub enum Error<K> {
  #[error("unknown variable {0:?}")]
  UnknownVariable(K),
  #[error("invalid function layout, expected '([args] body...)")]
  InvalidFunctionLayout,
  #[error("invalid function argument type {0:?}")]
  InvalidFunctionArgumentType(Expr<K>),
  // #[error("invalid variable identifier {0:?}")]
  // InvalidVariableIdent(Expr<K>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ExprFormatter<'a, K, I>
where
  K: Key,
  I: Interner<K>,
{
  pub interner: &'a I,
  pub expr: &'a Expr<K>,
}

impl<'a, K, I> fmt::Display for ExprFormatter<'a, K, I>
where
  K: Key,
  I: Interner<K>,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.expr {
      Expr::Nil => f.write_str("nil"),
      Expr::Bool(x) => write!(f, "{x}"),
      Expr::Int(x) => write!(f, "{x}"),
      Expr::Float(x) => write!(f, "{x}"),

      Expr::Ident(x) => f.write_str(self.interner.resolve(x)),

      Expr::Array(x) => {
        f.write_str("[")?;
        iter::once("")
          .chain(iter::repeat(" "))
          .zip(x.iter())
          .try_for_each(|(pad, expr)| {
            write!(
              f,
              "{pad}{}",
              Self {
                interner: self.interner,
                expr
              }
            )
          })?;
        f.write_str("]")
      }
      Expr::List(x) => {
        f.write_str("'(")?;
        iter::once("")
          .chain(iter::repeat(" "))
          .zip(x.iter())
          .try_for_each(|(pad, expr)| {
            write!(
              f,
              "{pad}{}",
              Self {
                interner: self.interner,
                expr
              }
            )
          })?;
        f.write_str(")")
      }
      Expr::Call(x) => {
        f.write_str("(")?;
        iter::once("")
          .chain(iter::repeat(" "))
          .zip(x.iter())
          .try_for_each(|(pad, expr)| {
            write!(
              f,
              "{pad}{}",
              Self {
                interner: self.interner,
                expr
              }
            )
          })?;
        f.write_str(")")
      }

      Expr::Error => f.write_str("<error>"),
    }
  }
}

// use ariadne::{sources, Color, Label, Report, ReportKind};
// use chumsky::prelude::*;
// use lasso::{Rodeo, Spur};
// use std::collections::HashMap;

// use crate::{
//   lex::lexer,
//   parse::{parser, Expr},
//   Spanned,
// };

// #[derive(Debug, Clone, PartialEq, Default)]
// pub struct Scope {
//   spurs: Rodeo,
//   defs: HashMap<Spur, Def>,
// }

// // TODO: combine these into a single concept
// #[derive(Debug, Clone, PartialEq)]
// pub enum Def {
//   Var(Expr),
//   Fn { args: Vec<Spur>, body: Expr },
// }

// pub fn eval_expr(expr: Expr, scope: &mut Scope) -> Expr {
//   match expr {
//     Expr::Group(exprs) => {
//       let last = exprs
//         .iter()
//         .map(|expr| eval_expr(expr.clone(), scope))
//         .last();

//       match last {
//         Some(expr) => expr,
//         None => Expr::Nil,
//       }
//     }
//     Expr::List(exprs) => {
//       let mut iter = exprs.iter();
//       let (fn_name, span) = iter.next().unwrap();

//       match fn_name {
//         Expr::Symbol(name) => match scope.spurs.resolve(name) {
//           // Variables and Functions
//           "def" => {
//             let name = iter.next().unwrap().0.clone();
//             let val = eval_expr(iter.next().unwrap().0.clone(), scope);

//             if let Expr::Symbol(name) = name {
//               scope.defs.insert(name, Def::Var(val.clone()));
//               val
//             } else {
//               panic!("Expected symbol for name {}", span);
//             }
//           }
//           "defn" => {
//             let name = iter.next().unwrap().0.clone();
//             let args = iter.next().unwrap().0.clone();
//             let expr = iter.map(|expr| expr.0.clone()).collect::<Vec<Expr>>();

//             if let Expr::Symbol(name) = name {
//               if let Expr::Array(args) = args {
//                 let args = args
//                   .into_iter()
//                   .map(|(arg, _)| {
//                     if let Expr::Symbol(arg) = arg {
//                       arg
//                     } else {
//                       panic!("Expected symbol for arg {}", span);
//                     }
//                   })
//                   .collect();

//                 scope.defs.insert(
//                   name,
//                   Def::Fn {
//                     args,
//                     body: Expr::Group(expr),
//                   },
//                 );

//                 Expr::Nil
//               } else {
//                 panic!("Expected array for args {}", span);
//               }
//             } else {
//               panic!("Expected symbol for name {}", span);
//             }
//           }

//           // Conditionals
//           "if" => match eval_expr(iter.next().unwrap().0.clone(), scope) {
//             Expr::Bool(true) => {
//               eval_expr(iter.next().unwrap().0.clone(), scope)
//             }
//             Expr::Bool(false) => match iter.nth(1) {
//               Some(expr) => eval_expr(expr.0.clone(), scope),
//               None => Expr::Nil,
//             },
//             _ => panic!("Expected bool for if condition {}", span),
//           },

//           // Loops
//           "while" => {
//             let lhs = iter.next().unwrap().0.clone();
//             let initial_bool = match eval_expr(lhs.clone(), scope) {
//               Expr::Bool(b) => b,
//               _ => panic!("Expected bool for while condition {}", span),
//             };

//             if !initial_bool {
//               return Expr::Nil;
//             }

//             let while_body =
//               iter.map(|expr| expr.0.clone()).collect::<Vec<Expr>>();

//             while let Expr::Bool(true) = eval_expr(lhs.clone(), scope) {
//               let mut has_broken = false;

//               while_body.iter().for_each(|expr| {
//                 if !has_broken {
//                   let result = eval_expr(expr.clone(), scope);

//                   if let Expr::Break = result {
//                     has_broken = true;
//                   }
//                 };
//               });

//               if has_broken {
//                 break;
//               }
//             }

//             Expr::Nil
//           }
//           "break" => match iter.next() {
//             Some(_) => panic!("break does not take any arguments {}", span),
//             None => Expr::Break,
//           },

//           // Arithmetic
//           "+" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs + rhs),
//             _ => Expr::Nil,
//           },
//           "-" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs - rhs),
//             _ => Expr::Nil,
//           },
//           "*" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs * rhs),
//             _ => Expr::Nil,
//           },
//           "/" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs / rhs),
//             _ => Expr::Nil,
//           },
//           "mod" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Num(lhs % rhs),
//             _ => Expr::Nil,
//           },

//           // Comparison
//           "=" => Expr::Bool(
//             eval_expr(iter.next().unwrap().0.clone(), scope)
//               == eval_expr(iter.next().unwrap().0.clone(), scope),
//           ),
//           "!=" => Expr::Bool(
//             eval_expr(iter.next().unwrap().0.clone(), scope)
//               != eval_expr(iter.next().unwrap().0.clone(), scope),
//           ),
//           ">" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs > rhs),
//             _ => Expr::Nil,
//           },
//           ">=" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs >= rhs),
//             _ => Expr::Nil,
//           },
//           "<" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs < rhs),
//             _ => Expr::Nil,
//           },
//           "<=" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Num(lhs), Expr::Num(rhs)) => Expr::Bool(lhs <= rhs),
//             _ => Expr::Nil,
//           },

//           // Arrays
//           "get" => match (
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//             eval_expr(iter.next().unwrap().0.clone(), scope),
//           ) {
//             (Expr::Array(lhs), Expr::Num(rhs)) => lhs[rhs as usize].0.clone(),
//             _ => Expr::Nil,
//           },
//           "set" => {
//             let symbol = iter.next().unwrap().0.clone();
//             let index = eval_expr(iter.next().unwrap().0.clone(), scope);
//             let val = eval_expr(iter.next().unwrap().0.clone(), scope);

//             let symbol = match symbol {
//               Expr::Symbol(symbol) => symbol,
//               _ => panic!("Expected symbol for set {}", span),
//             };
//             let array = match scope.defs.get_mut(&symbol) {
//               Some(Def::Var(Expr::Array(lhs))) => lhs,
//               _ => panic!("Expected array for set {}", span),
//             };
//             let index = match index {
//               Expr::Num(index) => index,
//               _ => panic!("Expected number for set {}", span),
//             };

//             array[index as usize].0 = val.clone();

//             val
//           }
//           "len" => {
//             let array = match eval_expr(iter.next().unwrap().0.clone(), scope) {
//               Expr::Array(lhs) => lhs,
//               _ => panic!("Expected array for len {}", span),
//             };

//             Expr::Num(array.len() as f64)
//           }
//           "push" => {
//             let symbol = iter.next().unwrap().0.clone();
//             let val = eval_expr(iter.next().unwrap().0.clone(), scope);

//             let symbol = match symbol {
//               Expr::Symbol(symbol) => symbol,
//               _ => panic!("Expected symbol for push {}", span),
//             };
//             let array = match scope.defs.get_mut(&symbol) {
//               Some(Def::Var(Expr::Array(lhs))) => lhs,
//               _ => panic!("Expected array for push {}", span),
//             };
//             array.push((val.clone(), SimpleSpan::new(0, 0)));

//             val
//           }
//           "pop" => {
//             let symbol = iter.next().unwrap().0.clone();

//             let symbol = match symbol {
//               Expr::Symbol(symbol) => symbol,
//               _ => panic!("Expected symbol for pop {}", span),
//             };
//             let array = match scope.defs.get_mut(&symbol) {
//               Some(Def::Var(Expr::Array(lhs))) => lhs,
//               _ => panic!("Expected array for pop {}", span),
//             };

//             match array.pop() {
//               Some((val, _)) => val,
//               None => Expr::Nil,
//             }
//           }

//           // Strings
//           "str" => {
//             let lhs = eval_expr(iter.next().unwrap().0.clone(), scope);
//             let mut lhs = match lhs {
//               Expr::Str(lhs) => scope.spurs.resolve(&lhs).to_string(),
//               _ => lhs.to_string(),
//             };

//             let rhs = iter
//               .map(|expr| eval_expr(expr.0.clone(), scope))
//               .collect::<Vec<Expr>>();

//             rhs
//               .iter()
//               .map(|expr| match expr {
//                 Expr::Str(expr) => scope.spurs.resolve(&expr).to_string(),
//                 _ => expr.to_string(),
//               })
//               .for_each(|expr| {
//                 lhs.push_str(&expr);
//               });

//             Expr::Str(scope.spurs.get_or_intern(lhs))
//           }
//           "explode" => match eval_expr(iter.next().unwrap().0.clone(), scope) {
//             Expr::Str(lhs) => Expr::Array(
//               scope
//                 .spurs
//                 .resolve(&lhs)
//                 .to_string()
//                 .chars()
//                 .map(|c| {
//                   (
//                     Expr::Str(scope.spurs.get_or_intern(&c.to_string())),
//                     SimpleSpan::new(0, 0),
//                   )
//                 })
//                 .collect::<Vec<_>>(),
//             ),
//             _ => Expr::Nil,
//           },
//           "print" => {
//             let val = eval_expr(iter.next().unwrap().0.clone(), scope);

//             match val {
//               Expr::Str(val) => println!("{}", scope.spurs.resolve(&val)),
//               _ => println!("{}", val),
//             }

//             val
//           }

//           // Eval and IO (import/export groundwork)
//           "read-file" => {
//             let path = match eval_expr(iter.next().unwrap().0.clone(), scope) {
//               Expr::Str(path) => path,
//               _ => panic!("Expected string for read-file {}", span),
//             };

//             let path = scope.spurs.resolve(&path);

//             let contents = std::fs::read_to_string(path).unwrap();

//             Expr::Str(scope.spurs.get_or_intern(contents))
//           }
//           "eval" => {
//             let expr = match eval_expr(iter.next().unwrap().0.clone(), scope) {
//               Expr::Str(expr) => expr,
//               _ => panic!("Expected string for eval {}", span),
//             };

//             let expr = scope.spurs.resolve(&expr).to_string();

//             eval(&expr, scope, "eval".to_string()).0
//           }

//           // Runtime Functions
//           _ => {
//             let r#fn = scope.defs.get(name).cloned();

//             match r#fn {
//               Some(Def::Fn { args, body }) => {
//                 let args = args
//                   .clone()
//                   .into_iter()
//                   .map(|arg| {
//                     (arg, eval_expr(iter.next().unwrap().0.clone(), scope))
//                   })
//                   .collect::<Vec<_>>();

//                 for (name, val) in args.clone() {
//                   scope.defs.insert(name, Def::Var(val));
//                 }

//                 let result = eval_expr(body, scope);

//                 for arg in args {
//                   scope.defs.remove(&arg.0);
//                 }

//                 result
//               }
//               Some(Def::Var(_)) => todo!(),
//               None => panic!("Unknown function {:?}", name),
//             }
//           }
//         },
//         first => first.clone(),
//       }
//     }
//     Expr::Symbol(name) => match scope.defs.get(&name).cloned() {
//       Some(Def::Var(val)) => val,
//       Some(Def::Fn { .. }) => todo!(),
//       None => Expr::Symbol(name),
//     },
//     expr => expr,
//   }
// }

// pub fn eval_exprs(exprs: Vec<Expr>, scope: &mut Scope) -> Expr {
//   exprs
//     .into_iter()
//     .map(|expr| eval_expr(expr, scope))
//     .last()
//     .unwrap()
// }

// pub fn eval(
//   source: &str,
//   scope: &mut Scope,
//   filename: String,
// ) -> (Expr, Vec<Spanned<Expr>>) {
//   let (tokens, errs) = lexer::<Vec<_>, Rich<_>>()
//     .parse_with_state(source, &mut scope.spurs)
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

//   let result = eval_exprs(
//     exprs.clone().into_iter().map(|(tok, _)| tok).collect(),
//     scope,
//   );

//   (result, exprs)
// }
