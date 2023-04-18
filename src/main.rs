use std::{env, fs};

use fns::eval::{eval, Scope};

fn main() {
  let filename = env::args().nth(1).expect("Expected file argument");
  let src = fs::read_to_string(&filename).expect("Failed to read file");

  let mut scope = Scope::default();

  let (result, _exprs) = eval(&src, &mut scope, filename);

  // println!("Exprs: {:?}", exprs);
  // println!("Program: {:?}", program);
  println!("Result: {:?}", result);
}
