use std::{env, fs};

use fns::eval::{eval, Program};

fn main() {
  let filename = env::args().nth(1).expect("Expected file argument");
  let src = fs::read_to_string(&filename).expect("Failed to read file");

  let mut program = Program::new();

  let (result, exprs) = eval(&src, &mut program, filename);

  // println!("Exprs: {:?}", exprs);
  println!("Program: {:?}", program);
  println!("Result: {:?}", result);
}
