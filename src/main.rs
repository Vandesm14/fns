use std::{env, fs};

use fns::eval::{eval, Program};

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
  Conditionals: `(if (= x 2)) "x is 2" "x is not 2")` `(if (= x 2) "x is 2")`
  Loops: `(while (lt x 10) (println x) (set x (+ x 1)))`

  Arithmetic: `(+ 1 2)` `(- 1 2)` `(* 1 2)` `(/ 1 2)`
  Comparison: `(= 1 2)` `(!= 1 2)` `(> 1 2)` `(>= 1 2)` `(< 1 2)` `(<= 1 2)`
  Arrays: `(def x [1 2 3])` `(get x 0)` `(set x 0 4)` `(len x)` `(push x 4)` `(pop x)`
  Strings: `(explode "hello")` `(str "hello" "world")`
*/

fn main() {
  let filename = env::args().nth(1).expect("Expected file argument");
  let src = fs::read_to_string(&filename).expect("Failed to read file");

  let mut program = Program::new();

  let (result, exprs) = eval(&src, &mut program, filename);

  println!("Exprs: {:?}", exprs);
  println!("Program: {:?}", program);
  println!("Result: {:?}", result);
}
