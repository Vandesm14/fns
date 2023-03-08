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

fn main() {
  println!("Hello, world!");
}
