# Primitives

## Language

- [x] Expressions: `(...)`
- [x] Lists/Arrays/Sequences: `[...]`
- [x] Strings:
  - [x] `"..."`
  - [x] `"\""`
- [x] Numbers:
  - [x] `1`
  - [x] `1.0`
  - [x] `-1`
  - [x] `-1.0`
- [x] Booleans: `true` `false`
- [x] Nil: `nil`
- [x] Symbols: `/[a-zA-Z_-][a-zA-Z0-9_-]*`

## Builtins

- [x] Variables:
  - [x] `(def x 2)`
  - [x] Use `def` to re-assign a variable
- [x] Functions:
  - [x] `(defn add [x y] (+ x y))`
- [x] Conditionals:
  - [x] `(if (= x 2) "x is 2" "x is not 2")`
  - [x] `(if (= x 2) "x is 2")`
- [x] Loops:
  - [x] `(while (lt x 10) (println x) (def x (+ x 1)))`
  - [x] `(while true (println "hello!") (break))`
- [x] Arithmetic:
  - [x] `(+ 1 2)`
  - [x] `(- 1 2)`
  - [x] `(* 1 2)`
  - [x] `(/ 1 2)`
  - [x] `(mod 1 2)`
- [x] Comparison:
  - [x] `(= 1 2)`
  - [x] `(!= 1 2)`
  - [x] `(> 1 2)`
  - [x] `(>= 1 2)`
  - [x] `(< 1 2)`
  - [x] `(<= 1 2)`
- [x] Arrays:
  - [x] `(def x [1 2 3])`
  - [x] `(get x 0)`
  - [x] `(set x 0 4)`
  - [x] `(len x)`
  - [x] `(push x 4)`
  - [x] `(pop x)`
- [x] Strings:
  - [x] `(explode "hello")`
  - [x] `(str "hello" "world" ...)`
  - [x] `(println "Hello!")`