# Primitives

## Language

- [x] Expressions: `(...)`
- [x] Lists/Arrays/Sequences: `[...]`
- [x] Strings:
  - [ ] `"..."`
  - [ ] `"\""`
- [x] Numbers:
  - [ ] `1`
  - [ ] `1.0`
  - [ ] `-1`
  - [ ] `-1.0`
- [ ] Booleans: `true` `false`
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
- [ ] Arrays:
  - [ ] `(def x [1 2 3])`
  - [ ] `(get x 0)`
  - [ ] `(set x 0 4)`
  - [ ] `(len x)`
  - [ ] `(push x 4)`
  - [ ] `(pop x)`
- [x] Strings:
  - [x] `(explode "hello")`
  - [x] `(str "hello" "world" ...)`
  - [x] `(println "Hello!")`