use chumsky::prelude::*;
use fns::parse::ParserInput;
use lasso::Rodeo;

fn main() {
  let file_path = std::env::args()
    .nth(1)
    .expect("No input file path provided");
  let source =
    std::fs::read_to_string(&file_path).expect("Unable to read file");

  let mut scope = fns::eval::Scope::<_, Rodeo>::default();

  let (tokens, errors) = fns::lex::lexer::<_, _, _, Vec<_>, Rich<_>>()
    .parse_with_state(source.as_str(), &mut scope.interner)
    .into_output_errors();

  if !errors.is_empty() {
    println!("TOKEN ERRORS:");
    errors.iter().for_each(|error| println!("  {error:?}"));
  }

  if let Some(tokens) = tokens {
    // println!("TOKENS:");
    // tokens.iter().for_each(|token| println!("  {token:?}"));

    let (exprs, errors) =
      fns::parse::parser::<_, _, ParserInput<_, _>, Vec<_>, Rich<_>>()
        .parse_with_state(
          tokens
            .as_slice()
            .spanned((source.len()..source.len()).into()),
          &mut scope.interner,
        )
        .into_output_errors();

    if !errors.is_empty() {
      println!("EXPR ERRORS:");
      errors.iter().for_each(|error| println!("  {error:?}"));
    }

    if let Some(exprs) = exprs {
      // println!("EXPRS:");
      // exprs.iter().for_each(|expr| println!("  {expr:?}"));

      println!(
        "RESULT: {:?}",
        fns::eval::eval(exprs.into_iter(), &mut scope)
      );
    }
  }

  // let mut scope = Scope::default();

  // let (result, _exprs) = eval(&src, &mut scope, filename);

  // // println!("Exprs: {:?}", exprs);
  // // println!("Program: {:?}", program);
  // println!("Result: {:?}", result);
}
