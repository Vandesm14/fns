use chumsky::prelude::*;
use lasso::{Rodeo, Spur};

fn main() {
    let source = r#"
        (defn i32 (int) (@wat (@i32.const int)))
        (defn i64 (int) (@wat (@i64.const int)))
        (defn f32 (int) (@wat (@f32.const int)))
        (defn f64 (int) (@wat (@f64.const int)))

        (def false (i32 0))
        (def true (i32 1))

        (defn add (lhs rhs) (@wat (i32.add $lhs $rhs)))
    "#;

    let mut interner: Rodeo<Spur> = Rodeo::new();

    let tokens = fns::lex::lexer::<_, _, _, Vec<_>, Rich<_>>()
        .parse_with_state(source, &mut interner)
        .into_result();

    let tokens = match tokens {
        Ok(tokens) => tokens,
        Err(errors) => {
            eprintln!("ERRORS:");
            for error in errors.into_iter() {
                eprintln!("{error}");
            }
            std::process::exit(1)
        }
    };

    let stmts = fns::parse::parser::<_, _, _, Vec<_>, Rich<_>>()
        .parse_with_state(
            tokens
                .as_slice()
                .spanned((source.len()..source.len()).into()),
            &mut interner,
        )
        .into_result();

    let stmts = match stmts {
        Ok(stmts) => stmts,
        Err(errors) => {
            eprintln!("ERRORS:");
            for error in errors.into_iter() {
                eprintln!("{error}");
            }
            std::process::exit(1)
        }
    };

    for (stmt, _) in stmts.into_iter() {
        println!("{stmt}");
    }
}
