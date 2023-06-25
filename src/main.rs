use chumsky::prelude::*;
use lasso::{Rodeo, Spur};

fn main() {
    let source = "(@wat (@i32.const -12))";

    let mut interner: Rodeo<Spur> = Rodeo::new();

    let tokens = fns::lex::lexer::<_, _, _, Vec<_>>()
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

    let stmts = fns::parse::parser::<_, _, _, Vec<_>>()
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
