use chumsky::span::SimpleSpan;

pub mod eval;
pub mod lex;
pub mod parse;

pub type Spanned<T> = (T, SimpleSpan);
