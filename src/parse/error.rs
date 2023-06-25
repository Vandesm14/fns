//!

use core::{fmt, iter};

use chumsky::{input::ValueInput, util::MaybeRef};
use lasso::Key;

use crate::lex::token::Token;

///
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error<'source, K, I>
where
    K: 'source,
    I: ValueInput<'source, Token = Token<K>>,
{
    /// An unexpected input was found.
    ExpectedFound {
        /// The expected tokens.
        expected: Vec<Option<MaybeRef<'source, I::Token>>>,
        /// The found tokens.
        found: Option<MaybeRef<'source, I::Token>>,
    },
}

impl<'source, K, I> chumsky::error::Error<'source, I> for Error<'source, K, I>
where
    K: 'source,
    I: ValueInput<'source, Token = Token<K>>,
{
    fn expected_found<
        E: IntoIterator<Item = Option<MaybeRef<'source, I::Token>>>,
    >(
        expected: E,
        found: Option<MaybeRef<'source, I::Token>>,
        _span: I::Span,
    ) -> Self {
        Self::ExpectedFound {
            expected: expected.into_iter().collect(),
            found,
        }
    }
}

impl<'source, K, I> fmt::Display for Error<'source, K, I>
where
    K: 'source + Key,
    I: ValueInput<'source, Token = Token<K>>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedFound {
                expected, found, ..
            } => {
                write!(f, "found ")?;

                match found {
                    Some(found) => write!(f, "{}", found.into_inner()),
                    None => write!(f, "end of input"),
                }?;

                write!(f, " but expected ")?;

                if expected.is_empty() {
                    write!(f, "something else")
                } else {
                    expected
                        .iter()
                        .zip(iter::once("").chain(iter::repeat(", ")))
                        .try_for_each(|(expected, sep)| {
                            write!(f, "{sep}")?;
                            match expected {
                                Some(expected) => {
                                    write!(f, "{}", expected.into_inner())
                                }
                                None => write!(f, "end of input"),
                            }
                        })
                }
            }
        }
    }
}
