//!

use core::{fmt, iter};

use chumsky::{input::StrInput, util::MaybeRef};
use lasso::{LassoError, LassoErrorKind};

///
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Error<'source, I>
where
    I: StrInput<'source, char>,
{
    /// An unexpected input was found.
    ExpectedFound {
        /// The expected tokens.
        expected: Vec<Option<MaybeRef<'source, I::Token>>>,
        /// The found tokens.
        found: Option<MaybeRef<'source, I::Token>>,
    },
    /// Unable to intern a <code>&[str]</code>.
    CannotIntern(LassoError),
}

impl<'source, I> chumsky::error::Error<'source, I> for Error<'source, I>
where
    I: StrInput<'source, char>,
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

impl<'source, I> fmt::Display for Error<'source, I>
where
    I: StrInput<'source, char>,
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
            Self::CannotIntern(error) => match error.kind() {
                LassoErrorKind::MemoryLimitReached => {
                    f.write_str("configured memory limit was reached")
                }
                LassoErrorKind::KeySpaceExhaustion => {
                    f.write_str("key space was exhausted")
                }
                LassoErrorKind::FailedAllocation => {
                    f.write_str("unable to allocate memory")
                }
            },
        }
    }
}
