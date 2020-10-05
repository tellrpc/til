use crate::source_cluster::SourceCluster;
use crate::source_segmentation::{SourceSegmentation, SourceSegments};
use crate::token::{FloatLiteralKind, IntLiteralKind, Item, ItemKind, Location, NewlineKind, Span};
use std::convert;
use std::error;
use std::fmt;
use std::iter;
use std::num::{ParseFloatError, ParseIntError};
use std::result;

#[derive(Debug)]
pub struct LexerError {
    reason: String,
}

/// ParseIntError can be returned when parsing an IntegerLiteral value
impl convert::From<ParseIntError> for LexerError {
    fn from(e: ParseIntError) -> Self {
        LexerError::new(e.to_string())
    }
}

/// ParseFloatError can be returned when parsing a FloatLiteral value
impl convert::From<ParseFloatError> for LexerError {
    fn from(e: ParseFloatError) -> Self {
        LexerError::new(e.to_string())
    }
}

impl LexerError {
    fn new(reason: String) -> LexerError {
        LexerError { reason }
    }
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LexerError: {}", self.reason)
    }
}

impl error::Error for LexerError {}

type Result = result::Result<Item, LexerError>;

pub struct Lexer<'a> {
    source: &'a str,
    segments: iter::Peekable<SourceSegments<'a>>,
}

/// extend the span to include the location of the provided source cluster
#[inline]
fn extend_span(span: &mut Span, source_cluster: &SourceCluster) {
    span.set_to(Location::new(
        source_cluster.line(),
        source_cluster.column() + 1,
    ));
}

impl Lexer<'_> {
    /// Take the next value from the iterator of source clusters and return it, or
    /// an error if there is no next value available
    fn consume_next(&mut self) -> result::Result<SourceCluster, LexerError> {
        if let Some(sc) = self.segments.next() {
            Ok(sc)
        } else {
            Err(LexerError::new(
                "unexpected EOF in segment stream".to_string(),
            ))
        }
    }

    /// Return an Item whose kind is either IntLiteral or FloatLiteral, or an error
    fn numeric_literal(&mut self, cl: SourceCluster) -> Result {
        let mut repr = String::new();
        // the correct to location is set when update_repr is called.
        let mut span = Span::new(cl.line(), cl.column(), 0, 0);

        let mut update_repr = |sc: SourceCluster| {
            repr += sc.cluster();
            extend_span(&mut span, &sc);
        };

        update_repr(cl);

        while let Some(peeked) = self.segments.peek() {
            match peeked {
                pk if pk.is_base10_digit() => {
                    update_repr(self.consume_next()?);
                }
                pk if pk.cluster() == "." => {
                    update_repr(self.consume_next()?);
                    return self.float_literal(repr, span);
                }
                _ => break,
            }
        }

        let val = repr.parse::<i64>()?;
        Ok(Item::new(
            span,
            ItemKind::IntLiteral(IntLiteralKind::new(val)),
        ))
    }

    /// return an Item whose kind is FloatLiteral, or an error.
    fn float_literal(&mut self, mut repr: String, mut span: Span) -> Result {
        while let Some(peeked) = self.segments.peek() {
            match peeked {
                pk if pk.is_base10_digit() => {
                    let sc = self.consume_next()?;
                    repr += sc.cluster();
                    extend_span(&mut span, &sc);
                }
                _ => break,
            }
        }
        let val = repr.parse::<f64>()?;
        Ok(Item::new(
            span,
            ItemKind::FloatLiteral(FloatLiteralKind::new(val)),
        ))
    }

    /// return an item whose kind is Newline.
    /// Consumes all consecutive newlines and whitespace following the initial newline
    fn newline(&mut self, cl: SourceCluster) -> Result {
        let span = Span::new(cl.line(), cl.column(), cl.line(), cl.column() + 1);
        let item = Item::new(span, ItemKind::Newline(NewlineKind::new()));
        while let Some(peeked) = self.segments.peek() {
            match peeked {
                pk if pk.is_whitespace() => {
                    self.consume_next()?;
                }
                _ => break,
            }
        }
        Ok(item)
    }
}

/// Iterator produces a stream of token::Item's by consuming the internal
/// iterator over SourceClusters
impl Iterator for Lexer<'_> {
    type Item = Result;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cluster) = self.segments.next() {
            let maybe_result = match cluster {
                cl if cl.is_base10_digit() || cl.cluster() == "-" => Some(self.numeric_literal(cl)),
                cl if cl.is_newline() => Some(self.newline(cl)),
                cl if cl.is_whitespace() => None,
                cl => Some(Err(LexerError::new(format!(
                    "Unexpected character: {}",
                    cl.cluster()
                )))),
            };

            // if maybe_result is none, then we do not wish to emit the result of this loop
            // and should continue
            if let Some(result) = maybe_result {
                return Some(result);
            }
        }
        None
    }
}

/// Implemented by items which can produce a lexer iterator
/// (used to add the lex extension function to an &str
trait Lexing {
    fn lex(&self) -> Lexer;
}

/// Lexing implementation for &str
impl Lexing for &str {
    fn lex(&self) -> Lexer {
        Lexer {
            source: self,
            segments: self.source_clusters().peekable(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::token::*;
    use assert_approx_eq::assert_approx_eq;

    macro_rules! test_token_value {
            ($token_kind:expr, $ttype:path, $name:ident, $test:block) => {
                 if let $ttype($name) = $token_kind $test
                 else {panic!("not a {}", stringify!($ttype))}
            }
        }

    macro_rules! test_token_span {
        ($token:expr, $span:expr) => {
            let item = $token;
            let sp = $span;
            assert_eq!(
                sp.from().line(),
                item.span().from().line(),
                "from line has unexpected value"
            );
            assert_eq!(
                sp.from().column(),
                item.span().from().column(),
                "from column has unexpected value"
            );
            assert_eq!(
                sp.to().line(),
                item.span().to().line(),
                "to line has unexpected value"
            );
            assert_eq!(
                sp.to().column(),
                item.span().to().column(),
                "to column has unexpected value"
            );
        };
    }

    macro_rules! test_value_token {
        ($token:expr, $ttype:path, $value:expr, $span:expr) => {
            let item = $token;
            let sp = $span;
            test_token_span!(&item, &sp);
            test_token_value!(item.kind(), $ttype, knd, {
                assert_eq!($value, knd.value(), "value is unexpected");
            });
        };
    }

    macro_rules! test_value_token_approx {
        ($token:expr, $ttype:path, $value:expr, $span:expr) => {
            let item = $token;
            let sp = $span;
            test_token_span!(&item, &sp);
            test_token_value!(item.kind(), $ttype, knd, {
                assert_approx_eq!($value, knd.value());
            });
        };
    }

    macro_rules! test_const_token {
        ($token:expr, $ttype:path, $const_val:expr, $span:expr) => {
            let item = $token;
            let sp = $span;
            test_token_span!(&item, &sp);
            test_token_value!(item.kind(), $ttype, knd, {
                assert_eq!($const_val, knd.value());
            })
        };
    }

    #[test]
    fn emits_an_int_literal_token() -> result::Result<(), LexerError> {
        test_value_token!(
            "123".lex().next().expect("no token")?,
            ItemKind::IntLiteral,
            123,
            Span::new(1, 1, 1, 4)
        );
        Ok(())
    }

    #[test]
    fn emits_two_int_literal_tokens() -> result::Result<(), LexerError> {
        let mut lexer = "123 456".lex();
        test_value_token!(
            lexer.next().expect("no token one")?,
            ItemKind::IntLiteral,
            123,
            Span::new(1, 1, 1, 4)
        );
        test_value_token!(
            lexer.next().expect("no token two")?,
            ItemKind::IntLiteral,
            456,
            Span::new(1, 5, 1, 8)
        );
        Ok(())
    }

    #[test]
    fn emits_a_negative_int_literal_token() -> result::Result<(), LexerError> {
        test_value_token!(
            "-123".lex().next().expect("no token")?,
            ItemKind::IntLiteral,
            -123,
            Span::new(1, 1, 1, 5)
        );
        Ok(())
    }

    #[test]
    fn emits_a_float_literal_token() -> result::Result<(), LexerError> {
        test_value_token_approx!(
            "123.456".lex().next().expect("no token")?,
            ItemKind::FloatLiteral,
            123.456,
            Span::new(1, 1, 1, 8)
        );
        Ok(())
    }

    #[test]
    fn emits_a_negative_float_literal_token() -> result::Result<(), LexerError> {
        test_value_token_approx!(
            "-123.456".lex().next().expect("no token")?,
            ItemKind::FloatLiteral,
            -123.456,
            Span::new(1, 1, 1, 9)
        );
        Ok(())
    }

    #[test]
    fn emits_two_float_literal_tokens() -> result::Result<(), LexerError> {
        let mut lexer = "12.34 45.67".lex();
        test_value_token!(
            lexer.next().expect("no token one")?,
            ItemKind::FloatLiteral,
            12.34,
            Span::new(1, 1, 1, 6)
        );
        test_value_token!(
            lexer.next().expect("no token two")?,
            ItemKind::FloatLiteral,
            45.67,
            Span::new(1, 7, 1, 12)
        );
        Ok(())
    }

    #[test]
    #[ignore]
    fn consumes_leading_whitespace() {
        unimplemented!()
    }

    #[test]
    fn emits_newline_tokens() -> result::Result<(), LexerError> {
        let mut lexer = "123\n".lex();
        // ignore the first token, it is only there so the lexer doesn't consume it as a leading newline
        lexer.next().expect("no first token")?;
        test_const_token!(
            lexer.next().expect("no newline token")?,
            ItemKind::Newline,
            "\n",
            Span::new(1, 4, 1, 5)
        );
        Ok(())
    }

    #[test]
    fn emits_only_a_single_newline_for_consecutive_newlines_and_whitespace() -> result::Result<(), LexerError>
    {
        let mut lexer = "123\n \t \n\n".lex();
        // ignore the first token, it is only there so the lexer doesn't consume it as a leading newline
        lexer.next().expect("no first token")?;
        test_const_token!(
            lexer.next().expect("no newline token")?,
            ItemKind::Newline,
            "\n",
            Span::new(1, 4, 1, 5)
        );
        assert!(lexer.next().is_none(), "extra whitespace was not consumed");
        Ok(())
    }
}
