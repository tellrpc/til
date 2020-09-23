mod lexer {
    use std::convert;
    use std::error;
    use std::fmt;
    use std::iter;
    use std::num;
    use std::result;
    use crate::token::{AsLocation, Token, IntLiteralToken, FloatLiteralToken};
    use crate::source_cluster::SourceCluster;
    use crate::source_segmentation::{SourceSegmentation, SourceSegments};
    use std::num::{ParseIntError, ParseFloatError};
    use std::error::Error;


    #[derive(Debug)]
    struct LexerError {
        reason: String,
    }

    impl convert::From<ParseIntError> for LexerError {
        fn from(e: ParseIntError) -> Self {
            LexerError::new(e.to_string())
        }
    }

    impl convert::From<ParseFloatError> for LexerError {
        fn from(e: ParseFloatError) -> Self {
            LexerError::new(e.to_string())
        }
    }

    impl LexerError {
        fn new(reason: String) -> LexerError {
            LexerError {
                reason,
            }
        }
    }

    impl fmt::Display for LexerError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "LexerError: {}", self.reason)
        }
    }

    impl error::Error for LexerError {}

    type Result = result::Result<Token, LexerError>;

    struct Lexer<'a> {
        source: &'a str,
        segments: iter::Peekable<SourceSegments<'a>>,
    }

    impl Lexer<'_> {
        fn consume_next(&mut self) -> result::Result<SourceCluster, LexerError> {
            if let Some(sc) = self.segments.next() {
                Ok(sc)
            } else {
                Err(LexerError::new("unexpected EOF in segment stream".to_string()))
            }
        }
        fn numeric_literal(&mut self, cl: SourceCluster) -> Result {
            let mut repr = cl.cluster().to_string();
            while let Some(peeked) = self.segments.peek() {
                match peeked {
                    pk if pk.is_base10_digit() => {
                        let sc = self.consume_next()?;
                        repr += sc.cluster();
                    }
                    pk if pk.cluster() == "." => {
                        self.consume_next()?;
                        repr += ".";
                        return self.float_literal(cl, repr);
                    }
                    _ => break,
                }
            }

            let val = repr.parse::<i64>()?;
            Ok(Token::IntLiteral(IntLiteralToken::new(val, cl.line(), cl.column())))
        }

        fn float_literal(&mut self, cl: SourceCluster, mut repr: String) -> Result {
            while let Some(peeked) = self.segments.peek() {
                match peeked {
                    pk if pk.is_base10_digit() => {
                        let sc = self.consume_next()?;
                        repr += sc.cluster();
                    }
                    _ => break,
                }
            }
            let val = repr.parse::<f64>()?;
            Ok(Token::FloatLiteral(FloatLiteralToken::new(val, cl.line(), cl.column())))
        }
    }

    impl Iterator for Lexer<'_> {
        type Item = Result;

        fn next(&mut self) -> Option<Self::Item> {
            while let Some(cluster) = self.segments.next() {
                let maybe_result = match cluster {
                    cl if cl.is_base10_digit() || cl.cluster() == "-" => Some(self.numeric_literal(cl)),
                    cl => Some(Err(LexerError::new(format!("Unexpected character: {}", cl.cluster()))))
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

    trait Lexing {
        fn lex(&self) -> Lexer;
    }

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

        #[test]
        fn emits_an_int_literal_token() -> result::Result<(), LexerError> {
            match "123".lex().next().expect("no token")? {
                Token::IntLiteral(tkn) => {
                    assert_eq!(123, tkn.value());
                    assert_eq!(1, tkn.as_location().line());
                    assert_eq!(1, tkn.as_location().column());
                }
                _ => panic!("not an IntLiteral"),
            }

            Ok(())
        }

        #[test]
        fn emits_a_negative_int_literal_token() -> result::Result<(), LexerError> {
            match "-123".lex().next().expect("no token")? {
                Token::IntLiteral(tkn) => {
                    assert_eq!(-123, tkn.value());
                    assert_eq!(1, tkn.as_location().line());
                    assert_eq!(1, tkn.as_location().column());
                }
                _ => panic!("not an IntLiteral"),
            }

            Ok(())
        }

        #[test]
        fn emits_a_float_literal_token() -> result::Result<(), LexerError> {
            match "123.456".lex().next().expect("no token")? {
                Token::FloatLiteral(tkn) => {
                    assert_approx_eq!(123.456, tkn.value());
                    assert_eq!(1, tkn.as_location().line());
                    assert_eq!(1, tkn.as_location().column());
                }
                _ => panic!("not a float literal")
            }

            Ok(())
        }

        #[test]
        fn emits_a_negative_float_literal_token() -> result::Result<(), LexerError> {
            match "-123.456".lex().next().expect("no token")? {
                Token::FloatLiteral(tkn) => {
                    assert_approx_eq!(-123.456, tkn.value());
                    assert_eq!(1, tkn.as_location().line());
                    assert_eq!(1, tkn.as_location().column());
                }
                _ => panic!("not a float literal")
            }

            Ok(())
        }
    }
}

mod token {
    use std::fmt;
    use std::fmt::{Display, Debug, Formatter};

    #[derive(Debug)]
    pub struct Location {
        line: u32,
        column: u32,
    }

    impl Location {
        pub fn line(&self) -> u32 {
            self.line
        }

        pub fn column(&self) -> u32 {
            self.column
        }
    }

    impl Display for Location {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "(line: {}, column: {})", self.line, self.column)
        }
    }

    pub trait AsLocation {
        fn as_location(&self) -> &Location;
    }

    pub trait Representation {
        fn repr(&self) -> String;
    }

    #[derive(Debug)]
    pub struct StringLiteralToken {
        value: String,
        location: Location
    }

    impl StringLiteralToken {
        pub fn new(value: String, line: u32, column: u32) -> StringLiteralToken {
            StringLiteralToken { value, location: Location { line, column } }
        }

        pub fn value(&self) -> &str {
            &self.value
        }
    }

    impl AsLocation for StringLiteralToken {
        fn as_location(&self) -> &Location {
            &self.location
        }
    }

    impl Representation for StringLiteralToken {
        fn repr(&self) -> String {
            format!("\"{}\"", self.value)
        }
    }

    #[derive(Debug)]
    pub struct LiteralToken<T: Debug + Display + Copy> {
        value: T,
        location: Location,
    }


    impl<T: Debug + Display + Copy> LiteralToken<T> {
        pub fn new(value: T, line: u32, column: u32) -> LiteralToken<T> {
            LiteralToken {
                value,
                location: Location { line, column }
            }
        }

        pub fn repr(&self) -> String {
            format!("{}", self.value)
        }

        pub fn value(&self) -> T { self.value }
    }

    impl <T: Debug + Display + Copy> Display for LiteralToken<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }

    impl <T: Debug + Display + Copy> AsLocation for LiteralToken<T> {
        fn as_location(&self) -> &Location {
            &self.location
        }
    }

    impl <T: Debug + Display + Copy> Representation for LiteralToken<T> {
        fn repr(&self) -> String {
            format!("{}", self.value)
        }
    }

    pub type IntLiteralToken = LiteralToken<i64>;
    pub type FloatLiteralToken = LiteralToken<f64>;
    pub type BoolLiteralToken  = LiteralToken<bool>;

    #[derive(Debug)]
    pub enum Token {
        // Literal Types
        StringLiteral(StringLiteralToken),
        IntLiteral(IntLiteralToken),
        FloatLiteral(FloatLiteralToken),
        BoolLiteral(BoolLiteralToken),
        // Comment Types
        // DocComment,
        // // Punctuation
        // Bang,
        // Colon,
        // QMark,
        // LBrace,
        // RBrace,
        // LBracket,
        // RBracket,
        // LParen,
        // RParen,
        // At,
        // // Keywords
        // MessageKeyword,
        // ListKeyword,
        // MapKeyword,
        // ServiceKeyword,
        // FloatKeyword,
        // IntKeyword,
        // BoolKeyword,
        // StringKeyword,
        // TimeKeyword,
        // //Whitespace
        // LineFeed,
        // EOF,
    }

    #[cfg(test)]
    mod test {
        use super::*;
        use assert_approx_eq::assert_approx_eq;

        #[test]
        fn string_literal_token_properties_return_correct_values() {
            let str_lit = StringLiteralToken::new("Hello".to_string(), 1, 2);
            assert_eq!("Hello", str_lit.value());
            assert_eq!("\"Hello\"", str_lit.repr());
            assert_eq!(1, str_lit.as_location().line(), "line has the wrong value");
            assert_eq!(2, str_lit.as_location().column(), "column has the wrong value");
        }

        #[test]
        fn int_literal_token_properties_return_correct_values() {
            let int_lit = IntLiteralToken::new(123, 1, 2);
            assert_eq!(123, int_lit.value());
            assert_eq!("123", int_lit.repr());
            assert_eq!(1, int_lit.as_location().line(), "line has wrong value");
            assert_eq!(2, int_lit.as_location().column(), "column has wrong value");
        }

        #[test]
        fn float_literal_token_properties_return_correct_values() {
            let float_lit = FloatLiteralToken::new(123.456, 1, 2);
            assert_approx_eq!(123.456, float_lit.value());
            assert_eq!("123.456", float_lit.repr());
            assert_eq!(1, float_lit.as_location().line(), "line has wrong value");
            assert_eq!(2, float_lit.as_location().column(), "column has wrong value");
        }

        #[test]
        fn bool_literal_token_properties_return_correct_values() {
            let bool_lit = BoolLiteralToken::new(true, 1, 2);
            assert_eq!(true, bool_lit.value());
            assert_eq!("true", bool_lit.repr());
            assert_eq!(1, bool_lit.as_location().line(), "line has wrong value");
            assert_eq!(2, bool_lit.as_location().column(), "column has wrong value");
        }
    }
}

mod source_segmentation {
    use crate::source_cluster::SourceCluster;
    use unicode_segmentation::{Graphemes, UnicodeSegmentation};

    /// Container for an iterator over source segments
    pub struct SourceSegments<'a> {
        column: u32,
        line: u32,
        graphemes: Graphemes<'a>,
    }

    impl SourceSegments<'_> {
        /// construct a new SourceSegments
        pub fn new(source: &str) -> SourceSegments {
            SourceSegments {
                graphemes: source.graphemes(true),
                column: 1,
                line: 1,
            }
        }
    }

    impl<'a> Iterator for SourceSegments<'a> {
        type Item = SourceCluster<'a>;

        fn next(&mut self) -> Option<Self::Item> {
            // normalise \r\n to \n
            let normalise_newline = |gc| {
                if gc == "\r\n" {
                    "\n"
                } else {
                    gc
                }
            };

            self.graphemes.next().map(|cluster| {
                let result = SourceCluster::new(
                    normalise_newline(cluster),
                    self.line,
                    self.column,
                );

                if result.is_newline() {
                    self.line += 1;
                    self.column = 1;
                } else {
                    self.column += 1;
                }

                result
            })
        }
    }

    pub trait SourceSegmentation {
        ///Return an iterator over source segments
        fn source_clusters(&self) -> SourceSegments;
    }

    impl SourceSegmentation for &str {
        fn source_clusters(&self) -> SourceSegments {
            SourceSegments::new(self)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn source_segments_returns_source_segments_struct() {
            // if this compiles it works for this test's purposes
            let _source_seg: SourceSegments = "Mary had a little lamb".source_clusters();
        }

        #[test]
        fn source_segments_returns_an_iterator_over_the_source_grapheme_clusters() {
            let source = "Mary had a little lamb.";
            assert_eq!(
                source.source_clusters().count(),
                source.graphemes(true).count()
            );
        }

        #[test]
        fn source_segments_correctly_increments_line_and_column_values() {
            let source = "ab\r\ncd\r\nநி"; // the \r\n grapheme cluster will be normalised to \n
            let mut iter = source.source_clusters();

            let test_item = |sc: SourceCluster, el: u32, ec: u32, egc: &str| {
                assert_eq!(el, sc.line(), "wrong line for cluster {:?}", sc);
                assert_eq!(ec, sc.column(), "wrong column for cluster {:?}", sc);
                assert_eq!(
                    sc.grapheme_cluster(),
                    egc,
                    "wrong grapheme cluster for cluster {:?}",
                    sc
                );
            };

            test_item(iter.next().expect("no cluster for 'a'"), 1, 1, "a");
            test_item(iter.next().expect("no cluster for 'b'"), 1, 2, "b");
            test_item(iter.next().expect("no cluster for '\n'"), 1, 3, "\n");
            test_item(iter.next().expect("no cluster for 'c'"), 2, 1, "c");
            test_item(iter.next().expect("no cluster for 'd'"), 2, 2, "d");
            test_item(iter.next().expect("no cluster for '\n' 2"), 2, 3, "\n");
            test_item(iter.next().expect("no cluster for 'நி'"), 3, 1, "நி");
        }
    }
}

mod source_cluster {

    const ALPHA_MASK: u8 = 1;
    const ALPHANUMERIC_MASK: u8 = 1 << 1;
    const DIGIT_MASK: u8 = 1 << 2;
    const LOWERCASE_MASK: u8 = 1 << 3;
    const UPPERCASE_MASK: u8 = 1 << 4;
    const WHITESPACE_MASK: u8 = 1 << 5;
    const NEWLINE_MASK: u8 = 1 << 6;

    #[derive(Debug)]
    pub struct SourceCluster<'a> {
        grapheme_cluster: &'a str,
        column: u32,
        line: u32,
        unicode_characteristics: u8,
    }

    impl SourceCluster<'_> {
        /// Construct a new SourceCluster. The source paramter should be a valid GraphemeCluster as
        /// returned by the unicode_segmentation crate
        pub fn new(source: &str, line: u32, column: u32) -> SourceCluster {
            // only test the first char of the grapheme cluster.
            // uses take(1).fold(...) so that empty clusters have no characteristics
            let unicode_characteristics: u8 = source.chars().take(1).fold(0u8, |mut acc, c| {
                if c.is_alphabetic() {
                    acc |= ALPHA_MASK
                };
                if c.is_alphanumeric() {
                    acc |= ALPHANUMERIC_MASK
                };
                if c.is_digit(10) {
                    acc |= DIGIT_MASK
                };
                if c.is_lowercase() {
                    acc |= LOWERCASE_MASK
                };
                if c.is_uppercase() {
                    acc |= UPPERCASE_MASK
                };
                if c.is_whitespace() {
                    acc |= WHITESPACE_MASK
                };
                if c == '\n' {
                    acc |= NEWLINE_MASK
                };
                acc
            });

            SourceCluster {
                grapheme_cluster: source,
                column,
                line,
                unicode_characteristics,
            }
        }

        pub(crate) fn cluster(&self) -> &str {
            &self.grapheme_cluster
        }

        #[inline]
        fn test_characteristic(&self, mask: u8) -> bool {
            self.unicode_characteristics & mask != 0
        }

        /// getter for the line of the source cluster
        pub fn line(&self) -> u32 {
            self.line
        }

        /// getter for the column of the source cluster
        pub fn column(&self) -> u32 {
            self.column
        }

        /// getter for the underlying grapheme cluster
        pub fn grapheme_cluster(&self) -> &str {
            &self.grapheme_cluster
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_alphabetic(&self) -> bool {
            self.test_characteristic(ALPHA_MASK)
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_alphanumeric(&self) -> bool {
            self.test_characteristic(ALPHANUMERIC_MASK)
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_base10_digit(&self) -> bool {
            self.test_characteristic(DIGIT_MASK)
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_lowercase(&self) -> bool {
            self.test_characteristic(LOWERCASE_MASK)
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_uppercase(&self) -> bool {
            self.test_characteristic(UPPERCASE_MASK)
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_whitespace(&self) -> bool {
            self.test_characteristic(WHITESPACE_MASK)
        }

        /// true if true for the first char of the owned grapheme cluster
        pub fn is_newline(&self) -> bool {
            self.test_characteristic(NEWLINE_MASK)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::SourceCluster;

        fn test_cluster(source: &str) -> SourceCluster {
            SourceCluster::new(source, 0, 0)
        }

        #[test]
        fn alphabetic_source_cluster_is_alphabetic() {
            //ascii letter
            assert!(test_cluster("a").is_alphabetic());
            //non-ascii letter
            assert!(test_cluster("ந").is_alphabetic());
            //alpha grapheme cluster
            assert!(test_cluster("நி").is_alphabetic());
        }

        #[test]
        fn nonalphabetic_souce_cluster_is_not_alphabetic() {
            //number
            assert!(!test_cluster("1").is_alphabetic());
            //whitespace
            assert!(!test_cluster("\n").is_alphabetic());
            //empty
            assert!(!test_cluster("").is_alphabetic());
        }

        #[test]
        fn alphanumeric_source_cluster_is_alphanumeric() {
            //ascii letter
            assert!(test_cluster("a").is_alphanumeric());
            //non-ascii letter
            assert!(test_cluster("ந").is_alphanumeric());
            //alpha grapheme cluster
            assert!(test_cluster("நி").is_alphanumeric());
            //number
            assert!(test_cluster("1").is_alphanumeric());
        }

        #[test]
        fn nonalphanumeric_source_cluster_is_not_alphanumeric() {
            //whitespace
            assert!(!test_cluster("\t").is_alphanumeric());
        }

        #[test]
        fn base10_digit_is_base10_digit() {
            assert!(test_cluster("9").is_base10_digit());
        }

        #[test]
        fn non_base10_digit_is_not_base10_digit() {
            //ascii letter
            assert!(!test_cluster("n").is_base10_digit());
            //hex digit
            assert!(!test_cluster("f").is_base10_digit());
            //non ascii letter
            assert!(!test_cluster("ந").is_base10_digit());
            //non ascii grapheme cluster
            assert!(!test_cluster("நி").is_base10_digit());
        }

        #[test]
        fn lowercase_source_cluster_is_lowercase() {
            assert!(test_cluster("a").is_lowercase());
        }

        #[test]
        fn non_lowercase_source_cluster_is_not_lowercase() {
            assert!(!test_cluster("A").is_lowercase());
        }

        #[test]
        fn uppercase_source_cluster_is_uppercase() {
            assert!(test_cluster("A").is_uppercase());
        }

        #[test]
        fn non_uppercase_source_cluster_is_not_uppercase() {
            assert!(!test_cluster("a").is_uppercase());
        }

        #[test]
        fn whitespace_source_cluster_is_whitespace() {
            assert!(test_cluster("\n").is_whitespace());
        }

        #[test]
        fn non_whitespace_source_cluster_is_not_whitespace() {
            assert!(!test_cluster("a").is_whitespace());
        }

        #[test]
        fn newline_is_newline() {
            assert!(test_cluster("\n").is_newline());
        }

        #[test]
        fn line_returns_the_line_property() {
            assert_eq!(SourceCluster::new("a", 1, 2).line(), 1);
        }

        #[test]
        fn column_returns_the_column_property() {
            assert_eq!(SourceCluster::new("a", 1, 2).column(), 2);
        }

        #[test]
        fn grapheme_cluster_returns_the_grapheme_cluster() {
            assert_eq!(test_cluster("a").grapheme_cluster(), "a");
        }
    }
}
