mod lexer {
    use std::convert;
    use std::error;
    use std::fmt;
    use std::iter;
    use std::num;
    use std::result;
    use crate::token;
    use crate::source_cluster;
    use crate::source_segmentation;
    use crate::source_segmentation::SourceSegmentation;
    use std::num::ParseIntError;
    use std::error::Error;


    #[derive(Debug)]
    struct LexerError {
        reason: String,
    }

    impl convert::From<num::ParseIntError> for LexerError {
        fn from(e: ParseIntError) -> Self {
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

    type Result = result::Result<Box<dyn token::Token>, LexerError>;

    struct Lexer<'a> {
        source: &'a str,
        segments: iter::Peekable<source_segmentation::SourceSegments<'a>>,
    }

    impl Lexer<'_> {
        fn consume_next(&mut self) -> result::Result<source_cluster::SourceCluster, LexerError> {
            if let Some(sc) = self.segments.next() {
                Ok(sc)
            } else {
                Err(LexerError::new("unexpected EOF in segment stream".to_string()))
            }
        }
        fn numeric_literal(&mut self, cl: source_cluster::SourceCluster) -> Result {
            let mut repr = cl.cluster().to_string();
            while let Some(peeked) = self.segments.next() {
                match peeked {
                    pk if pk.is_base10_digit() => {
                        let sc = self.consume_next()?;
                        repr += sc.cluster();
                    },
                    pk if pk.cluster() == "." => {
                        self.consume_next()?;
                        repr += ".";
                        return self.float_literal(cl, repr);
                    }
                    _ => break,
                }
            }

            let val = repr.parse::<i64>()?;
            Ok(Box::new(token::IntLiteralToken::new(val, cl.line(), cl.column())))
        }

        fn float_literal(&mut self, cl: source_cluster::SourceCluster, mut repr: String) -> Result {
            unimplemented!()
        }
    }

    impl Iterator for Lexer<'_> {
        type Item = Result;

        fn next(&mut self) -> Option<Self::Item> {
            while let Some(cluster) = self.segments.next() {
                let maybe_result = match cluster {
                    cl if cl.is_base10_digit() => Some(self.numeric_literal(cl)),
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

        #[test]
        fn emits_an_int_literal_token() -> result::Result<(), LexerError> {
            let tkn = "123".lex().next().expect("no token")?;
            assert_eq!(Type::IntLiteral, tkn.ttype());
            Ok(())
        }

        // TODO test for negative integers (and fix the implementation to support them)
        // TODO test floats and negative floats.
    }
}

mod token {
    use std::fmt::Display;

    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    pub enum Type {
        // Literal Types
        StringLiteral,
        IntLiteral,
        FloatLiteral,
        BoolLiteral,
        // Comment Types
        DocComment,
        // Punctuation
        Bang,
        Colon,
        QMark,
        LBrace,
        RBrace,
        LBracket,
        RBracket,
        LParen,
        RParen,
        At,
        // Keywords
        MessageKeyword,
        ListKeyword,
        MapKeyword,
        ServiceKeyword,
        FloatKeyword,
        IntKeyword,
        BoolKeyword,
        StringKeyword,
        TimeKeyword,
        //Whitespace
        LineFeed,
        EOF,
    }

    pub trait Token {
        fn ttype(&self) -> Type;
        fn repr(&self) -> String;
        fn line(&self) -> u32;
        fn column(&self) -> u32;
    }

    pub struct LiteralToken<T> {
        ttype: Type,
        formatter: Box<dyn Fn(&T) -> String>,
        value: T,
        line: u32,
        column: u32,
    }

    impl<T> Token for LiteralToken<T> {
        fn ttype(&self) -> Type {
            self.ttype
        }

        fn repr(&self) -> String {
            (self.formatter)(&self.value)
        }

        fn line(&self) -> u32 {
            self.line
        }

        fn column(&self) -> u32 {
            self.column
        }
    }

    /// creates a new function for a literal token
    macro_rules! literal_token_constructor {
        ($struct_name:ident, $type_name:ty, $ttype_name:path, $formatter:expr) => {
            /// construct a new $struct_name
            pub fn new(value: $type_name, line: u32, column: u32) -> $struct_name {
                $struct_name {
                    ttype: $ttype_name,
                    value,
                    formatter: Box::new($formatter),
                    line,
                    column,
                }
            }
        };
    }

    /// creates a value function for a literal token
    macro_rules! literal_value_function {
        ($type_name:ty) => {
            /// get the literal value
            pub fn value(&self) -> $type_name {
                self.value
            }
        }
    }

    /// declares and implements a LiteralToken type.
    macro_rules! literal_token_decl_and_impl {
        ($struct_name:ident, $type_name:ty, $ttype_name:path) => {
            /// A LiteralToken for the $type_name primitive and the $ttype_name token
            pub type $struct_name = LiteralToken<$type_name>;

            impl $struct_name {
                literal_token_constructor!($struct_name, $type_name, $ttype_name, |v: &$type_name| {format!("{}", v)});
                literal_value_function!($type_name);
            }
        }
    }

    /// A token for string literals
    pub type StringLiteralToken = LiteralToken<String>;

    /// String literal token has a slightly different implementation to the other literal token types
    /// and the compiler seems unable to differentiate between them, so string literal is defined here
    impl StringLiteralToken {
        literal_token_constructor!(
            StringLiteralToken,
            String,
            Type::StringLiteral,
            |v: &String| { format!("\"{}\"", v) }
        );

        pub fn value(&self) -> &str {
            &self.value
        }
    }

    literal_token_decl_and_impl!(IntLiteralToken, i64, Type::IntLiteral);

    literal_token_decl_and_impl!(FloatLiteralToken, f64, Type::FloatLiteral);

    literal_token_decl_and_impl!(BoolLiteralToken, bool, Type::BoolLiteral);

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn string_literal_token_properties_return_correct_values() {
            let str_lit = StringLiteralToken::new("Hello".to_string(), 1, 2);
            assert_eq!("Hello", str_lit.value());
            assert_eq!("\"Hello\"", str_lit.repr());
            assert_eq!(1, str_lit.line(), "line has the wrong value");
            assert_eq!(2, str_lit.column(), "column has the wrong value");
        }

        #[test]
        fn int_literal_token_properties_return_correct_values() {
            let int_lit = IntLiteralToken::new(123, 1, 2);
            assert_eq!(123, int_lit.value());
            assert_eq!(1, int_lit.line(), "line has wrong value");
            assert_eq!(2, int_lit.column(), "column has wrong value");
        }

        #[test]
        fn float_literal_token_properties_return_correct_values() {
            let float_lit = FloatLiteralToken::new(123.456, 1, 2);
            assert_eq!(123.456, float_lit.value());
            assert_eq!(1, float_lit.line(), "line has wrong value");
            assert_eq!(2, float_lit.column(), "column has wrong value");
        }

        #[test]
        fn bool_literal_token_properties_return_correct_values() {
            let bool_lit = BoolLiteralToken::new(true, 1, 2);
            assert_eq!(true, bool_lit.value());
            assert_eq!(1, bool_lit.line(), "line has wrong value");
            assert_eq!(2, bool_lit.column(), "column has wrong value");
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

    impl Iterator for SourceSegments<'_> {
        type Item = SourceCluster;

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
                    normalise_newline(cluster).to_string(),
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
    use std::rc::Rc;

    const ALPHA_MASK: u8 = 1;
    const ALPHANUMERIC_MASK: u8 = 1 << 1;
    const DIGIT_MASK: u8 = 1 << 2;
    const LOWERCASE_MASK: u8 = 1 << 3;
    const UPPERCASE_MASK: u8 = 1 << 4;
    const WHITESPACE_MASK: u8 = 1 << 5;
    const NEWLINE_MASK: u8 = 1 << 6;

    #[derive(Debug)]
    pub struct SourceCluster {
        grapheme_cluster: Rc<String>,
        column: u32,
        line: u32,
        unicode_characteristics: u8,
    }

    impl SourceCluster {
        /// Construct a new SourceCluster. The source paramter should be a valid GraphemeCluster as
        /// returned by the unicode_segmentation crate
        pub fn new(source: String, line: u32, column: u32) -> SourceCluster {
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
                grapheme_cluster: Rc::new(source),
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
            SourceCluster::new(source.to_string(), 0, 0)
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
            assert_eq!(SourceCluster::new("a".to_string(), 1, 2).line(), 1);
        }

        #[test]
        fn column_returns_the_column_property() {
            assert_eq!(SourceCluster::new("a".to_string(), 1, 2).column(), 2);
        }

        #[test]
        fn grapheme_cluster_returns_the_grapheme_cluster() {
            assert_eq!(test_cluster("a").grapheme_cluster(), "a");
        }
    }
}
