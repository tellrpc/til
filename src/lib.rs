mod lexer {
    use crate::source_cluster::SourceCluster;
    use crate::source_segmentation::{SourceSegmentation, SourceSegments};
    use crate::token::{FloatLiteralKind, IntLiteralKind, Item, ItemKind, Location, Span};
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
    }

    /// Iterator produces a stream of token::Item's by consuming the internal
    /// iterator over SourceClusters
    impl Iterator for Lexer<'_> {
        type Item = Result;

        fn next(&mut self) -> Option<Self::Item> {
            while let Some(cluster) = self.segments.next() {
                let maybe_result = match cluster {
                    cl if cl.is_base10_digit() || cl.cluster() == "-" => {
                        Some(self.numeric_literal(cl))
                    }
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

        macro_rules! test_token_kind {
            ($token_kind:expr, $ttype:path, $name:ident, $test:block) => {
                 if let $ttype($name) = $token_kind $test
                 else {panic!("not a {}", stringify!($ttype))}
            }
        }

        macro_rules! test_token {
            ($token:expr, $ttype:path, $value:expr, $span:expr) => {
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
                test_token_kind!(item.kind(), $ttype, tkn, {
                    assert_eq!($value, tkn.value(), "value is unexpected");
                });
            };
        }

        macro_rules! test_token_approx {
            ($token:expr, $ttype:path, $value:expr, $span:expr) => {
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
                test_token_kind!(item.kind(), $ttype, tkn, {
                    assert_approx_eq!($value, tkn.value());
                });
            };
        }

        #[test]
        fn emits_an_int_literal_token() -> result::Result<(), LexerError> {
            test_token!(
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
            test_token!(
                lexer.next().expect("no token one")?,
                ItemKind::IntLiteral,
                123,
                Span::new(1, 1, 1, 4)
            );
            test_token!(
                lexer.next().expect("no token two")?,
                ItemKind::IntLiteral,
                456,
                Span::new(1, 5, 1, 8)
            );
            Ok(())
        }

        #[test]
        fn emits_a_negative_int_literal_token() -> result::Result<(), LexerError> {
            test_token!(
                "-123".lex().next().expect("no token")?,
                ItemKind::IntLiteral,
                -123,
                Span::new(1, 1, 1, 5)
            );
            Ok(())
        }

        #[test]
        fn emits_a_float_literal_token() -> result::Result<(), LexerError> {
            test_token_approx!(
                "123.456".lex().next().expect("no token")?,
                ItemKind::FloatLiteral,
                123.456,
                Span::new(1, 1, 1, 8)
            );
            Ok(())
        }

        #[test]
        fn emits_a_negative_float_literal_token() -> result::Result<(), LexerError> {
            test_token_approx!(
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
            test_token!(
                lexer.next().expect("no token one")?,
                ItemKind::FloatLiteral,
                12.34,
                Span::new(1, 1, 1, 6)
            );
            test_token!(
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
        #[ignore]
        fn emits_newline_tokens() {
            unimplemented!()
        }

        #[test]
        #[ignore]
        fn emits_only_a_single_newline_for_many_consecutive_newlines() {
            unimplemented!()
        }
    }
}

mod token {
    use std::fmt;
    use std::fmt::{Debug, Display, Formatter};

    #[derive(Debug)]
    pub struct Location {
        line: u32,
        column: u32,
    }

    impl Location {
        pub fn new(line: u32, column: u32) -> Location {
            Location { line, column }
        }
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

    impl Default for Location {
        fn default() -> Self {
            Location {
                line: 0,
                column: 0,
            }
        }
    }

    #[derive(Debug)]
    pub struct Span {
        from: Location,
        to: Location,
    }

    impl Span {
        pub fn new(from_line: u32, from_column: u32, to_line: u32, to_column: u32) -> Span {
            Span {
                from: Location::new(from_line, from_column),
                to: Location::new(to_line, to_column),
            }
        }

        pub fn from(&self) -> &Location {
            &self.from
        }

        pub fn to(&self) -> &Location {
            &self.to
        }

        pub fn set_from(&mut self, from: Location) {
            self.from = from;
        }

        pub fn set_to(&mut self, to: Location) {
            self.to = to;
        }
    }

    impl Default for Span {
        fn default() -> Self {
            Span{
                from: Location::default(),
                to: Location::default(),
            }
        }
    }

    impl Display for Span {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "(from: {}, to: {})", self.from, self.to)
        }
    }

    #[derive(Debug)]
    pub struct Item {
        span: Span,
        kind: ItemKind,
    }

    impl Item {
        pub fn new(span: Span, kind: ItemKind) -> Item {
            Item { span, kind }
        }

        pub fn span(&self) -> &Span {
            &self.span
        }

        pub fn kind(&self) -> &ItemKind {
            &self.kind
        }

        pub fn repr(&self) -> String {
            match self.kind {
                ItemKind::StringLiteral(ref tkn) => tkn.repr(),
                ItemKind::IntLiteral(ref tkn) => tkn.repr(),
                ItemKind::FloatLiteral(ref tkn) => tkn.repr(),
                ItemKind::BoolLiteral(ref tkn) => tkn.repr(),
            }
        }
    }

    #[derive(Debug)]
    pub struct StringLiteralKind {
        value: String,
    }

    impl StringLiteralKind {
        pub fn new(value: String) -> StringLiteralKind {
            StringLiteralKind { value }
        }

        pub fn value(&self) -> &str {
            &self.value
        }

        pub fn repr(&self) -> String {
            format!("\"{}\"", self.value)
        }
    }

    #[derive(Debug)]
    pub struct LiteralKind<T: Debug + Display + Copy> {
        value: T,
    }

    impl<T: Debug + Display + Copy> LiteralKind<T> {
        pub fn new(value: T) -> LiteralKind<T> {
            LiteralKind { value }
        }

        pub fn value(&self) -> T {
            self.value
        }

        pub fn repr(&self) -> String {
            format!("{}", self.value)
        }
    }

    impl<T: Debug + Display + Copy> Display for LiteralKind<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }

    pub type IntLiteralKind = LiteralKind<i64>;
    pub type FloatLiteralKind = LiteralKind<f64>;
    pub type BoolLiteralKind = LiteralKind<bool>;

    #[derive(Debug)]
    pub enum ItemKind {
        // Literal Types
        StringLiteral(StringLiteralKind),
        IntLiteral(IntLiteralKind),
        FloatLiteral(FloatLiteralKind),
        BoolLiteral(BoolLiteralKind),
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

        fn testable_span() -> Span {
            Span::new(0,1,2,3)
        }

        fn test_span(span: &Span) {
            assert_eq!(0, span.from.line());
            assert_eq!(1, span.from().column());
            assert_eq!(2, span.to().line());
            assert_eq!(3, span.to().column());
        }

        macro_rules! test_token_kind {
            ($item:expr, $kind:path, $name:ident, $test:block) => {
                if let $kind($name) = $item.kind() $test
                else {
                    panic!("not a {}", stringify!($kind));
                }
            }
        }

        #[test]
        fn string_literal_token_properties_return_correct_values() {
            // let str_lit = StringLiteralToken::new("Hello".to_string());
            let str_lit = Item::new(
                testable_span(),
                ItemKind::StringLiteral(StringLiteralKind::new("Hello".to_string())),
            );

            test_span(str_lit.span());
            assert_eq!("\"Hello\"", str_lit.repr());
            test_token_kind!(str_lit, ItemKind::StringLiteral, tkn, {
                assert_eq!("Hello", tkn.value);
            });
        }

        #[test]
        fn int_literal_token_properties_return_correct_values() {
            let int_lit = Item::new(testable_span(), ItemKind::IntLiteral(IntLiteralKind::new(123)));

            test_span(int_lit.span());
            assert_eq!("123", int_lit.repr());
            test_token_kind!(int_lit, ItemKind::IntLiteral, tkn, {
               assert_eq!(123, tkn.value());
            });

        }

        #[test]
        fn float_literal_token_properties_return_correct_values() {
            let float_lit = Item::new(testable_span(), ItemKind::FloatLiteral(FloatLiteralKind::new(123.456)));
            test_span(float_lit.span());
            assert_eq!("123.456", float_lit.repr());
            test_token_kind!(float_lit, ItemKind::FloatLiteral, tkn, {
                assert_approx_eq!(123.456, tkn.value());
            });
        }

        #[test]
        fn bool_literal_token_properties_return_correct_values() {
            let bool_lit = Item::new(testable_span(), ItemKind::BoolLiteral(BoolLiteralKind::new(true)));
            assert_eq!("true", bool_lit.repr());
            test_token_kind!(bool_lit, ItemKind::BoolLiteral, tkn, {
                assert_eq!(true, tkn.value());
            });
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
                let result = SourceCluster::new(normalise_newline(cluster), self.line, self.column);

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
