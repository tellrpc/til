use crate::token::ItemKind::Newline;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
/// Location describes a location in the source by line and column
pub struct Location {
    line: u32,
    column: u32,
}

impl Location {
    /// Construct a new location at the given line and column
    pub fn new(line: u32, column: u32) -> Location {
        Location { line, column }
    }

    /// Get the line of the location
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Get the column of the location
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
        Location { line: 0, column: 0 }
    }
}

/// Span describes a span of source starting at span.from and ending at span.to.
/// It is a half-open interval containing its start but not containing its end.
#[derive(Debug)]
pub struct Span {
    from: Location,
    to: Location,
}

impl Span {
    /// Construct a new span
    pub fn new(from_line: u32, from_column: u32, to_line: u32, to_column: u32) -> Span {
        Span {
            from: Location::new(from_line, from_column),
            to: Location::new(to_line, to_column),
        }
    }

    /// Get the start location of the span
    pub fn from(&self) -> &Location {
        &self.from
    }

    /// Get the end location of the span
    pub fn to(&self) -> &Location {
        &self.to
    }

    /// Set the start location of the span
    pub fn set_from(&mut self, from: Location) {
        self.from = from;
    }

    /// Set the end location of the span
    pub fn set_to(&mut self, to: Location) {
        self.to = to;
    }
}

impl Default for Span {
    fn default() -> Self {
        Span {
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

/// Item represents a single item in the token stream
#[derive(Debug)]
pub struct Item {
    span: Span,
    kind: ItemKind,
}

impl Item {
    /// Construct a new item
    pub fn new(span: Span, kind: ItemKind) -> Item {
        Item { span, kind }
    }

    /// Get the span of the item
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Get the kind of the item
    pub fn kind(&self) -> &ItemKind {
        &self.kind
    }

    /// Get a string representation of the item
    pub fn repr(&self) -> String {
        match self.kind {
            ItemKind::StringLiteral(ref knd) => knd.repr(),
            ItemKind::IntLiteral(ref knd) => knd.repr(),
            ItemKind::FloatLiteral(ref knd) => knd.repr(),
            ItemKind::BoolLiteral(ref knd) => knd.repr(),
            ItemKind::Newline(ref knd) => knd.repr(),
        }
    }
}

/// Kind descriptor for a StringLiteral
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

/// Kind descriptor for a literal whose underlying type implements Copy (int, float etc)
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

/// Kind descriptor for a kind whose contents are a const string (keywords, punctuation etc)
#[derive(Debug)]
pub struct ConstKind {
    value: &'static str,
}

impl ConstKind {
    pub fn value(&self) -> &str {
        self.value
    }

    pub fn repr(&self) -> String {
        self.value().to_string()
    }
}

const NEWLINE_REPR: &str = "\n";

/// Kind descriptor for a newline
pub type NewlineKind = ConstKind;

impl NewlineKind {
    pub fn new() -> NewlineKind {
        NewlineKind {
            value: NEWLINE_REPR,
        }
    }
}

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
    //Whitespace
    Newline(NewlineKind),
    // EOF,
}

#[cfg(test)]
mod test {
    use super::*;
    use assert_approx_eq::assert_approx_eq;

    fn testable_span() -> Span {
        Span::new(0, 1, 2, 3)
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
        let int_lit = Item::new(
            testable_span(),
            ItemKind::IntLiteral(IntLiteralKind::new(123)),
        );

        test_span(int_lit.span());
        assert_eq!("123", int_lit.repr());
        test_token_kind!(int_lit, ItemKind::IntLiteral, tkn, {
            assert_eq!(123, tkn.value());
        });
    }

    #[test]
    fn float_literal_token_properties_return_correct_values() {
        let float_lit = Item::new(
            testable_span(),
            ItemKind::FloatLiteral(FloatLiteralKind::new(123.456)),
        );
        test_span(float_lit.span());
        assert_eq!("123.456", float_lit.repr());
        test_token_kind!(float_lit, ItemKind::FloatLiteral, tkn, {
            assert_approx_eq!(123.456, tkn.value());
        });
    }

    #[test]
    fn bool_literal_token_properties_return_correct_values() {
        let bool_lit = Item::new(
            testable_span(),
            ItemKind::BoolLiteral(BoolLiteralKind::new(true)),
        );
        assert_eq!("true", bool_lit.repr());
        test_token_kind!(bool_lit, ItemKind::BoolLiteral, tkn, {
            assert_eq!(true, tkn.value());
        });
    }

    #[test]
    fn newline_token_properties_return_correct_values() {
        let newline_tkn = Item::new(testable_span(), ItemKind::Newline(NewlineKind::new()));
        test_span(newline_tkn.span());
        assert_eq!(NEWLINE_REPR, newline_tkn.repr());
        test_token_kind!(newline_tkn, ItemKind::Newline, tkn, {
            assert_eq!(NEWLINE_REPR, tkn.value());
        });
    }
}
