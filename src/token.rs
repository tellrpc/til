use paste::paste;
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
            ItemKind::Bang(ref knd) => knd.repr(),
            ItemKind::Colon(ref knd) => knd.repr(),
            ItemKind::QMark(ref knd) => knd.repr(),
            ItemKind::LBrace(ref knd) => knd.repr(),
            ItemKind::RBrace(ref knd) => knd.repr(),
            ItemKind::LBracket(ref knd) => knd.repr(),
            ItemKind::RBracket(ref knd) => knd.repr(),
            ItemKind::LParen(ref knd) => knd.repr(),
            ItemKind::RParen(ref knd) => knd.repr(),
            ItemKind::At(ref knd) => knd.repr(),
            ItemKind::MessageKeyword(ref knd) => knd.repr(),
            ItemKind::ListKeyword(ref knd) => knd.repr(),
            ItemKind::MapKeyword(ref knd) => knd.repr(),
            ItemKind::ServiceKeyword(ref knd) => knd.repr(),
            ItemKind::FloatKeyword(ref knd) => knd.repr(),
            ItemKind::IntKeyword(ref knd) => knd.repr(),
            ItemKind::BoolKeyword(ref knd) => knd.repr(),
            ItemKind::StringKeyword(ref knd) => knd.repr(),
            ItemKind::TimeKeyword(ref knd) => knd.repr(),
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

macro_rules! const_kind_decl {
    ($const_name:ident, $kind_name:ident, $const_val:literal) => {
        pub const $const_name: &str = $const_val;

        paste! {
            #[doc = "Kind descriptor for a " $kind_name "."]
            #[derive(Debug)]
            pub struct $kind_name {
                value: &'static str,
            }
        }

        impl $kind_name {
            pub fn value(&self) -> &str {
                self.value
            }

            pub fn repr(&self) -> String {
                self.value().to_string()
            }
        }

        impl $kind_name {
            pub fn new() -> $kind_name {
                $kind_name { value: $const_name }
            }
        }
    };
}

const_kind_decl!(NEWLINE_REPR, NewlineKind, "\n");
const_kind_decl!(BANG_REPR, BangKind, "!");
const_kind_decl!(COLON_REPR, ColonKind, ":");
const_kind_decl!(QMARK_REPR, QMarkKind, "?");
const_kind_decl!(LBRACE_REPR, LBraceKind, "{");
const_kind_decl!(RBRACE_REPR, RBraceKind, "}");
const_kind_decl!(LBRACKET_REPR, LBracketKind, "[");
const_kind_decl!(RBRACKET_REPR, RBracketKind, "]");
const_kind_decl!(LPAREN_REPR, LParenKind, "(");
const_kind_decl!(RPAREN_REPR, RParenKind, ")");
const_kind_decl!(AT_REPR, AtKind, "@");
const_kind_decl!(MESSAGE_KW_REPR, MessageKeywordKind, "message");
const_kind_decl!(LIST_KW_REPR, ListKeywordKind, "list");
const_kind_decl!(MAP_KW_REPR, MapKeywordKind, "map");
const_kind_decl!(SERVICE_KW_REPR, ServiceKeywordKind, "service");
const_kind_decl!(FLOAT_KW_REPR, FloatKeywordKind, "float");
const_kind_decl!(INT_KW_REPR, IntKeywordKind, "int");
const_kind_decl!(BOOL_KW_REPR, BoolKeywordKind, "bool");
const_kind_decl!(STRING_KW_REPR, StringKeywordKind, "string");
const_kind_decl!(TIME_KW_REPR, TimeKeywordKind, "time");

#[derive(Debug)]
pub enum ItemKind {
    // Literal Types
    StringLiteral(StringLiteralKind),
    IntLiteral(IntLiteralKind),
    FloatLiteral(FloatLiteralKind),
    BoolLiteral(BoolLiteralKind),
    // Comment Types
    // DocComment,
    // Punctuation
    Bang(BangKind),
    Colon(ColonKind),
    QMark(QMarkKind),
    LBrace(LBraceKind),
    RBrace(RBraceKind),
    LBracket(LBracketKind),
    RBracket(RBracketKind),
    LParen(LParenKind),
    RParen(RParenKind),
    At(AtKind),
    // Keywords
    MessageKeyword(MessageKeywordKind),
    ListKeyword(ListKeywordKind),
    MapKeyword(MapKeywordKind),
    ServiceKeyword(ServiceKeywordKind),
    FloatKeyword(FloatKeywordKind),
    IntKeyword(IntKeywordKind),
    BoolKeyword(BoolKeywordKind),
    StringKeyword(StringKeywordKind),
    TimeKeyword(TimeKeywordKind),
    //Whitespace
    Newline(NewlineKind),
    // EOF,
}

#[cfg(test)]
mod test {
    use super::*;
    use assert_approx_eq::assert_approx_eq;
    use paste::paste;

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

    macro_rules! test_const_kind {
        ($kind_enum:ident, $kind_name:ident, $kind_repr:ident) => {
            paste! {
                #[test]
                fn [<$kind_name:lower _properties_return_correct_values>]() {
                    let tkn = Item::new(testable_span(), ItemKind::$kind_enum($kind_name::new()));
                    test_span(tkn.span());
                    assert_eq!($kind_repr, tkn.repr());
                    test_token_kind!(tkn, ItemKind::$kind_enum, knd, {
                        assert_eq!($kind_repr, knd.value());
                    });
                }
            }
        };
    }

    test_const_kind!(Newline, NewlineKind, NEWLINE_REPR);
    test_const_kind!(Bang, BangKind, BANG_REPR);
    test_const_kind!(Colon, ColonKind, COLON_REPR);
    test_const_kind!(QMark, QMarkKind, QMARK_REPR);
    test_const_kind!(LBrace, LBraceKind, LBRACE_REPR);
    test_const_kind!(RBrace, RBraceKind, RBRACE_REPR);
    test_const_kind!(LBracket, LBracketKind, LBRACKET_REPR);
    test_const_kind!(RBracket, RBracketKind, RBRACKET_REPR);
    test_const_kind!(LParen, LParenKind, LPAREN_REPR);
    test_const_kind!(RParen, RParenKind, RPAREN_REPR);
    test_const_kind!(At, AtKind, AT_REPR);
    test_const_kind!(MessageKeyword, MessageKeywordKind, MESSAGE_KW_REPR);
    test_const_kind!(ListKeyword, ListKeywordKind, LIST_KW_REPR);
    test_const_kind!(MapKeyword, MapKeywordKind, MAP_KW_REPR);
    test_const_kind!(ServiceKeyword, ServiceKeywordKind, SERVICE_KW_REPR);
    test_const_kind!(FloatKeyword, FloatKeywordKind, FLOAT_KW_REPR);
    test_const_kind!(IntKeyword, IntKeywordKind, INT_KW_REPR);
    test_const_kind!(BoolKeyword, BoolKeywordKind, BOOL_KW_REPR);
    test_const_kind!(StringKeyword, StringKeywordKind, STRING_KW_REPR);
    test_const_kind!(TimeKeyword, TimeKeywordKind, TIME_KW_REPR);

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

    // #[test]
    // fn newline_token_properties_return_correct_values() {
    //     let newline_tkn = Item::new(testable_span(), ItemKind::Newline(NewlineKind::new()));
    //     test_span(newline_tkn.span());
    //     assert_eq!(NEWLINE_REPR, newline_tkn.repr());
    //     test_token_kind!(newline_tkn, ItemKind::Newline, tkn, {
    //         assert_eq!(NEWLINE_REPR, tkn.value());
    //     });
    // }
}
