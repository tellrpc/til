// use std::fmt;
// use std::sync;
//
// use crate::source;
//
// /// Type represents the range of token types
// #[derive(Debug, Copy, Clone, PartialEq)]
// pub enum Type {
//     // Literal Types
//     StringLiteral,
//     IntLiteral,
//     FloatLiteral,
//     BoolLiteral,
//     // Comment Types
//     DocComment,
//     // Punctuation
//     Bang,
//     Colon,
//     QMark,
//     LBrace,
//     RBrace,
//     LBracket,
//     RBracket,
//     LParen,
//     RParen,
//     At,
//     // Keywords
//     MessageKeyword,
//     ListKeyword,
//     MapKeyword,
//     ServiceKeyword,
//     FloatKeyword,
//     IntKeyword,
//     BoolKeyword,
//     StringKeyword,
//     TimeKeyword,
//     //Whitespace
//     LineFeed,
//     EOF,
// }
//
// impl fmt::Display for Type {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{:?}", self)
//     }
// }
//
// /// A Token extracted from a text stream by the lexer.
// /// Tokens are immutable.
// pub struct Token {
//     token_type: Type,
//     file: sync::Arc<source::File>,
//     line: u64,
//     column: u64,
//     repr: String,
// }
//
// impl Token {
//     /// Construct a new token
//     pub fn new(token_type: Type, file: sync::Arc<source::File>, line: u64, column: u64, repr: String) -> Token {
//         Token {
//             token_type,
//             file,
//             line,
//             column,
//             repr,
//         }
//     }
//
//     pub fn token_type(&self) -> Type {
//         self.token_type
//     }
//
//     pub fn file(&self) -> sync::Arc<source::File> {
//         // file is a sync::Arc so clone it to give const access to the source::File
//         self.file.clone()
//     }
//
//     pub fn line(&self) -> u64 {
//         self.line
//     }
//
//     pub fn column(&self) -> u64 {
//         self.column
//     }
//
//     pub fn repr(&self) -> &str {
//         &self.repr[..]
//     }
// }
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//
//     #[test]
//     fn test_type_string() {
//         assert_eq!(Type::StringKeyword.to_string(), "StringKeyword")
//     }
//
//     #[test]
//     fn test_token_new() -> Result<(), Box<dyn std::error::Error>> {
//         let file = sync::Arc::new(source::File::new_from_string("contents".to_string(), "filename".to_string())?);
//         let tkn = Token::new(Type::EOF, file.clone(), 2, 3, "\n".to_string());
//         assert_eq!(tkn.token_type(), Type::EOF, "token_type() does not match");
//         assert_eq!(tkn.file().path(), "filename", "file() does not match");
//         assert_eq!(tkn.line(), 2, "line() does not match");
//         assert_eq!(tkn.column(), 3, "column() does not match");
//         assert_eq!(tkn.repr(), "\n", "repr does not match");
//         Ok(())
//     }
// }