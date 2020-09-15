// use std::sync;
//
// use unicode_segmentation as useg;
// use useg::UnicodeSegmentation;
// use crate::source;
// use crate::token;
// use std::iter;

mod grapheme_clusters;

// pub struct Error(String);
//
// pub type Result = std::result::Result<token::Token, Error>;
//
// pub struct Lexer<'a> {
//     file: sync::Arc<source::File>,
//     chars: iter::Peekable<useg::Graphemes<'a>>,
//     line: u64,
//     column: u64,
// }
//
// struct Char<'a> {
//     pub ch: &'a str,
//     pub ln: u64,
//     pub col: u64,
// }
//
// fn unexpected_char_error(c: Char) -> Error {
//     Error(format!("Unexpected character {} at line: {} column {}", c.ch, c.ln, c.col))
// }
//
// impl<'a> Lexer<'a> {
//     pub fn new(file: sync::Arc<source::File>, contents: &'a str) -> Lexer<'a> {
//         Lexer {
//             file,
//             chars: UnicodeSegmentation::graphemes(contents, true).peekable(),
//             line: 1,
//             column: 1,
//         }
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
//     fn next_char(&mut self) -> Option<Char> {
//         if let Some(c) = self.chars.next() {
//             let nxt = Char { ch: c, ln: self.line, col: self.column };
//             if c == "\n" {
//                 self.line += 1;
//                 self.column = 1;
//             }
//             Some(nxt)
//         } else {
//             None
//         }
//     }
//
//     // TODO: Can probably use match self.chars.peek better than if let because can match None and Some("/") etc
//     // fn consume_line(&mut self) {
//     //     while let Some(peek) = self.chars.peek() {
//     //         if peek == "/n" {
//     //             self.next_char()
//     //             break
//     //         }
//     //         if peek == "/r" {
//     //             self.consume_line_feed()
//     //         }
//     //         self.next_char();
//     //     }
//     // }
//     //
//     // TODO: Can probably use match self.chars.peek better than if let because can match None and Some("/") etc
//     // fn consume_line_feeds(&mut self) {
//     //     if let Some(peek) = self.chars.peek() {
//     //         if peek == "\n" {
//     //             self.next_char();
//     //         }
//     //     }
//     // }
//
//     // TODO: Can probably use match self.chars.peek better than if let because can match None and Some("/") etc
//     // fn maybe_doc_comment_tkn(&mut self, c: Char, f: sync::Arc<source::File>) -> Option<Result> {
//     //     let mut buffer: String = c.ch.to_string();
//     //     if let Some(peek) = self.chars.peek() {
//     //         if peek == "/" {
//     //             buffer += self.next_char().unwrap().ch;
//     //             return if let Some(peek) = self.chars.peek() {
//     //                 if peek == "/" {
//     //                     // this is a doc comment. read it to the buffer and return it
//     //                     while let Some(peek) = self.chars.peek() {
//     //                         if peek == "\n" {
//     //                             self.next_char();
//     //                             break;
//     //                         } else if peak == "\r" {
//     //                             self.next_char();
//     //                             self.consume_line_feed();
//     //                             break;
//     //                         }
//     //                         buffer += self.next_char().unwrap().ch;
//     //                     }
//     //                     Some(Ok(token::Token::new(token::Type::DocComment, f, c.ln, c.col, buffer)))
//     //                 } else {
//     //                     // This is an ordinary comment. Consume the rest of the line and return None
//     //                     self.consume_line();
//     //                     None
//     //                 }
//     //             } else {
//     //                 // The file is ended
//     //                 None
//     //             }
//     //         }
//     //         else {
//     //             let next = self.next_char().unwrap();
//     //             return Some(Err(unexpected_char_error(next)))
//     //         }
//     //     }
//     //     None
//     // }
// }
//
// fn bang_tkn(c: Char, f: sync::Arc<source::File>) -> Option<Result> {
//     Some(Ok(token::Token::new(token::Type::Bang, f, c.ln, c.col, c.ch.to_string())))
// }
//
//
// impl Iterator for Lexer<'_> {
//     type Item = Result;
//
//     fn next(&mut self) -> Option<Self::Item> {
//         let file = self.file.clone();
//         while let Some(nxt) = self.next_char() {
//             match nxt.ch {
//                 "!" => return bang_tkn(nxt, file),
//                 _ => return None // TODO Nope!
//             }
//         }
//         None
//     }
// }
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use std::error;
//     use std::result;
//     use std::sync;
//
//     // fn create_file(contents: &str, path: &str) -> sync::Arc<source::File> {
//     //     sync::Arc::new(source::File::new_from_string(contents.to_string(), path.to_string()).expect("error creating file"))
//     // }
//     //
//     // fn create_lexer(file: &sync::Arc<source::File>) -> Lexer {
//     //     Lexer::new(file.clone(), file.contents())
//     // }
//
//     // #[test]
//     // fn test_new() {
//     //     let f = create_file("contents", "the/file/path");
//     //     let l = create_lexer(&f);
//     //     assert_eq!(l.line(), 1, "l.line() is incorrect");
//     //     assert_eq!(l.column(), 1, "l.column() is incorrect");
//     // }
//     //
//     // #[test]
//     // fn test_lex_bang() {
//     //     let f = create_file("!", "path");
//     //     let mut l = create_lexer(&f);
//     //     if let Some(Ok(tkn)) = l.next() {
//     //         assert_eq!(tkn.token_type(), token::Type::Bang);
//     //         assert_eq!(tkn.line(), 1);
//     //         assert_eq!(tkn.column(), 1);
//     //     } else {
//     //         assert!(false, "not some ok token")
//     //     }
//     // }
//
//     // fn test_bang()
// }

