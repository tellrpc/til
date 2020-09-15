// use std::iter;
// use unicode_segmentation::{Graphemes, UnicodeSegmentation};
//
// /// A single GraphemeCluster from a SourceStream
// struct GraphemeCluster<'a> {
//     repr: &'a str,
//     chars: Vec<char>,
//     line: u64,
//     column: u64,
// }
//
// impl<'a> GraphemeCluster<'_> {
//     fn new(repr: &str, line: u64, column: u64) -> GraphemeCluster {
//         GraphemeCluster {
//             repr,
//             chars: repr.chars().collect::<Vec<char>>(),
//             line,
//             column,
//         }
//     }
//
//     fn test_cluster_property<T>(&self, test: T) -> bool where T: Fn(&char) -> bool {
//         self.chars.len() > 0 && test(&self.chars[0])
//     }
//
//     /// Is the GraphemeCluster alphabetic
//     pub fn is_alphabetic(&self) -> bool {
//         self.test_cluster_property(|c| { c.is_alphabetic() })
//     }
//
//     /// Is the GraphemeCluster alphanumeric
//     pub fn is_alphanumeric(&self) -> bool {
//         self.test_cluster_property(|c| { c.is_alphanumeric() })
//     }
//
//     /// Is the GraphemeCluster a digit
//     pub fn is_digit(&self) -> bool {
//         self.test_cluster_property(|c| { c.is_digit(10) })
//     }
//
//     /// Is the GraphemeCluster whitespace
//     pub fn is_whitespace(&self) -> bool {
//         self.test_cluster_property(|c| { c.is_whitespace() })
//     }
//
//     /// Is the GraphemeCluster a newline (the GraphemeClusters iterator normalises all newline variations to \n)
//     pub fn is_newline(&self) -> bool {
//         self.test_cluster_property(|c| *c == '\n')
//     }
// }
//
// /// Iterator returning the GraphemeClusters in the source str
// struct GraphemeClusters<'a> {
//     graphemes: iter::Peekable<Graphemes<'a>>,
//     line: u64,
//     column: u64,
// }
//
// impl<'a> GraphemeClusters<'_> {
//     pub fn new(src: &'a str) -> GraphemeClusters {
//         GraphemeClusters{
//             graphemes: src.graphemes(true).peekable(),
//             line: 1,
//             column: 1
//         }
//     }
//
//     fn next_cluster(&mut self, gc: &'a str) -> GraphemeCluster<'a> {
//         let cluster = GraphemeCluster::new(gc, self.line, self.column);
//         self.column += 1;
//         return cluster;
//
//     }
//
//     fn next_cluster_advancing_line(&mut self, gc: &'a str) -> GraphemeCluster<'a> {
//         let cluster = GraphemeCluster::new(gc, self.line, self.column);
//         self.line += 1;
//         self.column = 1;
//         return cluster;
//     }
// }
//
// impl<'a> Iterator for GraphemeClusters <'a> {
//     type Item = GraphemeCluster<'a>;
//
//     fn next(&mut self) -> Option<Self::Item> {
//         if let Some(gc) = self.graphemes.next() {
//             // convert solitary \r to \n, convert \r\n to \n
//             if gc == "\r" || gc == "\r\n" || gc == "\n" {
//                 Some(self.next_cluster_advancing_line("\n"))
//             } else {
//                 Some(self.next_cluster(gc))
//             }
//         } else {
//             None
//         }
//     }
// }
//
// #[cfg(test)]
// mod test {
//     use super::*;
//
//     #[test]
//     fn test_is_alphabetic() {
//         assert!(GraphemeCluster::new("a", 1, 1).is_alphabetic());
//         assert!(GraphemeCluster::new("ä", 1, 1).is_alphabetic());
//         assert!(!GraphemeCluster::new("1", 1, 1).is_alphabetic());
//         assert!(!GraphemeCluster::new("!", 1, 1).is_alphabetic());
//     }
//
//     #[test]
//     fn test_is_alphanumeric() {
//         assert!(GraphemeCluster::new("a", 1, 1).is_alphanumeric());
//         assert!(GraphemeCluster::new("ä", 1, 1).is_alphanumeric());
//         assert!(GraphemeCluster::new("1", 1, 1).is_alphanumeric());
//         assert!(!GraphemeCluster::new("!", 1, 1).is_alphanumeric());
//     }
//
//     #[test]
//     fn test_is_digit() {
//         assert!(GraphemeCluster::new("0", 1, 1).is_digit());
//         assert!(GraphemeCluster::new("1", 1, 1).is_digit());
//         assert!(GraphemeCluster::new("9", 1, 1).is_digit());
//         assert!(!GraphemeCluster::new("a", 1, 1).is_digit());
//         assert!(!GraphemeCluster::new("Ä", 1, 1).is_digit());
//     }
//
//     #[test]
//     fn test_is_whitespace() {
//         assert!(GraphemeCluster::new(" ", 1, 1).is_whitespace());
//         assert!(GraphemeCluster::new("\n", 1, 1).is_whitespace());
//         assert!(GraphemeCluster::new("\t", 1, 1).is_whitespace());
//         assert!(!GraphemeCluster::new("a", 1, 1).is_whitespace());
//         assert!(!GraphemeCluster::new("1", 1, 1).is_whitespace());
//     }
//
//     #[test]
//     fn test_is_newline() {
//         assert!(GraphemeCluster::new("\n", 1, 1).is_newline());
//         assert!(!GraphemeCluster::new("1", 1, 1).is_newline());
//     }
//
//     #[test]
//     fn test_grapheme_clusters_crlf() {
//         let gcs = GraphemeClusters::new("\r\n").collect::<Vec<GraphemeCluster>>();
//         assert_eq!(1, gcs.len());
//         assert!(gcs[0].repr == "\n");
//     }
//
//     #[test]
//     fn test_grapheme_clusters_cr() {
//         let gcs = GraphemeClusters::new("\r").collect::<Vec<GraphemeCluster>>();
//         assert_eq!(1, gcs.len());
//         assert!(gcs[0].repr == "\n");
//     }
//
//     #[test]
//     fn test_grapheme_clusters_lf() {
//         let gcs = GraphemeClusters::new("\n").collect::<Vec<GraphemeCluster>>();
//         assert_eq!(1, gcs.len());
//         assert!(gcs[0].repr == "\n");
//     }
//
//     #[test]
//     fn test_grapheme_clusters_line_advance() {
//         let gcs = GraphemeClusters::new("abc\nd").collect::<Vec<GraphemeCluster>>();
//
//         // The a is at line 1, column 1
//         assert_eq!("a", gcs[0].repr);
//         assert_eq!(1, gcs[0].line);
//         assert_eq!(1, gcs[0].column);
//
//         // The c is at line 1, column 3
//         assert_eq!("c", gcs[2].repr);
//         assert_eq!(1, gcs[2].line);
//         assert_eq!(3, gcs[2].column);
//
//         // The newline is at line 1, column 4
//         assert_eq!("\n", gcs[3].repr);
//         assert_eq!(1, gcs[3].line);
//         assert_eq!(4, gcs[3].column);
//
//         // The d is at line 2, column 1
//         assert_eq!("d", gcs[4].repr);
//         assert_eq!(2, gcs[4].line);
//         assert_eq!(1, gcs[4].column);
//     }
// }