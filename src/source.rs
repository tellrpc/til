// use std::error;
// use std::fmt;
// use std::fs;
// use std::io;
// use std::fmt::Formatter;
//
// /// An error raised when reading data into a File
// #[derive(Debug)]
// pub struct Error(String);
//
// impl fmt::Display for Error {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "FileError: {}", self.0)
//     }
// }
//
// impl error::Error for Error {}
//
// impl From<io::Error> for Error {
//     fn from(e: io::Error) -> Self {
//         Error(format!("cannot read file: {}", e.to_string()))
//     }
// }
//
// pub type Result<T> = std::result::Result<T, Error>;
//
// /// Trait for any source of til code
// trait Source {
//     fn path(&self) -> &str;
//     fn contents(&self) -> Result<String>;
// }
//
// /// FileSource is a file backed Source
// #[derive(Debug)]
// pub struct FileSource {
//     path: String,
// }
//
// impl FileSource {
//     pub fn new(path: String) -> FileSource {
//         FileSource {
//             path
//         }
//     }
// }
//
// impl Source for FileSource {
//     fn path(&self) -> &str {
//         &self.path
//     }
//
//     fn contents(&self) -> Result<String> {
//         let contents = fs::read_to_string(&self.path)?;
//         Ok(contents)
//     }
// }
//
// #[derive(Debug)]
// pub struct StringSource {
//     path: String,
//     contents: String,
// }
//
// impl StringSource {
//     pub fn new(path: String, contents: String) -> StringSource {
//         StringSource { path, contents }
//     }
// }
//
// impl Source for StringSource {
//     fn path(&self) -> &str {
//         &self.path
//     }
//
//     fn contents(&self) -> Result<String> {
//         Ok(self.contents.clone())
//     }
// }
//
// #[cfg(test)]
// mod test {
//     use super::*;
//     use std::result;
//
//     const TEST_PATH: &str = "the/file/path";
//     const TEST_SOURCE: &str = "The file source";
//
//     #[test]
//     fn test_file_source_path() {
//         let f = FileSource::new("src/example.til".to_string());
//         assert_eq!("src/example.til", f.path())
//     }
//
//     #[test]
//     fn test_file_source_contents() -> result::Result<(), Error> {
//         let contents = fs::read_to_string("src/example.til")?;
//         let f = FileSource::new("src/example.til".to_string());
//         assert_eq!(contents, f.contents()?);
//         Ok(())
//     }
//
//     #[test]
//     fn test_string_source_path() {
//         let s = StringSource::new(TEST_PATH.to_string(), TEST_SOURCE.to_string());
//         assert_eq!(TEST_PATH, s.path());
//     }
//
//     #[test]
//     fn test_string_source_contents() -> result::Result<(), Error> {
//         let s = StringSource::new(TEST_PATH.to_string(), TEST_SOURCE.to_string());
//         assert_eq!(TEST_SOURCE.to_string(), s.contents()?);
//         Ok(())
//     }
// }