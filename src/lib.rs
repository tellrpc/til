// pub mod lexer;
// pub mod source;
// pub mod token;

mod source_cluster {
    use std::rc::Rc;

    const ALPHA_MASK: u8 = 1;
    const ALPHANUMERIC_MASK: u8 = 1 << 1;
    const DIGIT_MASK: u8 = 1 << 2;
    const LOWERCASE_MASK: u8 = 1 << 3;
    const UPPERCASE_MASK: u8 = 1 << 4;
    const WHITESPACE_MASK: u8 = 1 << 5;

    #[derive(Clone)]
    pub struct SourceCluster {
        grapheme_cluster: Rc<String>,
        unicode_characteristics: u8,
    }

    impl SourceCluster {
        fn new(source: String) -> SourceCluster {
            let unicode_characteristics: u8 = source.chars().take(1).fold(0u8, |mut acc, c|{
                if c.is_alphabetic() {acc = acc | ALPHA_MASK};
                if c.is_alphanumeric() {acc = acc | ALPHANUMERIC_MASK};
                if c.is_digit(10) {acc = acc | DIGIT_MASK};
                if c.is_lowercase() {acc = acc | LOWERCASE_MASK};
                if c.is_uppercase() {acc = acc | UPPERCASE_MASK};
                if c.is_whitespace() {acc = acc | WHITESPACE_MASK};
                acc
            });

            SourceCluster{
                grapheme_cluster: Rc::new(source),
                unicode_characteristics,
            }
        }

        fn test_characteristic(&self, mask: u8) -> bool {
            self.unicode_characteristics & mask != 0
        }

        pub fn is_alphabetic(&self) -> bool {
            self.test_characteristic(ALPHA_MASK)
        }

        pub fn is_alphanumeric(&self) -> bool {
            self.test_characteristic(ALPHANUMERIC_MASK)
        }

        pub fn is_base10_digit(&self) -> bool {
            self.test_characteristic(DIGIT_MASK)
        }

        pub fn is_lowercase(&self) -> bool {
            self.test_characteristic(LOWERCASE_MASK)
        }

        pub fn is_uppercase(&self) -> bool {
            self.test_characteristic(UPPERCASE_MASK)
        }

        pub fn is_whitespace(&self) -> bool {
            self.test_characteristic(WHITESPACE_MASK)
        }
    }

    #[cfg(test)]
    mod tests {
        use std::error::Error;
        use super::SourceCluster;

        fn test_cluster(source: &str) -> SourceCluster {
            SourceCluster::new(source.to_string())
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
            assert!(!test_cluster("a").is_whitespace())
        }
    }

}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
