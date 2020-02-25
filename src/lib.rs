#![doc(html_root_url = "https://docs.rs/trec-text/0.1.0")]

//! Parsing TREC Text format.
//!
//! TREC Text is a text format containing a sequence of records:
//! `<DOC> <DOCNO> 0 </DOCNO> Text body </DOC>`
//!
//! # Examples
//!
//! Typically, document records will be read from files.
//! [`Parser`](struct.Parser.html) can be constructer from any structure that implements
//! [`Read`](https://doc.rust-lang.org/std/io/trait.Read.html),
//! and implements [`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html).
//!
//! Because parsing of a record can fail, either due to IO error or corupted records,
//! the iterator returns elements of `Result<DocumentRecord>`.
//!
//! ```
//! # use trec_text::*;
//! # fn main() -> Result<()> {
//! use std::io::Cursor;
//!
//! let input = r#"
//!<DOC> <DOCNO> 0 </DOCNO> zero </DOC>
//!CORRUPTED <DOCNO> 1 </DOCNO> ten </DOC>
//!<DOC> <DOCNO> 2 </DOCNO> ten nine </DOC>
//!    "#;
//! let mut parser = Parser::new(Cursor::new(input));
//!
//! let document = parser.next().unwrap()?;
//! assert_eq!(String::from_utf8_lossy(document.docno()), "0");
//! assert_eq!(String::from_utf8_lossy(document.content()), " zero ");
//!
//! assert!(parser.next().unwrap().is_err());
//!
//! let document = parser.next().unwrap()?;
//! assert_eq!(String::from_utf8_lossy(document.docno()), "2");
//! assert_eq!(String::from_utf8_lossy(document.content()), " ten nine ");
//!
//! assert!(parser.next().is_none());
//! # Ok(())
//! # }
//! ```

pub use anyhow::Result;

use anyhow::anyhow;
use std::io::{self, Read};
use std::iter::Peekable;

/// TREC Text record data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentRecord {
    docno: Vec<u8>,
    content: Vec<u8>,
}

impl DocumentRecord {
    /// Retrieves `DOCNO` field bytes. Any whitespaces proceeding `<DOCNO>` and preceeding
    /// `</DOCNO>` are trimmed.
    #[must_use]
    pub fn docno(&self) -> &[u8] {
        &self.docno
    }

    /// Retrieves content bytes.
    #[must_use]
    pub fn content(&self) -> &[u8] {
        &self.content
    }
}

/// TREC Text format parser.
pub struct Parser<B>
where
    B: Iterator<Item = io::Result<u8>>,
{
    bytes: Peekable<B>,
    in_progress: bool,
}

impl<R: Read> Parser<io::Bytes<R>> {
    /// Consumes the reader and returns a new TREC Text parser starting at the beginning.
    pub fn new(reader: R) -> Self {
        Self {
            bytes: reader.bytes().peekable(),
            in_progress: false,
        }
    }
}

impl<B> Parser<B>
where
    B: Iterator<Item = io::Result<u8>>,
{
    /// Returns the underlying iterator of remaining bytes.
    pub fn into_bytes(self) -> impl Iterator<Item = Result<u8>> {
        self.bytes.map(|elem| elem.map_err(anyhow::Error::new))
    }

    fn consume_tag_discarding_prefix(&mut self, tag: &str) -> Result<()> {
        let pattern: Vec<_> = tag.bytes().collect();
        let mut pos = 0;
        for byte in &mut self.bytes {
            pos = byte.map(|b| if pattern[pos] == b { pos + 1 } else { 0 })?;
            if pos == pattern.len() {
                return Ok(());
            }
        }
        Err(anyhow!("Unexpected EOF"))
    }

    fn skip_whitespaces(&mut self) -> Result<()> {
        while let Some(byte) = self.bytes.peek() {
            match byte {
                Ok(byte) => {
                    if !byte.is_ascii_whitespace() {
                        break;
                    }
                }
                Err(err) => {
                    return Err(anyhow!(format!("{}", err)));
                }
            }
            self.bytes.next();
        }
        Ok(())
    }

    fn consume_tag_with_prefix(&mut self, tag: &str) -> Result<Vec<u8>> {
        let pattern: Vec<_> = tag.bytes().collect();
        let mut buf: Vec<u8> = Vec::new();
        let mut pos = 0;
        for byte in &mut self.bytes {
            pos = byte.map(|b| {
                buf.push(b);
                if pattern[pos] == b {
                    pos + 1
                } else {
                    0
                }
            })?;
            if pos == pattern.len() {
                buf.drain(buf.len() - pattern.len()..);
                return Ok(buf);
            }
        }
        Err(anyhow!("Unexpected EOF"))
    }

    fn consume_tag(&mut self, tag: &str) -> Result<()> {
        for byte in tag.bytes() {
            if let Some(b) = self.bytes.next() {
                if b? != byte {
                    return Err(anyhow!(format!("Unable to consume tag: {}", tag)));
                }
            } else {
                return Err(anyhow!("Unexpected EOF"));
            }
        }
        Ok(())
    }

    fn next_document(&mut self) -> Result<DocumentRecord> {
        if self.in_progress {
            self.consume_tag_discarding_prefix("<DOC>")?;
        } else {
            self.in_progress = true;
            self.skip_whitespaces()?;
            self.consume_tag("<DOC>")?;
        }
        self.skip_whitespaces()?;
        self.consume_tag("<DOCNO>")?;
        self.skip_whitespaces()?;
        let mut docno = self.consume_tag_with_prefix("</DOCNO>")?;
        let ws_suffix = docno
            .iter()
            .copied()
            .rev()
            .take_while(u8::is_ascii_whitespace)
            .count();
        docno.drain(docno.len() - ws_suffix..);
        let content = self.consume_tag_with_prefix("</DOC>")?;
        self.skip_whitespaces()?;
        self.in_progress = false;
        Ok(DocumentRecord { docno, content })
    }
}

impl<B> Iterator for Parser<B>
where
    B: Iterator<Item = io::Result<u8>>,
{
    type Item = Result<DocumentRecord>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.bytes.peek().is_none() {
            None
        } else {
            Some(self.next_document())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Cursor;

    fn assert_rest_eq<B>(parser: Parser<B>, expected: &str) -> Result<()>
    where
        B: Iterator<Item = io::Result<u8>> + 'static,
    {
        let rest: Result<Vec<_>> = parser.into_bytes().collect();
        assert_eq!(rest?, expected.bytes().collect::<Vec<_>>());
        Ok(())
    }

    #[test]
    fn test_consume_tag() -> Result<()> {
        let input = "<DOC>";
        let mut parser = Parser::new(Cursor::new(input));
        assert!(parser.consume_tag("<DOC>").is_ok());
        assert_rest_eq(parser, "")
    }

    #[test]
    fn test_consume_tag_fails() -> Result<()> {
        let input = "DOC>";
        let mut parser = Parser::new(Cursor::new(input));
        assert!(parser.consume_tag("<DOC>").is_err());
        assert_rest_eq(parser, "OC>")
    }

    #[test]
    fn test_consume_tag_with_remaining_bytes() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("<DOC>rest"));
        assert!(parser.consume_tag("<DOC>").is_ok());
        assert_rest_eq(parser, "rest")
    }

    #[test]
    fn test_consume_tag_discarding_prefix_no_prefix() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("<DOC>rest"));
        assert!(parser.consume_tag_discarding_prefix("<DOC>").is_ok());
        assert_rest_eq(parser, "rest")
    }

    #[test]
    fn test_consume_tag_discarding_prefix_garbage_prefix() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("xxx dsfa sdaf///<<<>>><DOC>rest"));
        assert!(parser.consume_tag_discarding_prefix("<DOC>").is_ok());
        assert_rest_eq(parser, "rest")
    }

    #[test]
    fn test_consume_tag_discarding_prefix_no_matching_tag() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("xxx dsfa sdaf///<<<>>>"));
        assert!(parser.consume_tag_discarding_prefix("<DOC>").is_err());
        Ok(())
    }

    #[test]
    fn test_consume_tag_with_prefix_no_prefix() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("</DOC>rest"));
        assert!(parser.consume_tag_with_prefix("</DOC>").is_ok());
        assert_rest_eq(parser, "rest")
    }

    #[test]
    fn test_consume_tag_with_prefix_content() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("xxx dsfa sdaf///<<<>>></DOC>rest"));
        assert_eq!(
            parser.consume_tag_with_prefix("</DOC>").unwrap(),
            "xxx dsfa sdaf///<<<>>>".bytes().collect::<Vec<_>>()
        );
        assert_rest_eq(parser, "rest")
    }

    #[test]
    fn test_consume_tag_with_prefix_no_matching_tag() -> Result<()> {
        let mut parser = Parser::new(Cursor::new("xxx dsfa sdaf///<<<>>>"));
        assert!(parser.consume_tag_with_prefix("<DOC>").is_err());
        Ok(())
    }

    #[test]
    fn test_next_document() -> Result<()> {
        let input = r#"
<DOC> <DOCNO> 0 </DOCNO> zero </DOC>
<DOC> <DOCNO> 1 </DOCNO> ten </DOC>
<DOC> <DOCNO> 2 </DOCNO> ten nine </DOC>
    "#;
        let mut parser = Parser::new(Cursor::new(input));

        let document = parser.next_document()?;
        assert_eq!(String::from_utf8_lossy(document.docno()), "0");
        assert_eq!(String::from_utf8_lossy(document.content()), " zero ");

        let document = parser.next_document()?;
        assert_eq!(String::from_utf8_lossy(document.docno()), "1");
        assert_eq!(String::from_utf8_lossy(document.content()), " ten ");

        let document = parser.next_document()?;
        assert_eq!(String::from_utf8_lossy(document.docno()), "2");
        assert_eq!(String::from_utf8_lossy(document.content()), " ten nine ");

        Ok(())
    }

    #[test]
    fn test_iter_documents() -> Result<()> {
        let input = r#"
<DOC> <DOCNO> 0 </DOCNO> zero </DOC>
CORRUPTED <DOCNO> 1 </DOCNO> ten </DOC>
<DOC> <DOCNO> 2 </DOCNO> ten nine </DOC>
    "#;
        let mut parser = Parser::new(Cursor::new(input));

        let document = parser.next().unwrap()?;
        assert_eq!(String::from_utf8_lossy(document.docno()), "0");
        assert_eq!(String::from_utf8_lossy(document.content()), " zero ");

        assert!(parser.next().unwrap().is_err());
        assert!(parser.in_progress);

        let document = parser.next().unwrap()?;
        assert_eq!(String::from_utf8_lossy(document.docno()), "2");
        assert_eq!(String::from_utf8_lossy(document.content()), " ten nine ");

        assert!(parser.next().is_none());

        Ok(())
    }
    #[test]
    fn test_parse_jassjr_example() -> io::Result<()> {
        let input = r#"
<DOC> <DOCNO> 0 </DOCNO> zero </DOC>
<DOC> <DOCNO> 1 </DOCNO> ten </DOC>
<DOC> <DOCNO> 2 </DOCNO> ten nine </DOC>

<DOC> <DOCNO> 3 </DOCNO> ten nine eight </DOC>
<DOC>
<DOCNO> 4 </DOCNO>

ten nine eight seven

</DOC>

<DOC> <DOCNO> 5 </DOCNO> ten nine eight seven six </DOC>
<DOC> <DOCNO> 6 </DOCNO> ten nine eight seven six five </DOC>
<DOC> <DOCNO> 7 </DOCNO> ten nine eight seven six five four </DOC>
<DOC> <DOCNO> 8 </DOCNO> ten nine eight seven six five four three </DOC>
<DOC> <DOCNO> 9 </DOCNO> ten nine eight seven six five four three two </DOC>
<DOC> <DOCNO> 10 </DOCNO> ten nine eight seven six five four three two one </DOC>
                "#;
        let documents: Result<Vec<_>> = Parser::new(Cursor::new(input)).collect();
        assert!(documents.is_ok());
        let documents: Vec<_> = documents
            .unwrap()
            .into_iter()
            .map(|doc| {
                (
                    String::from_utf8_lossy(doc.docno()).trim().to_string(),
                    String::from_utf8_lossy(doc.content()).trim().to_string(),
                )
            })
            .collect();
        assert_eq!(
            documents,
            vec![
                (String::from("0"), String::from("zero")),
                (String::from("1"), String::from("ten")),
                (String::from("2"), String::from("ten nine")),
                (String::from("3"), String::from("ten nine eight")),
                (String::from("4"), String::from("ten nine eight seven")),
                (String::from("5"), String::from("ten nine eight seven six")),
                (
                    String::from("6"),
                    String::from("ten nine eight seven six five")
                ),
                (
                    String::from("7"),
                    String::from("ten nine eight seven six five four")
                ),
                (
                    String::from("8"),
                    String::from("ten nine eight seven six five four three")
                ),
                (
                    String::from("9"),
                    String::from("ten nine eight seven six five four three two")
                ),
                (
                    String::from("10"),
                    String::from("ten nine eight seven six five four three two one")
                ),
            ]
        );
        Ok(())
    }
}
