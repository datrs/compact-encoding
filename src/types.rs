//! Basic types of compact_encoding.
use std::fmt;

pub(crate) const U16_SIGNIFIER: u8 = 0xfd;
pub(crate) const U32_SIGNIFIER: u8 = 0xfe;
pub(crate) const U64_SIGNIFIER: u8 = 0xff;

/// Specific type [EncodingError]
#[derive(fmt::Debug, Clone, PartialEq)]
pub enum EncodingErrorKind {
    /// Encoding or decoding did not stay between [State] `start` and `end`.
    OutOfBounds,
    /// Buffer data overflowed type during encoding or decoding.
    Overflow,
    /// Buffer contained invalid data during decoding.
    InvalidData,
}

/// Encoding/decoding error.
#[derive(fmt::Debug, Clone, PartialEq)]
pub struct EncodingError {
    /// Specific type of error
    pub kind: EncodingErrorKind,
    /// Message for the error
    pub message: String,
}

impl std::error::Error for EncodingError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl EncodingError {
    /// Create EncodingError
    pub fn new(kind: EncodingErrorKind, message: &str) -> Self {
        Self {
            kind,
            message: message.to_string(),
        }
    }
    /// Helper function for making an overflow error
    pub fn overflow(message: &str) -> Self {
        Self {
            kind: EncodingErrorKind::Overflow,
            message: message.to_string(),
        }
    }
    /// Helper function for making an out of bounds error
    pub fn out_of_bounds(message: &str) -> Self {
        Self {
            kind: EncodingErrorKind::OutOfBounds,
            message: message.to_string(),
        }
    }
    /// Helper function for making an invalid data error
    pub fn invalid_data(message: &str) -> Self {
        Self {
            kind: EncodingErrorKind::InvalidData,
            message: message.to_string(),
        }
    }
}

impl fmt::Display for EncodingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.kind {
            EncodingErrorKind::OutOfBounds => "Compact encoding failed, out of bounds",
            EncodingErrorKind::Overflow => "Compact encoding failed, overflow",
            EncodingErrorKind::InvalidData => "Compact encoding failed, invalid data",
        };
        write!(f, "{}: {}", prefix, self.message)
    }
}

impl From<EncodingError> for std::io::Error {
    fn from(e: EncodingError) -> Self {
        match e.kind {
            EncodingErrorKind::InvalidData => {
                std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{e}"))
            }
            _ => std::io::Error::new(std::io::ErrorKind::Other, format!("{e}")),
        }
    }
}
