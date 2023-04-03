#![forbid(unsafe_code, missing_docs)]
#![cfg_attr(test, deny(warnings))]
#![doc(test(attr(deny(warnings))))]

//! # Series of compact encoding schemes for building small and fast parsers and serializers
//!
//! ## Usage
//!
//! ```
//! use compact_encoding::{CompactEncoding, State};
//!
//! // Start with an empty state
//! let mut enc_state = State::new();
//!
//! let number = 41_u32;
//! let str = "hi".to_string();
//!
//! // Use preencode to figure out how big a buffer is needed
//! enc_state.preencode(&number).unwrap();
//! enc_state.preencode(&str).unwrap();
//!
//! // Create buffer of pre-encoded size
//! let mut buffer = enc_state.create_buffer();
//! assert_eq!(buffer.len(), 1 + 1 + 2);
//!
//! // Then actually encode the values
//! enc_state.encode(&number, &mut buffer).unwrap();
//! enc_state.encode(&str, &mut buffer).unwrap();
//! assert_eq!(buffer.to_vec(), vec![41_u8, 2_u8, b'h', b'i']);
//!
//! // On the decoding end, create a state from byte buffer
//! let mut dec_state = State::from_buffer(&buffer);
//! let number_dec: u32 = dec_state.decode(&buffer).unwrap();
//! let str_dec: String = dec_state.decode(&buffer).unwrap();
//! assert_eq!(number_dec, number);
//! assert_eq!(str_dec, str);
//! ```
pub mod generic;
pub mod types;
pub use types::{CompactEncoding, EncodingError, EncodingErrorKind, State};
