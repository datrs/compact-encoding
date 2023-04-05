#![forbid(unsafe_code, missing_docs)]
#![cfg_attr(test, deny(warnings))]
#![doc(test(attr(deny(warnings))))]

//! # Series of compact encoding schemes for building small and fast parsers and serializers
//!
//! Binary compatible with the
//! [original Javascript compact-encoding library](https://github.com/compact-encoding/compact-encoding/).
//!
//! ## Usage
//!
//! ### Basic
//!
//! Using only the types implemented here (replace `unwrap()` with proper
//! handling of [EncodingError]):
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
//!
//! ### Custom
//!
//! If you want to encode your own structs directly, you can do that
//! by implementing [CompactEncoding] yourself (replace `unwrap()` with proper
//! handling of [EncodingError]):
//!
//! ```
//! use compact_encoding::{CompactEncoding, EncodingError, State};
//!
//! #[derive(Debug, PartialEq)]
//! struct MyStruct {
//!     my_flag_1: bool,
//!     my_flag_2: bool,
//!     my_values: Vec<[u8; 32]>,
//! }
//!
//! impl CompactEncoding<MyStruct> for State {
//!     fn preencode(&mut self, value: &MyStruct) -> Result<usize, EncodingError> {
//!         self.add_end(1)?; // flags
//!         if !value.my_values.is_empty() {
//!             self.preencode(&value.my_values)?;
//!         }
//!         Ok(self.end())
//!     }
//!
//!     fn encode(&mut self, value: &MyStruct, buffer: &mut [u8]) -> Result<usize, EncodingError> {
//!         let mut flags: u8 = 0;
//!         if value.my_flag_1 {
//!             flags |= 1;
//!         }
//!         if value.my_flag_2 {
//!             flags |= 2;
//!         }
//!         if !value.my_values.is_empty() {
//!             flags |= 4;
//!         }
//!         self.encode(&flags, buffer)?;
//!         if !value.my_values.is_empty() {
//!             self.encode(&value.my_values, buffer)?;
//!         }
//!         Ok(self.start())
//!     }
//!
//!     fn decode(&mut self, buffer: &[u8]) -> Result<MyStruct, EncodingError> {
//!        let flags: u8 = self.decode(buffer)?;
//!        let my_flag_1: bool = flags & 1 != 0;
//!        let my_flag_2: bool = flags & 2 != 0;
//!        let my_values: Vec<[u8; 32]> = if flags & 4 != 0 {
//!            self.decode(buffer)?
//!        } else {
//!            vec![]
//!        };
//!        Ok(MyStruct {
//!             my_flag_1,
//!             my_flag_2,
//!             my_values
//!        })
//!     }
//! }
//!
//! // Test values
//! let empty = MyStruct {
//!     my_flag_1: false,
//!     my_flag_2: true,
//!     my_values: vec![]
//! };
//! let non_empty = MyStruct {
//!     my_flag_1: true,
//!     my_flag_2: false,
//!     my_values: vec![[1; 32], [2; 32]]
//! };
//!
//! // Start with an empty state
//! let mut enc_state = State::new();
//! enc_state.preencode(&empty).unwrap();
//! enc_state.preencode(&non_empty).unwrap();
//! let mut buffer = enc_state.create_buffer();
//!
//! // With the above use of a flags byte, the empty value encodes to only one byte
//! assert_eq!(buffer.len(), 1 + 1 + 1 + 2 * 32);
//!
//! // Then actually encode the values
//! enc_state.encode(&empty, &mut buffer).unwrap();
//! enc_state.encode(&non_empty, &mut buffer).unwrap();
//!
//! // On the decoding end, create a state from byte buffer
//! let mut dec_state = State::from_buffer(&buffer);
//!
//! // And decode directly to your own struct
//! let empty_dec: MyStruct = dec_state.decode(&buffer).unwrap();
//! let non_empty_dec: MyStruct = dec_state.decode(&buffer).unwrap();
//! assert_eq!(empty_dec, empty);
//! assert_eq!(non_empty_dec, non_empty);
//! ```
//!
//! **NB**: This only works if you don't export your struct out of your crate.
//! If you export the struct, orphan rule will require you to
//! implement a wrapper for [State], e.g. `struct MyState(State);` and implement
//! [CompactEncoding] for the wrapper struct instead.
pub mod generic;
pub mod types;
pub use types::{CompactEncoding, EncodingError, EncodingErrorKind, State};
