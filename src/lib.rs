#![forbid(unsafe_code, missing_docs)]
#![cfg_attr(test, deny(warnings))]
//! # Series of compact encoding schemes for building small and fast parsers and serializers
//!
//! Binary compatible with the
//! [original JavaScript compact-encoding library](https://github.com/compact-encoding/compact-encoding/).
//!
//! ## Usage
//!
//! The simplest way to encoded and decode a some data is using the [`to_encoded_bytes`] and
//! [`map_decode`] macros:
//! ```
//! use compact_encoding::{map_decode, to_encoded_bytes};
//!
//! let number = 41_u32;
//! let word = "hi";
//!
//! let encoded_buffer = to_encoded_bytes!(number, word);
//! let ((number_dec, word_dec), remaining_buffer) = map_decode!(&encoded_buffer, [u32, String]);
//!
//! assert!(remaining_buffer.is_empty());
//! assert_eq!(number_dec, number);
//! assert_eq!(word_dec, word);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//! ### Manual encoding and decoding
//!
//! When more fine-grained control of encoding and decoding is needed you manually do each step of
//! encoding and decoding like in the following example, where we want to use a fixed width
//! encoding for `number` (instead of the default variable width encoding). It shows how to
//! manually calculate the needed buffer size, create the buffer, encode data, and decode it.
//! ```
//! use compact_encoding::{CompactEncoding, FixedWidthEncoding, FixedWidthU32};
//!
//! let number = 41_u32;
//! let word = "hi";
//!
//! // Use `encoded_size` to figure out how big a buffer should be
//! let size = number.as_fixed_width().encoded_size()? + word.encoded_size()?;
//!
//! // Create a buffer with the calculated size
//! let mut buffer = vec![0; size];
//! assert_eq!(buffer.len(), 4 + 1 + 2);
//!
//! // Then actually encode the values
//! let mut remaining_buffer = number.as_fixed_width().encode(&mut buffer)?;
//! remaining_buffer = word.encode(remaining_buffer)?;
//! assert!(remaining_buffer.is_empty());
//! assert_eq!(buffer.to_vec(), vec![41_u8, 0, 0, 0, 2_u8, b'h', b'i']);
//!
//! // `buffer` now contains all the encoded data, and we can decode from it
//! let (number_dec, remaining_buffer) = FixedWidthU32::decode(&buffer)?;
//! let (word_dec, remaining_buffer) = String::decode(remaining_buffer)?;
//! assert!(remaining_buffer.is_empty());
//! assert_eq!(number_dec, number);
//! assert_eq!(word_dec, word);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ### Implementing CompactEncoding for custom types
//!
//! Here we demonstrate how to implement [`CompactEncoding`] for a custom struct.
//! ```
//! use compact_encoding::{
//!     map_decode, map_encode, sum_encoded_size, to_encoded_bytes, CompactEncoding, EncodingError,
//! };
//!
//! #[derive(Debug, PartialEq)]
//! struct MyStruct {
//!     some_flag: bool,
//!     values: Option<Vec<[u8; 32]>>,
//!     other: String,
//!     stuff: u64,
//! }
//!
//! impl CompactEncoding for MyStruct {
//!     fn encoded_size(&self) -> Result<usize, EncodingError> {
//!         Ok(1 /* flags */ + {
//!              /* handle option values */
//!             if let Some(values) = &self.values  {
//!                 values.encoded_size()?
//!             } else {
//!                 0
//!             }
//!         } + sum_encoded_size!(&self.other, &self.stuff))
//!     }
//!
//!     fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
//!         let mut flags: u8 = 0;
//!         if self.some_flag {
//!             flags |= 1;
//!         }
//!         if self.values.is_some() {
//!             flags |= 2;
//!         }
//!         let mut rest = flags.encode(buffer)?;
//!         if let Some(values) = &self.values {
//!             rest = values.encode(rest)?;
//!         }
//!         Ok(map_encode!(rest, self.other, self.stuff))
//!     }
//!
//!     fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError> {
//!         let (flags, rest) = u8::decode(buffer)?;
//!         let some_flag: bool = flags & 1 != 0;
//!         let (values, rest) = if flags & 2 != 0 {
//!             let (vec, rest) = <Vec<[u8; 32]>>::decode(rest)?;
//!             (Some(vec), rest)
//!         } else {
//!             (None, rest)
//!         };
//!         let ((other, stuff), rest) = map_decode!(rest, [String, u64]);
//!         Ok((
//!             Self {
//!                 some_flag,
//!                 values,
//!                 other,
//!                 stuff,
//!             },
//!             rest,
//!         ))
//!     }
//! }
//!
//! // Test values
//! let foo = MyStruct {
//!     some_flag: false,
//!     values: None,
//!     other: "hi".to_string(),
//!     stuff: 42,
//! };
//!
//! let bar = MyStruct {
//!     some_flag: true,
//!     values: Some(vec![[1; 32], [2; 32]]),
//!     other: "yo".to_string(),
//!     stuff: 0,
//! };
//!
//! // Encode `foo` and `bar` to a buffer
//! let buffer = to_encoded_bytes!(&foo, &bar);
//!
//! // With the above use of a flags byte, the empty value encodes to only one byte
//! assert_eq!(
//!     buffer.len(),
//!     // flags + string + u64
//!     (1 + 3 + 1) +
//!     // "" + (values.len().encoded_size() + (values.len() * <[u8;32]>::encoded_size()) + ""
//!     (1 + (1 + (2 * 32)) + 3 + 1)
//! );
//!
//! // And decode directly to your own struct
//! let (foo_dec, rest) = MyStruct::decode(&buffer)?;
//! let (bar_dec, rest) = MyStruct::decode(&rest)?;
//! // Ensure all bytes were used
//! assert!(rest.is_empty());
//! assert_eq!(foo_dec, foo);
//! assert_eq!(bar_dec, bar);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
mod error;
mod fixedwidth;
pub use fixedwidth::{FixedWidthEncoding, FixedWidthU32, FixedWidthU64, FixedWidthUint};
use std::{
    any::type_name,
    net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6},
};

pub use crate::error::{EncodingError, EncodingErrorKind};

/// indicates a variable width unsigned integer fits in u16
pub const U16_SIGNIFIER: u8 = 0xfd;
/// indicates a variable width unsigned integer fits in u32
pub const U32_SIGNIFIER: u8 = 0xfe;
/// indicates a variable width unsigned integer fits in u64
pub const U64_SIGNIFIER: u8 = 0xff;

const U16_SIZE: usize = 2;
const U32_SIZE: usize = 4;
const U64_SIZE: usize = 8;

/// Encoded size of a network port
pub const PORT_ENCODED_SIZE: usize = 2; // ports are unsigned 16-bit integers (u16)
/// Encoded size of an ipv4 address
pub const IPV4_ADDR_ENCODED_SIZE: usize = 4;
/// Encoded size of an ipv6 address
pub const IPV6_ADDR_ENCODED_SIZE: usize = 16;
/// Encoded size for a [`SocketAddrV4`], an ipv4 address plus port.
pub const SOCKET_ADDR_V4_ENCODED_SIZE: usize = IPV4_ADDR_ENCODED_SIZE + PORT_ENCODED_SIZE;
/// Encoded size for a [`SocketAddrV6`], an ipv6 address plus port.
pub const SOCKET_ADDR_V6_ENCODED_SIZE: usize = IPV6_ADDR_ENCODED_SIZE + PORT_ENCODED_SIZE;

/// A trait for building small and fast parsers and serializers.
pub trait CompactEncoding<Decode: ?Sized = Self> {
    /// The size in bytes required to encode `self`.
    fn encoded_size(&self) -> Result<usize, EncodingError>;

    /// Encode `self` into `buffer` returning the remainder of `buffer`.
    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError>;

    /// Decode a value from the given `buffer` of the type specified by the `Decode` type parameter
    /// (which defaults to `Self`). Returns the decoded value and remaining undecoded bytes.
    fn decode(buffer: &[u8]) -> Result<(Decode, &[u8]), EncodingError>
    where
        Decode: Sized;

    /// Encode `self` into a `Vec<u8>`. This is just a helper method for creating a buffer and
    /// encoding to it in one step.
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use compact_encoding::CompactEncoding;
    /// let foo: Ipv4Addr = "0.0.0.0".parse()?;
    /// let mut buff = vec![0; foo.encoded_size()?];
    /// foo.encode(&mut buff)?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn to_encoded_bytes(&self) -> Result<Box<[u8]>, EncodingError> {
        let mut buff = self.create_buffer()?;
        self.encode(&mut buff)?;
        Ok(buff)
    }
    /// Create an empty buffer of the correct size for encoding `self` to. This is just a helper
    /// method for: encoding to it in one step.
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use compact_encoding::CompactEncoding;
    /// let foo: Ipv4Addr = "0.0.0.0".parse()?;
    /// vec![0; foo.encoded_size()?];
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn create_buffer(&self) -> Result<Box<[u8]>, EncodingError> {
        Ok(vec![0; self.encoded_size()?].into_boxed_slice())
    }

    /// Like [`CompactEncoding::encode`] but also return the number of bytes encoded.
    fn encode_with_len<'a>(
        &self,
        buffer: &'a mut [u8],
    ) -> Result<(&'a mut [u8], usize), EncodingError> {
        let before_len = buffer.len();
        let rest = self.encode(buffer)?;
        let num_encoded_bytes = before_len - rest.len();
        Ok((rest, num_encoded_bytes))
    }

    /// Like [`CompactEncoding::decode`] but also return the number of bytes decoded.
    fn decode_with_len(buffer: &[u8]) -> Result<(Decode, &[u8], usize), EncodingError>
    where
        Decode: Sized,
    {
        let (out, rest) = Self::decode(buffer)?;
        Ok((out, rest, buffer.len() - rest.len()))
    }
}

/// Implement this for type `T` to have `CompactEncoding` implemented for `Vec<T>`
pub trait VecEncodable<Decode = Self>: CompactEncoding<Decode> {
    /// Calculate the resulting size in bytes of `vec`
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized;

    /// Encode `vec` to `buffer`
    fn vec_encode<'a>(vec: &[Self], buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized + CompactEncoding,
    {
        encode_vec(vec, buffer)
    }

    /// Decode [`Vec<Decode>`] from buffer
    fn vec_decode(buffer: &[u8]) -> Result<(Vec<Decode>, &[u8]), EncodingError>
    where
        Decode: Sized + CompactEncoding,
    {
        decode_vec(buffer)
    }
}

// NB: we DO want &Box<..> because we want the trait to work for boxed things, hence clippy::allow
#[allow(clippy::borrowed_box)]
/// Define this trait for `T` to get `impl Box<[T]> for CompactEncoding`
pub trait BoxedSliceEncodable: CompactEncoding {
    /// The encoded size in bytes
    fn boxed_slice_encoded_size(boxed: &Box<[Self]>) -> Result<usize, EncodingError>
    where
        Self: Sized;

    /// Encode `Box<[Self]>` to the buffer and return the remainder of the buffer
    fn boxed_slice_encode<'a>(
        vec: &Box<[Self]>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized,
    {
        encode_vec(vec, buffer)
    }

    /// Decode [`Box<[Self]>`] from buffer
    fn boxed_slice_decode(buffer: &[u8]) -> Result<(Box<[Self]>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (result, rest) = decode_vec(buffer)?;
        Ok((result.into_boxed_slice(), rest))
    }
}

#[macro_export]
/// Given a list of [`CompactEncoding`] things, sum the result of calling
/// [`CompactEncoding::encoded_size`] on all of them.
/// Note this is macro is useful when your arguments have differing types.
/// ```
/// # use crate::compact_encoding::{sum_encoded_size, CompactEncoding};
/// # use std::net::Ipv4Addr;
/// let foo: Ipv4Addr = "0.0.0.0".parse()?;
/// let bar = 42u64;
/// let qux = "hello?";
/// let result = sum_encoded_size!(foo, bar, qux);
/// assert_eq!(result, 12);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
/// If you want to use this within a non-result context you can do
/// ```
/// # use crate::compact_encoding::{sum_encoded_size, CompactEncoding, EncodingError};
/// let bar = 42u64;
/// let result = (|| Ok::<usize, EncodingError>(sum_encoded_size!(bar)))().unwrap();
/// assert_eq!(result, 1);
/// ```
macro_rules! sum_encoded_size {
    ($($val:expr),+) => {{
        0
        $(
            + $val.encoded_size()?
        )*
    }}
}

#[macro_export]
/// Given a list of [`CompactEncoding`] things, create a zeroed buffer of the correct size for encoding.
/// Note this is macro is useful when your arguments have differing types.
/// ```
/// # use crate::compact_encoding::{create_buffer, CompactEncoding};
/// # use std::net::Ipv4Addr;
/// let foo: Ipv4Addr = "0.0.0.0".parse()?;
/// let bar = 42u64;
/// let qux = "hello?";
/// let buff = create_buffer!(foo, bar, qux);
/// assert_eq!(buff.len(), 12);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
macro_rules! create_buffer {
    ($($val:expr),+) => {{
        let len = (
            0
            $(
                + $val.encoded_size()?
            )*
        );
        vec![0; len].into_boxed_slice()
    }}
}

#[macro_export]
/// Given a buffer and a list of [`CompactEncoding`] things, encode the arguments to the buffer.
/// Note this is macro is useful when your arguments have differing types.
/// ```
/// # use crate::compact_encoding::{create_buffer, map_encode, CompactEncoding};
/// let num = 42u64;
/// let word = "yo";
/// let mut buff = create_buffer!(num, word);
/// let result = map_encode!(&mut buff, num, word);
/// assert!(result.is_empty());
/// assert_eq!(&*buff, &[42, 2, b'y', b'o']);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
macro_rules! map_encode {
    ($buffer:expr$(,)*) => {
        $buffer
    };
    // Base case: single field
    ($buffer:expr, $field:expr) => {
        $field.encode($buffer)?
    };
    // Recursive case: first field + rest
    ($buffer:expr, $first:expr, $($rest:expr),+) => {{
        let rest = $first.encode($buffer)?;
        map_encode!(rest, $($rest),+)
    }};
}

#[macro_export]
/// Given a list of [`CompactEncoding`] things, encode the arguments to the buffer.
/// Note this is macro is useful when your arguments have differing types.
/// ```
/// # use crate::compact_encoding::to_encoded_bytes;
/// let result = to_encoded_bytes!(42u64, "yo");
/// assert_eq!(&*result, &[42, 2, 121, 111]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
macro_rules! to_encoded_bytes {
    ($($val:expr),*) => {{
        use $crate::{map_encode, create_buffer, CompactEncoding};
        let mut buffer = create_buffer!($($val),*);
        map_encode!(&mut buffer, $($val),*);
        buffer
    }}
}

#[macro_export]
/// Decode a buffer to the list of types provided, returning the remaining buffer.
/// It takes as arguments: `(&buffer, [type1, type2, type3, ...])`
/// And returns: `((decoded_type1, decoded_type2, ...), remaining_buffer)`
/// ```
/// # use crate::compact_encoding::{to_encoded_bytes, map_decode};
/// let buffer = to_encoded_bytes!(42u64, "yo");
/// let ((number, word), remaining_buffer) = map_decode!(&buffer, [u64, String]);
/// assert!(remaining_buffer.is_empty());
/// assert_eq!(number, 42u64);
/// assert_eq!(word, "yo");
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
macro_rules! map_decode {
    ($buffer:expr, [
        $($field_type:ty),* $(,)?
    ]) => {{
        use $crate::CompactEncoding;
        let mut current_buffer: &[u8] = $buffer;

        // Decode each type into `result_tuple`
        let result_tuple = (
            $(
                match <$field_type>::decode(&current_buffer)? {
                    (value, new_buf) => {
                        current_buffer = new_buf;
                        value
                    }
                },
            )*
        );
        (result_tuple, current_buffer)
    }};
}

#[macro_export]
/// Helper for mapping the first element of a two eleent tuple.
/// This is useful for cleanly handling the result of CompactEncoding::decode.
macro_rules! map_first {
    ($res:expr, $f:expr) => {{
        let (one, two) = $res;
        let mapped = $f(one);
        (mapped, two)
    }};
}

#[macro_export]
/// like [`map_first`] but the mapping should return a result.
macro_rules! map_first_result {
    ($res:expr, $f:expr) => {{
        let (one, two) = $res;
        let mapped = $f(one)?;
        (mapped, two)
    }};
}

/// Split a slice in two at `mid`. Returns encoding error when `mid` is out of bounds.
pub fn get_slices_checked(buffer: &[u8], mid: usize) -> Result<(&[u8], &[u8]), EncodingError> {
    buffer.split_at_checked(mid).ok_or_else(|| {
        EncodingError::out_of_bounds(&format!(
            "Could not split slice at [{mid}] slice.len() = [{}]",
            buffer.len()
        ))
    })
}

/// Split a mutable slice into two mutable slices around `mid`.
/// Returns encoding error when `mid` is out of bounds.
pub fn get_slices_mut_checked(
    buffer: &mut [u8],
    mid: usize,
) -> Result<(&mut [u8], &mut [u8]), EncodingError> {
    let len = buffer.len();
    buffer.split_at_mut_checked(mid).ok_or_else(|| {
        EncodingError::out_of_bounds(&format!(
            "Could not split mut slice at [{mid}] slice.len() = [{len}]"
        ))
    })
}

/// Get a slice as an array of size `N`. Errors when `slice.len() != N`.
pub fn as_array<const N: usize>(buffer: &[u8]) -> Result<&[u8; N], EncodingError> {
    let blen = buffer.len();
    if blen != N {
        return Err(EncodingError::out_of_bounds(&format!(
            "Could get a [{N}] byte array from a slice of length [{blen}]"
        )));
    }
    Ok(buffer.split_first_chunk::<N>().expect("checked above").0)
}

/// Get a slice as a mutable array of size `N`. Errors when `slice.len() != N`.
pub fn as_array_mut<const N: usize>(buffer: &mut [u8]) -> Result<&mut [u8; N], EncodingError> {
    let blen = buffer.len();
    if blen != N {
        return Err(EncodingError::out_of_bounds(&format!(
            "Could get a [{N}] byte array from a slice of length [{blen}]"
        )));
    }
    Ok(buffer
        .split_first_chunk_mut::<N>()
        .expect("checked above")
        .0)
}

/// Write `source` to `buffer` and return the remainder of `buffer`.
/// Errors when `N < buffer.len()`
pub fn write_array<'a, const N: usize>(
    source: &[u8; N],
    buffer: &'a mut [u8],
) -> std::result::Result<&'a mut [u8], EncodingError> {
    let blen = buffer.len();
    let Some((dest, rest)) = buffer.split_first_chunk_mut::<N>() else {
        return Err(EncodingError::out_of_bounds(&format!(
            "Could not write [{}] bytes to buffer of length [{}]",
            N, blen
        )));
    };
    dest.copy_from_slice(source);
    Ok(rest)
}

/// split the first `N` bytes of `buffer` off and return them
pub fn take_array<const N: usize>(
    buffer: &[u8],
) -> std::result::Result<([u8; N], &[u8]), EncodingError> {
    let Some((out, rest)) = buffer.split_first_chunk::<N>() else {
        return Err(EncodingError::out_of_bounds(&format!(
            "Could not take [{}] bytes from buffer of length [{}]",
            N,
            buffer.len()
        )));
    };
    Ok((*out, rest))
}
/// split the first `N` bytes of `buffer` off and return them
pub fn take_array_mut<const N: usize>(
    buffer: &mut [u8],
) -> std::result::Result<(&mut [u8; N], &mut [u8]), EncodingError> {
    let blen = buffer.len();
    let Some((out, rest)) = buffer.split_first_chunk_mut::<N>() else {
        return Err(EncodingError::out_of_bounds(&format!(
            "Could not write [{}] bytes to buffer of length [{blen}]",
            N,
        )));
    };
    Ok((out, rest))
}

/// write `source` to `buffer` and return remaining buffer
pub fn write_slice<'a>(source: &[u8], buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
    let mid = source.len();
    let (dest, rest) = get_slices_mut_checked(buffer, mid)?;
    dest.copy_from_slice(source);
    Ok(rest)
}

/// Helper to convert a vec to an array, and fail with an encoding error when needed
pub fn bytes_fixed_from_vec<const N: usize>(value: &[u8]) -> Result<[u8; N], EncodingError> {
    <[u8; N]>::try_from(value).map_err(|e| {
        EncodingError::invalid_data(&format!(
            "Could not covert slice with length [{}] to array of length [{}]. Error: [{e}]",
            value.len(),
            N
        ))
    })
}

fn encoded_size_str(value: &str) -> Result<usize, EncodingError> {
    Ok(encoded_size_usize(value.len()) + value.len())
}

/// The number of bytes required to encode this number. Note this is always variable width.
pub fn encoded_size_usize(val: usize) -> usize {
    if val < U16_SIGNIFIER.into() {
        1
    } else if val <= 0xffff {
        3
    } else if val <= 0xffffffff {
        5
    } else {
        9
    }
}

/// The number of bytes required to encode this number.
/// We only need this for u64 because all other uints can be converted to usize reliably.
pub fn encoded_size_var_u64(val: u64) -> usize {
    if val < U16_SIGNIFIER.into() {
        1
    } else if val <= 0xffff {
        3
    } else if val <= 0xffffffff {
        5
    } else {
        9
    }
}

/// Write `uint` to the start of `buffer` and return the remaining part of `buffer`.
pub fn encode_var_u64(uint: u64, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
    if uint < U16_SIGNIFIER.into() {
        encode_u8(uint as u8, buffer)
    } else if uint <= 0xffff {
        let rest = write_array(&[U16_SIGNIFIER], buffer)?;
        encode_u16(uint as u16, rest)
    } else if uint <= 0xffffffff {
        let rest = write_array(&[U32_SIGNIFIER], buffer)?;
        encode_u32(uint as u32, rest)
    } else {
        let rest = write_array(&[U64_SIGNIFIER], buffer)?;
        encode_u64(uint, rest)
    }
}

/// Decode a `usize` from `buffer` and return the remaining bytes.
/// This will fail, when we are decoding a `usize` on a usize = u32 machine for data that was originally encoded on a `usize = u64` machine whenever the value is over `u32::MAX`.
pub fn decode_usize(buffer: &[u8]) -> Result<(usize, &[u8]), EncodingError> {
    let ([first], rest) = take_array::<1>(buffer)?;
    Ok(match first {
        x if x < U16_SIGNIFIER => (x.into(), rest),
        U16_SIGNIFIER => map_first!(decode_u16(rest)?, |x: u16| x.into()),
        U32_SIGNIFIER => {
            map_first_result!(decode_u32(rest)?, |val| usize::try_from(val)
                .map_err(|_| EncodingError::overflow("Could not convert u32 to usize")))
        }
        _ => {
            map_first_result!(decode_u64(rest)?, |val| usize::try_from(val)
                .map_err(|_| EncodingError::overflow("Could not convert u64 to usize")))
        }
    })
}

/// Encoded a fixed sized array to a buffer, return the remainder of the buffer.
/// Errors when `value.len() > buffer.len()`;
/// ```
/// # use compact_encoding::encode_bytes_fixed;
/// let mut buffer = vec![0; 3];
/// let rest = encode_bytes_fixed(&[4, 2], &mut buffer)?;
/// assert_eq!(rest, &[0]);
/// assert_eq!(buffer, &[4, 2, 0]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn encode_bytes_fixed<'a, const N: usize>(
    value: &[u8; N],
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    write_array(value, buffer)
}

/// Decode a fixed sized array from a buffer. Return the array and the remainder of the buffer.
/// Errors when `buffer.len() < N`;
/// ```
/// # use compact_encoding::decode_bytes_fixed;
/// let mut buffer = vec![1, 2, 3];
/// let (arr, rest) = decode_bytes_fixed::<2>(&mut buffer)?;
/// assert_eq!(arr, [1, 2]);
/// assert_eq!(rest, &[3]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn decode_bytes_fixed<const N: usize>(
    buffer: &[u8],
) -> Result<([u8; N], &[u8]), EncodingError> {
    take_array(buffer)
    //write_array(value, buffer)
}

fn decode_u16(buffer: &[u8]) -> Result<(u16, &[u8]), EncodingError> {
    let (data, rest) = take_array::<2>(buffer)?;
    Ok((u16::from_le_bytes(data), rest))
}
fn decode_u32(buffer: &[u8]) -> Result<(u32, &[u8]), EncodingError> {
    let (data, rest) = take_array::<4>(buffer)?;
    Ok((u32::from_le_bytes(data), rest))
}
fn decode_u64(buffer: &[u8]) -> Result<(u64, &[u8]), EncodingError> {
    let (data, rest) = take_array::<8>(buffer)?;
    Ok((u64::from_le_bytes(data), rest))
}

fn decode_u32_var(buffer: &[u8]) -> Result<(u32, &[u8]), EncodingError> {
    let ([first], rest) = take_array::<1>(buffer)?;
    Ok(match first {
        x if x < U16_SIGNIFIER => (x.into(), rest),
        U16_SIGNIFIER => {
            let (val, rest) = decode_u16(rest)?;
            (val.into(), rest)
        }
        _ => decode_u32(rest)?,
    })
}

fn decode_u64_var(buffer: &[u8]) -> Result<(u64, &[u8]), EncodingError> {
    let ([first], rest) = take_array::<1>(buffer)?;
    Ok(match first {
        x if x < U16_SIGNIFIER => (x.into(), rest),
        U16_SIGNIFIER => map_first!(decode_u16(rest)?, |x: u16| x.into()),
        U32_SIGNIFIER => map_first!(decode_u32(rest)?, |x: u32| x.into()),
        _ => decode_u64(rest)?,
    })
}

fn decode_buffer_vec(buffer: &[u8]) -> Result<(Vec<u8>, &[u8]), EncodingError> {
    let (n_bytes, rest) = decode_usize(buffer)?;
    let (out, rest) = get_slices_checked(rest, n_bytes)?;
    Ok((out.to_vec(), rest))
}

fn decode_string(buffer: &[u8]) -> Result<(String, &[u8]), EncodingError> {
    let (len, rest) = decode_usize(buffer)?;
    let (str_buff, rest) = get_slices_checked(rest, len)?;
    let out = String::from_utf8(str_buff.to_vec())
        .map_err(|e| EncodingError::invalid_data(&format!("String is invalid UTF-8, {e}")))?;
    Ok((out, rest))
}

fn encode_u8(val: u8, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
    write_array(&val.to_le_bytes(), buffer)
}
fn encode_u16(val: u16, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
    write_array(&val.to_le_bytes(), buffer)
}
fn encode_u32(val: u32, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
    write_array(&val.to_le_bytes(), buffer)
}
fn encode_u64(val: u64, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
    write_array(&val.to_le_bytes(), buffer)
}

/// Encode a `usize` in a variable width way
pub fn encode_usize_var<'a>(
    value: &usize,
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    if *value < U16_SIGNIFIER.into() {
        encode_u8(*value as u8, buffer)
    } else if *value <= 0xffff {
        encode_u16(*value as u16, write_array(&[U16_SIGNIFIER], buffer)?)
    } else if *value <= 0xffffffff {
        let value = u32::try_from(*value).map_err(|e| {
            EncodingError::overflow(&format!(
                "count not covert usize [{value}] to u32. Error: [{e}]"
            ))
        })?;
        encode_u32(value, write_array(&[U32_SIGNIFIER], buffer)?)
    } else {
        let value = u64::try_from(*value).map_err(|e| {
            EncodingError::overflow(&format!(
                "count not covert usize [{value}] to u64. Error: [{e}]"
            ))
        })?;
        encode_u64(value, write_array(&[U64_SIGNIFIER], buffer)?)
    }
}

fn encode_str<'a>(value: &str, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
    let rest = encode_usize_var(&value.len(), buffer)?;
    write_slice(value.as_bytes(), rest)
}

fn encode_buffer<'a>(value: &[u8], buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
    let rest = encode_usize_var(&value.len(), buffer)?;
    write_slice(value, rest)
}

impl<const N: usize> CompactEncoding for [u8; N] {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(N)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        write_array(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        take_array(buffer)
    }
}

impl CompactEncoding for u8 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(1)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        write_array(&[*self], buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let ([out], rest) = take_array::<1>(buffer)?;
        Ok((out, rest))
    }
}

impl CompactEncoding for u16 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(U16_SIZE)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_u16(*self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u16(buffer)
    }
}

// NB: we want u32 encoded and decoded as variable sized uint
impl CompactEncoding for u32 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(encoded_size_usize(*self as usize))
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_usize_var(&(*self as usize), buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u32_var(buffer)
    }
}
impl CompactEncoding for u64 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(encoded_size_var_u64(*self))
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_var_u64(*self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u64_var(buffer)
    }
}

impl CompactEncoding for usize {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(encoded_size_usize(*self))
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_usize_var(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_usize(buffer)
    }
}

impl CompactEncoding for String {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        encoded_size_str(self)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_str(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_string(buffer)
    }
}

impl CompactEncoding<String> for str {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        encoded_size_str(self)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_str(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(String, &[u8]), EncodingError> {
        decode_string(buffer)
    }
}

impl CompactEncoding for Vec<String> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        let mut out = encoded_size_usize(self.len());
        for s in self {
            out += s.encoded_size()?;
        }
        Ok(out)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        let mut rest = encode_usize_var(&self.len(), buffer)?;
        for s in self {
            rest = s.encode(rest)?;
        }
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (len, mut rest) = decode_usize(buffer)?;
        let mut out = Vec::with_capacity(len);
        for _ in 0..len {
            let result = String::decode(rest)?;
            out.push(result.0);
            rest = result.1;
        }
        Ok((out, rest))
    }
}

impl CompactEncoding for Vec<u8> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(encoded_size_usize(self.len()) + self.len())
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_buffer(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_buffer_vec(buffer)
    }
}
impl CompactEncoding<Vec<u8>> for &[u8] {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(encoded_size_usize(self.len()) + self.len())
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_buffer(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Vec<u8>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_buffer_vec(buffer)
    }
}

impl CompactEncoding for Ipv4Addr {
    fn encoded_size(&self) -> std::result::Result<usize, EncodingError> {
        Ok(U32_SIZE)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> std::result::Result<&'a mut [u8], EncodingError> {
        let Some((dest, rest)) = buffer.split_first_chunk_mut::<4>() else {
            return Err(EncodingError::out_of_bounds(&format!(
                "Colud not encode {}, not enough room in buffer",
                type_name::<Self>()
            )));
        };
        dest.copy_from_slice(&self.octets());
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> std::result::Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let Some((dest, rest)) = buffer.split_first_chunk::<4>() else {
            return Err(EncodingError::out_of_bounds(&format!(
                "Colud not decode {}, buffer not big enough",
                type_name::<Self>()
            )));
        };
        Ok((Ipv4Addr::from(*dest), rest))
    }
}

impl CompactEncoding for Ipv6Addr {
    fn encoded_size(&self) -> std::result::Result<usize, EncodingError> {
        Ok(IPV6_ADDR_ENCODED_SIZE)
    }

    /// ```
    /// # use std::net::Ipv6Addr;
    /// # use compact_encoding::CompactEncoding;
    /// let addr: Ipv6Addr = "1:2:3::1".parse()?;
    /// let buff = addr.to_encoded_bytes()?.to_vec();
    /// assert_eq!(buff, vec![0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn encode<'a>(&self, buffer: &'a mut [u8]) -> std::result::Result<&'a mut [u8], EncodingError> {
        let Some((dest, rest)) = buffer.split_first_chunk_mut::<16>() else {
            return Err(EncodingError::out_of_bounds(&format!(
                "Colud not encode {}, not enough room in buffer",
                type_name::<Self>()
            )));
        };
        dest.copy_from_slice(&self.octets());
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> std::result::Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let Some((dest, rest)) = buffer.split_first_chunk::<16>() else {
            return Err(EncodingError::out_of_bounds(&format!(
                "Colud not decode {}, buffer not big enough",
                type_name::<Self>()
            )));
        };
        Ok((Ipv6Addr::from(*dest), rest))
    }
}

fn encode_vec<'a, T: CompactEncoding + Sized>(
    vec: &[T],
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    let mut rest = encode_usize_var(&vec.len(), buffer)?;
    for x in vec {
        rest = <T as CompactEncoding>::encode(x, rest)?;
    }
    Ok(rest)
}

fn decode_vec<T: CompactEncoding + Sized>(buffer: &[u8]) -> Result<(Vec<T>, &[u8]), EncodingError> {
    let (len, mut rest) = decode_usize(buffer)?;
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        let res = <T as CompactEncoding>::decode(rest)?;
        out.push(res.0);
        rest = res.1;
    }
    Ok((out, rest))
}

impl<T: VecEncodable> CompactEncoding for Vec<T> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        T::vec_encoded_size(self)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        <T as VecEncodable>::vec_encode(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        <T as VecEncodable>::vec_decode(buffer)
    }
}

impl<T, D> CompactEncoding<Vec<D>> for &[T]
where
    T: VecEncodable<D> + CompactEncoding<D>,
    D: CompactEncoding,
{
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        T::vec_encoded_size(self)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        let mut rest = encode_usize_var(&self.len(), buffer)?;
        for x in *self {
            rest = x.encode(rest)?;
        }
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> Result<(Vec<D>, &[u8]), EncodingError>
    where
        D: Sized,
    {
        decode_vec(buffer)
    }
}

/// Get the encoded size for a Vec with elements which have a fixed size encoding.
pub fn vec_encoded_size_for_fixed_sized_elements<T: CompactEncoding>(
    vec: &[T],
    element_encoded_size: usize,
) -> usize {
    encoded_size_usize(vec.len()) + (vec.len() * element_encoded_size)
}

impl VecEncodable for u32 {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(encoded_size_usize(vec.len()) + (vec.len() * 4))
    }
    /// Encode `vec` to `buffer`
    fn vec_encode<'a>(vec: &[Self], buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized,
    {
        let mut rest = encode_usize_var(&vec.len(), buffer)?;
        for x in vec {
            rest = encode_u32(*x, rest)?;
        }
        Ok(rest)
    }

    /// Decode [`Vec<Self>`] from buffer
    fn vec_decode(buffer: &[u8]) -> Result<(Vec<Self>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (len, mut rest) = decode_usize(buffer)?;
        let mut out = Vec::with_capacity(len);

        for _ in 0..len {
            let result = decode_u32(rest)?;
            out.push(result.0);
            rest = result.1;
        }
        Ok((out, rest))
    }
}

impl<const N: usize> VecEncodable for [u8; N] {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(encoded_size_usize(vec.len()) + (vec.len() * N))
    }
}

impl BoxedSliceEncodable for u8 {
    fn boxed_slice_encoded_size(boxed: &Box<[Self]>) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(encoded_size_usize(boxed.len()) + boxed.len())
    }

    fn boxed_slice_encode<'a>(
        boxed: &Box<[Self]>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized,
    {
        let rest = encode_usize_var(&boxed.len(), buffer)?;
        write_slice(boxed, rest)
    }

    fn boxed_slice_decode(buffer: &[u8]) -> Result<(Box<[Self]>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (len, rest) = decode_usize(buffer)?;
        let (out, rest) = get_slices_checked(rest, len)?;
        Ok((out.into(), rest))
    }
}

impl<T: BoxedSliceEncodable> CompactEncoding for Box<[T]> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        T::boxed_slice_encoded_size(self)
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        <T as BoxedSliceEncodable>::boxed_slice_encode(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        <T as BoxedSliceEncodable>::boxed_slice_decode(buffer)
    }
}

impl CompactEncoding for SocketAddrV4 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(SOCKET_ADDR_V4_ENCODED_SIZE)
    }

    /// ```
    /// # use std::net::SocketAddrV4;
    /// # use compact_encoding::CompactEncoding;
    /// let addr: SocketAddrV4 = "127.0.0.1:42".parse()?;
    /// let buff = addr.to_encoded_bytes()?.to_vec();
    /// assert_eq!(buff, vec![127, 0, 0, 1, 42, 0]);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        let rest = self.ip().encode(buffer)?;
        encode_u16(self.port(), rest)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (ip, rest) = Ipv4Addr::decode(buffer)?;
        let (port, rest) = decode_u16(rest)?;
        Ok((SocketAddrV4::new(ip, port), rest))
    }
}
impl CompactEncoding for SocketAddrV6 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(SOCKET_ADDR_V6_ENCODED_SIZE)
    }

    /// ```
    /// # use std::net::SocketAddrV6;
    /// # use compact_encoding::CompactEncoding;
    /// let addr: SocketAddrV6 = "[1:2:3::1]:80".parse()?;
    /// let buff = addr.to_encoded_bytes()?.to_vec();
    /// assert_eq!(buff, vec![0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 80, 0]);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        let rest = self.ip().encode(buffer)?;
        encode_u16(self.port(), rest)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (ip, rest) = Ipv6Addr::decode(buffer)?;
        let (port, rest) = decode_u16(rest)?;
        // TODO is this correct for flowinfo and scope_id?
        Ok((SocketAddrV6::new(ip, port, 0, 0), rest))
    }
}

impl VecEncodable for SocketAddrV4 {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(vec_encoded_size_for_fixed_sized_elements(
            vec,
            SOCKET_ADDR_V4_ENCODED_SIZE,
        ))
    }
}

impl VecEncodable for SocketAddrV6 {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(vec_encoded_size_for_fixed_sized_elements(
            vec,
            SOCKET_ADDR_V6_ENCODED_SIZE,
        ))
    }
}

impl VecEncodable for Vec<u8> {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        let mut out = encoded_size_usize(vec.len());
        for v in vec {
            out += v.encoded_size()?;
        }
        Ok(out)
    }
}

impl VecEncodable<Vec<u8>> for &[u8] {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        let mut out = encoded_size_usize(vec.len());
        for v in vec {
            out += v.encoded_size()?;
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn decode_buff_vec() -> Result<(), EncodingError> {
        let buf = &[1, 1];
        let (a, b) = decode_buffer_vec(buf)?;
        assert_eq!(a, &[1]);
        assert_eq!(b, &[]);
        Ok(())
    }
    macro_rules! check_usize_var_enc_dec {
        ($size:expr, $value:expr) => {
            let mut buffer = vec![0; encoded_size_usize($value)];
            assert_eq!(buffer.len(), $size);
            let remaining = encode_usize_var(&$value, &mut buffer)?;
            assert!(remaining.is_empty());
            let (result, rest) = decode_usize(&buffer)?;
            assert!(rest.is_empty());
            assert_eq!(result, $value);
        };
    }

    #[test]
    fn usize_var_enc_dec() -> Result<(), EncodingError> {
        check_usize_var_enc_dec!(1, 42);
        check_usize_var_enc_dec!(1 + 2, 256);
        check_usize_var_enc_dec!(1 + 4, 65536);
        check_usize_var_enc_dec!(1 + 8, 4294967296);

        Ok(())
    }
    #[test]
    fn enc_dec_vec_vec_u8() -> Result<(), EncodingError> {
        let input = vec![b"hello".to_vec(), b"goodbye".to_vec()];
        let buf = input.as_slice().to_encoded_bytes()?;
        let (result, rest): (Vec<Vec<u8>>, &[u8]) = Vec::<Vec<u8>>::decode(&buf)?;
        assert_eq!(result.len(), input.len());
        for (i, v) in result.iter().enumerate() {
            assert_eq!(v, &input[i]);
        }
        assert!(rest.is_empty());
        Ok(())
    }

    #[test]
    fn enc_dec_slice_slice_u8() -> Result<(), EncodingError> {
        let input: &[&[u8]] = &[b"hello".as_slice(), b"goodbye".as_slice()];
        let buf = input.to_encoded_bytes()?;
        let (result, rest): (Vec<Vec<u8>>, &[u8]) = Vec::<Vec<u8>>::decode(&buf)?;
        assert_eq!(result.len(), input.len());
        for (i, v) in result.iter().enumerate() {
            assert_eq!(v, &input[i]);
        }
        assert!(rest.is_empty());
        Ok(())
    }

    #[test]
    fn enc_dec_byte_slice() -> Result<(), EncodingError> {
        let input: &[u8] = b"hello world";
        let buf = input.to_encoded_bytes()?;
        let (result, rest): (Vec<u8>, &[u8]) = Vec::<u8>::decode(&buf)?;
        assert_eq!(result, input);
        assert!(rest.is_empty());
        Ok(())
    }

    #[test]
    fn enc_dec_empty_slice_slice_u8() -> Result<(), EncodingError> {
        let input: &[&[u8]] = &[];
        let buf = input.to_encoded_bytes()?;
        assert_eq!(buf.len(), 1); // just the length prefix
        let (result, rest): (Vec<Vec<u8>>, &[u8]) = Vec::<Vec<u8>>::decode(&buf)?;
        assert!(result.is_empty());
        assert!(rest.is_empty());
        Ok(())
    }

    #[test]
    fn slice_and_vec_encode_identically() -> Result<(), EncodingError> {
        let vec_input = vec![b"hello".to_vec(), b"goodbye".to_vec()];
        let slice_input: &[&[u8]] = &[b"hello".as_slice(), b"goodbye".as_slice()];

        let vec_buf = vec_input.to_encoded_bytes()?;
        let slice_buf = slice_input.to_encoded_bytes()?;

        assert_eq!(&*vec_buf, &*slice_buf);
        Ok(())
    }
}
