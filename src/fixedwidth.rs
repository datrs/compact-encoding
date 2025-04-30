//! Allow encoding of unsigned ints in a fixed width way, instead of the default variable width.
//!
//! # Why?
//!
//! By default, unsigned integrers are variable width encoded with [`CompactEncoding`].
//! However we sometimes want them fixed width encoded.
//! The [`FixedWidthEncoding`] lets us do this. To fixed width encode an unsigned integrer simply
//! call [`FixedWidthEncoding::as_fixed_width`] on it. Like this:
//!
//! ```
//! # use compact_encoding::EncodingError;
//! use compact_encoding::{to_encoded_bytes, FixedWidthEncoding};
//! let buff = to_encoded_bytes!(42u32.as_fixed_width());
//! assert_eq!(buff, vec![42, 0, 0, 0]);
//! // vs variable width
//! let buff = to_encoded_bytes!(42u32);
//! assert_eq!(buff, vec![42]);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Likewise when decoding decoding from a fixed width encoded buffer you use
//! [`FixedWidthUint::decode`] which will decode to the underlying unsigned integer type.
//! So: `FixedWidthUint<u32>::decode(buffer) -> u32`.
//! Note that we also provide type aliases to make this more ergonomic:
//! `FixedWidthU64 = FixedWidthUint<u64`.
//!
//! ```
//! # use compact_encoding::EncodingError;
//! use compact_encoding::{map_decode, FixedWidthU32, FixedWidthUint};
//! let buff = vec![42, 0, 0, 0]; // 42_u32 fixed width encoded
//!
//! let ((decoded,), _) = map_decode!(&buff, [FixedWidthUint<u32>]);
//! assert_eq!(decoded, 42); // NOT! FixedWidthUint(42_u32)
//!
//! assert_eq!(map_decode!(&buff, [FixedWidthU32]).0 .0, 42); // or using the alias
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use crate::{
    decode_u32, decode_u64, encode_u32, encode_u64, CompactEncoding, EncodingError, U32_SIZE,
    U64_SIZE,
};

/// Implents functionality needed to encode unisegned integrer in a fixed width way with
/// [`CompactEncoding`]
pub trait FixedWidthEncoding {
    /// The type we decode to
    // TODO could we just use T?
    type Decode;
    /// The size in bytes required to encode `self`.
    fn fw_encoded_size(&self) -> Result<usize, EncodingError>;

    /// Encode `self` into `buffer` returning the remainder of `buffer`.
    fn fw_encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError>;

    /// Decode a value from the given `buffer` of the type specified by the `Decode` type parameter
    /// (which defaults to `Self`). Returns the decoded value and remaining undecoded bytes.
    fn fw_decode(buffer: &[u8]) -> Result<(Self::Decode, &[u8]), EncodingError>
    where
        Self: Sized;

    /// Get a uint in a form that encodes to a fixed width
    fn as_fixed_width(&self) -> FixedWidthUint<Self> {
        FixedWidthUint(self)
    }
}

/// A fixed width encodable unsigned integer
#[derive(Debug)]
pub struct FixedWidthUint<'a, T: FixedWidthEncoding + ?Sized>(&'a T);

impl<T: FixedWidthEncoding> CompactEncoding<T::Decode> for FixedWidthUint<'_, T> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        self.0.fw_encoded_size()
    }

    fn encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        self.0.fw_encode(buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(T::Decode, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        <T as FixedWidthEncoding>::fw_decode(buffer)
    }
}

impl FixedWidthEncoding for u32 {
    type Decode = u32;

    fn fw_encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(U32_SIZE)
    }

    fn fw_encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_u32(*self, buffer)
    }

    fn fw_decode(buffer: &[u8]) -> Result<(Self::Decode, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u32(buffer)
    }
}
impl FixedWidthEncoding for u64 {
    type Decode = u64;

    fn fw_encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(U64_SIZE)
    }

    fn fw_encode<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_u64(*self, buffer)
    }

    fn fw_decode(buffer: &[u8]) -> Result<(Self::Decode, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u64(buffer)
    }
}

/// A wrapper around [`u32`] to let us encoded/decode to/from a fixed width
pub type FixedWidthU32<'a> = FixedWidthUint<'a, u32>;
/// A wrapper around [`u64`] to let us encoded/decode to/from a fixed width
pub type FixedWidthU64<'a> = FixedWidthUint<'a, u64>;
#[cfg(test)]
mod test {
    use crate::{map_decode, to_encoded_bytes};

    use super::*;

    #[test]
    fn fixed_width_u32() -> Result<(), EncodingError> {
        let x = 42u32;
        let fixed_buff = to_encoded_bytes!(x.as_fixed_width());
        let var_buff = to_encoded_bytes!(x);
        assert_eq!(fixed_buff, vec![42, 0, 0, 0]);
        assert_eq!(var_buff, vec![42]);

        let ((fixed_dec,), rest) = map_decode!(&fixed_buff, [FixedWidthU32]);
        assert!(rest.is_empty());
        assert_eq!(fixed_dec, x);

        let ((var_dec,), rest) = map_decode!(&var_buff, [u32]);
        assert!(rest.is_empty());
        assert_eq!(var_dec, x);
        Ok(())
    }

    #[test]
    fn fixed_width_u64() -> Result<(), EncodingError> {
        let x = 42u64;
        let fixed_buff = to_encoded_bytes!(x.as_fixed_width());
        let var_buff = to_encoded_bytes!(x);
        assert_eq!(fixed_buff, vec![42, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(var_buff, vec![42]);

        let ((fixed_dec,), rest) = map_decode!(&fixed_buff, [FixedWidthU64]);
        assert!(rest.is_empty());
        assert_eq!(fixed_dec, x);
        Ok(())
    }
}
