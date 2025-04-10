#![allow(unused)]
//! CompactEncodable stuff
use std::net::{Ipv4Addr, Ipv6Addr};

use crate::{
    types::{U16_SIGNIFIER, U32_SIGNIFIER, U64_SIGNIFIER},
    EncodingError,
};

const U16_SIZE: usize = 2;
const U32_SIZE: usize = 4;
/// Instead of carrying around [`State`] we just use a buffer.
/// To track how much buffer is used (like we do with [`State::start`])
/// we return a slice of the unused portion after encoding.
///
/// If you Implement this trait on a type then it will automatically implement [`CompactEncoding`].
pub trait CompactEncodable {
    /// The size required in the buffer for this time
    fn encoded_size(&self) -> Result<usize, EncodingError>;
    /// The bytes resulting from encoding this type
    // TODO add buffer argument. Change result to return remaining buffer
    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError>;
    /// Decode a value from the buffer. Returns the value  and remaining undecoded bytes
    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized;

    /// Encode `self` into a `Vec<u8>`. This is just a helper method for:
    /// ```
    /// # use std::net::Ipv4Addr;
    /// # use compact_encoding::encodable::CompactEncodable;
    /// let foo: Ipv4Addr = "0.0.0.0".parse()?;
    /// let mut buff = vec![0; foo.encoded_size()?];
    /// foo.encoded_bytes(&mut buff)?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn to_bytes(&self) -> Result<Vec<u8>, EncodingError> {
        let mut buff = vec![0; self.encoded_size()?];
        self.encoded_bytes(&mut buff)?;
        Ok(buff)
    }
}

/// Implement this for type `T` to have `CompactEncodable` implemented for `Vec<T>`
pub trait VecEncodable: CompactEncodable {
    /// Calculate the resulting size in bytes of `vec`
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized;

    /// Encode `vec` to `buffer`
    fn encoded_bytes<'a>(vec: &[Self], buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized,
    {
        encode_vec(vec, buffer)
    }

    /// Decode [`Vec<Self>`] from buffer
    fn decode(buffer: &[u8]) -> Result<(Vec<Self>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_vec(buffer)
    }
}

// NB: we DO want &Box<..> because we want the trait to work for  boxed things
#[allow(clippy::borrowed_box)]
/// Define this trait for `T` to get `Box<[T]>: CompactEncodable`
pub trait BoxArrayEncodable: CompactEncodable {
    /// The encoded size in bytes
    fn boxed_array_encoded_size(boxed: &Box<[Self]>) -> Result<usize, EncodingError>
    where
        Self: Sized;

    /// Encode `Box<[T]>` to the buffer and return the remainder of the buffer
    fn encoded_bytes<'a>(
        vec: &Box<[Self]>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized,
    {
        encode_vec(vec, buffer)
    }

    /// Decode [`Vec<Self>`] from buffer
    fn decode(buffer: &[u8]) -> Result<(Box<[Self]>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (result, rest) = decode_vec(buffer)?;
        Ok((result.into_boxed_slice(), rest))
    }
}

impl CompactEncodable for Ipv4Addr {
    fn encoded_size(&self) -> std::result::Result<usize, EncodingError> {
        Ok(U32_SIZE)
    }

    fn encoded_bytes<'a>(
        &self,
        buffer: &'a mut [u8],
    ) -> std::result::Result<&'a mut [u8], EncodingError> {
        let Some((dest, rest)) = buffer.split_first_chunk_mut::<4>() else {
            todo!()
        };
        dest.copy_from_slice(&self.octets());
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> std::result::Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let Some((dest, rest)) = buffer.split_first_chunk::<4>() else {
            todo!()
        };
        Ok((Ipv4Addr::from(*dest), rest))
    }
}
impl CompactEncodable for Ipv6Addr {
    fn encoded_size(&self) -> std::result::Result<usize, EncodingError> {
        Ok(4)
    }

    fn encoded_bytes<'a>(
        &self,
        buffer: &'a mut [u8],
    ) -> std::result::Result<&'a mut [u8], EncodingError> {
        let Some((dest, rest)) = buffer.split_first_chunk_mut::<16>() else {
            todo!()
        };
        dest.copy_from_slice(&self.octets());
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> std::result::Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let Some((dest, rest)) = buffer.split_first_chunk::<16>() else {
            todo!()
        };
        Ok((Ipv6Addr::from(*dest), rest))
    }
}
/// helper for mapping the first element of a two eleent tuple
macro_rules! map_first {
    ($res:expr, $f:expr) => {{
        let (one, two) = $res;
        let mapped = $f(one)?;
        (mapped, two)
    }};
}

/// The number of bytes required to encode this number
pub fn usize_encoded_size(val: usize) -> usize {
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
pub fn u64_var_encoded_size(val: u64) -> usize {
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
pub fn u64_encoded_bytes(uint: u64, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
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

/// Write `uint` to the start of `buffer` and return the remaining part of `buffer`.
pub fn usize_encoded_bytes(uint: usize, buffer: &mut [u8]) -> Result<&mut [u8], EncodingError> {
    u64_encoded_bytes(uint as u64, buffer)
}

/// decode a `usize` from `buffer` and return the remaining bytes
pub fn usize_decode(buffer: &[u8]) -> Result<(usize, &[u8]), EncodingError> {
    let [first, rest @ ..] = buffer else {
        todo!("silec had zero bytes")
    };
    let first = *first;
    if first < U16_SIGNIFIER {
        Ok((first.into(), rest))
    } else if first == U16_SIGNIFIER {
        let (out, rest) = decode_u16(buffer)?;
        return Ok((out.into(), rest));
    } else if first == U32_SIGNIFIER {
        let (out, rest) = decode_u32(buffer)?;
        let out: usize = out
            .try_into()
            .map_err(|_e| EncodingError::overflow("u32 is bigger than usize"))?;
        return Ok((out, rest));
    } else {
        let (out, rest) = decode_u64(buffer)?;
        let out: usize = out
            .try_into()
            .map_err(|_e| EncodingError::overflow("u64 is bigger than usize"))?;
        return Ok((out, rest));
    }
}

/// Split a slice in two at `mid`. Returns encoding error when `mid` is out of bounds.
pub fn get_slices_checked(buffer: &[u8], mid: usize) -> Result<(&[u8], &[u8]), EncodingError> {
    buffer.split_at_checked(mid).ok_or_else(|| {
        EncodingError::out_of_bounds(&format!(
            "Cound not read [{mid}] bytes from buffer of length [{}]",
            buffer.len()
        ))
    })
}
fn get_slices_mut_checked(
    buffer: &mut [u8],
    mid: usize,
) -> Result<(&mut [u8], &mut [u8]), EncodingError> {
    let len = buffer.len();
    buffer.split_at_mut_checked(mid).ok_or_else(|| {
        EncodingError::out_of_bounds(&format!(
            "Cound not read [{mid}] bytes from buffer of length [{len}]"
        ))
    })
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
            "Could not write [{}] bytes to buffer of length [{}]",
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
    let (mut dest, rest) = get_slices_mut_checked(buffer, mid)?;
    dest.copy_from_slice(source);
    Ok(rest)
}

fn encoded_size_str(value: &str) -> Result<usize, EncodingError> {
    Ok(usize_encoded_size(value.len()) + value.len())
}

/// Helper to convert a vec to an array, and fail with an encoding error when needed
pub fn bytes_fixed_from_vec<const N: usize>(value: &[u8]) -> Result<[u8; N], EncodingError> {
    <[u8; N]>::try_from(value).map_err(|e| {
        EncodingError::invalid_data(&format!(
            "Could not covert vec with length [{}] to array of length [{}]",
            value.len(),
            N
        ))
    })
}

/// Encoded a fixed sized array to a buffer
pub fn encode_bytes_fixed<'a, const N: usize>(
    value: &[u8; N],
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    write_array(value, buffer)
}

/// Encoded a fixed sized array to a buffer
pub fn decode_bytes_fixed<const N: usize>(
    buffer: &[u8],
) -> Result<([u8; N], &[u8]), EncodingError> {
    take_array(buffer)
    //write_array(value, buffer)
}

impl<const N: usize> CompactEncodable for [u8; N] {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(N)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        write_array(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        take_array(buffer)
    }
}

fn decode_u16(buffer: &[u8]) -> Result<(u16, &[u8]), EncodingError> {
    let (data, rest) = take_array::<2>(buffer)?;
    Ok(((data[0] as u16) | ((data[1] as u16) << 8), rest))
}

fn decode_u32(buffer: &[u8]) -> Result<(u32, &[u8]), EncodingError> {
    let (data, rest) = take_array::<4>(buffer)?;
    Ok((
        ((data[0] as u32)
            | ((data[1] as u32) << 8)
            | ((data[2] as u32) << 16)
            | ((data[3] as u32) << 24)),
        rest,
    ))
}

fn decode_u64(buffer: &[u8]) -> Result<(u64, &[u8]), EncodingError> {
    let (data, rest) = take_array::<8>(buffer)?;
    Ok((
        ((data[0] as u64)
            | ((data[1] as u64) << 8)
            | ((data[2] as u64) << 16)
            | ((data[3] as u64) << 24)
            | ((data[4] as u64) << 32)
            | ((data[5] as u64) << 40)
            | ((data[6] as u64) << 48)
            | ((data[7] as u64) << 56)),
        rest,
    ))
}

fn decode_u8(buffer: &[u8]) -> Result<(u8, &[u8]), EncodingError> {
    let (data, rest) = take_array::<1>(buffer)?;
    Ok((data[0], rest))
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
        U16_SIGNIFIER => map_first!(decode_u16(rest)?, |x: u16| Ok(x.into())),
        U32_SIGNIFIER => map_first!(decode_u32(rest)?, |x: u32| Ok(x.into())),
        _ => decode_u64(rest)?,
    })
}

fn decode_usize_var(buffer: &[u8]) -> Result<(usize, &[u8]), EncodingError> {
    let ([first], rest) = take_array::<1>(buffer)?;
    Ok(match first {
        x if x < U16_SIGNIFIER => (x.into(), rest),
        U16_SIGNIFIER => map_first!(decode_u16(rest)?, |x: u16| Ok(x.into())),
        U32_SIGNIFIER => {
            map_first!(decode_u32(rest)?, |val| usize::try_from(val).map_err(
                |_| EncodingError::overflow("Could not convert u32 to usize")
            ))
        }
        _ => {
            map_first!(decode_u64(rest)?, |val| usize::try_from(val).map_err(
                |_| EncodingError::overflow("Could not convert u64 to usize")
            ))
        }
    })
}

fn decode_buffer_vec(buffer: &[u8]) -> Result<(Vec<u8>, &[u8]), EncodingError> {
    let (n_bytes, rest) = decode_usize_var(buffer)?;
    let (out, rest) = get_slices_checked(rest, n_bytes)?;
    Ok((out.to_vec(), rest))
}

fn decode_string(buffer: &[u8]) -> Result<(String, &[u8]), EncodingError> {
    let (len, rest) = decode_usize_var(buffer)?;
    let (str_buff, rest) = get_slices_checked(rest, len)?;
    let out = String::from_utf8(str_buff.to_vec())
        .map_err(|e| EncodingError::invalid_data(&format!("String is invalid UTF-8, {e}")))?;
    Ok((out, rest))
}

fn decode_string_array(buffer: &[u8]) -> Result<(Vec<String>, &[u8]), EncodingError> {
    let (len, mut rest) = decode_usize_var(buffer)?;
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        let next = decode_string(rest)?;
        out.push(next.0);
        rest = next.1;
    }
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

fn encode_usize_var<'a>(
    value: &usize,
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    if *value < U16_SIGNIFIER.into() {
        encode_u8(*value as u8, buffer)
    } else if *value <= 0xffff {
        encode_u16(*value as u16, write_array(&[U16_SIGNIFIER], buffer)?)
    } else if *value <= 0xffffffff {
        let value = u32::try_from(*value).map_err(|e| {
            EncodingError::overflow(&format!("count not covert usize [{value}] to u32"))
        })?;
        encode_u32(value, write_array(&[U32_SIGNIFIER], buffer)?)
    } else {
        let value = u64::try_from(*value).map_err(|e| {
            EncodingError::overflow(&format!("count not covert usize [{value}] to u64"))
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

fn encode_string_array<'a>(
    value: &[String],
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    let mut rest = encode_usize_var(&value.len(), buffer)?;
    for s in value {
        rest = encode_str(s, rest)?;
    }
    Ok(rest)
}

impl CompactEncodable for u16 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(U16_SIZE)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_u16(*self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u16(buffer)
    }
}
impl CompactEncodable for u32 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(usize_encoded_size(*self as usize))
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_usize_var(&(*self as usize), buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u32(buffer)
    }
}
impl CompactEncodable for u64 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(u64_var_encoded_size(*self))
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        u64_encoded_bytes(*self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_u64(buffer)
    }
}

impl CompactEncodable for String {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        encoded_size_str(self)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_str(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_string(buffer)
    }
}

impl CompactEncodable for Vec<String> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        let mut out = usize_encoded_size(self.len());
        for s in self {
            out += s.encoded_size()?;
        }
        Ok(out)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        let mut rest = usize_encoded_bytes(self.len(), buffer)?;
        for s in self {
            rest = s.encoded_bytes(rest)?;
        }
        Ok(rest)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (len, mut rest) = decode_usize_var(buffer)?;
        let mut out = Vec::with_capacity(len);
        for _ in 0..len {
            let result = String::decode(rest)?;
            out.push(result.0);
            rest = result.1;
        }
        Ok((out, rest))
    }
}

impl CompactEncodable for Vec<u8> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(usize_encoded_size(self.len()) + self.len())
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        encode_buffer(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        decode_buffer_vec(buffer)
    }
}

fn encode_vec<'a, T: CompactEncodable + Sized>(
    vec: &[T],
    buffer: &'a mut [u8],
) -> Result<&'a mut [u8], EncodingError> {
    let mut rest = encode_usize_var(&vec.len(), buffer)?;
    for x in vec {
        rest = <T as CompactEncodable>::encoded_bytes(x, rest)?;
    }
    Ok(rest)
}

fn decode_vec<T: CompactEncodable + Sized>(
    buffer: &[u8],
) -> Result<(Vec<T>, &[u8]), EncodingError> {
    let (len, mut rest) = decode_usize_var(buffer)?;
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        let res = <T as CompactEncodable>::decode(rest)?;
        out.push(res.0);
        rest = res.1;
    }
    Ok((out, rest))
}

impl<T: VecEncodable> CompactEncodable for Vec<T> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        T::vec_encoded_size(self)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        <T as VecEncodable>::encoded_bytes(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        <T as VecEncodable>::decode(buffer)
    }
}

impl VecEncodable for u32 {
    fn vec_encoded_size(vec: &[Self]) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(usize_encoded_size(vec.len()) + (vec.len() * 4))
    }
}

impl CompactEncodable for u8 {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        Ok(1)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
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

impl BoxArrayEncodable for u8 {
    fn boxed_array_encoded_size(boxed: &Box<[Self]>) -> Result<usize, EncodingError>
    where
        Self: Sized,
    {
        Ok(usize_encoded_size(boxed.len()) + boxed.len())
    }

    fn encoded_bytes<'a>(
        boxed: &Box<[Self]>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8], EncodingError>
    where
        Self: Sized,
    {
        let rest = encode_usize_var(&boxed.len(), buffer)?;
        write_slice(boxed, rest)
    }

    fn decode(buffer: &[u8]) -> Result<(Box<[Self]>, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        let (len, rest) = decode_usize_var(buffer)?;
        let (out, rest) = get_slices_checked(rest, len)?;
        Ok((out.into(), rest))
    }
}

impl<T: BoxArrayEncodable> CompactEncodable for Box<[T]> {
    fn encoded_size(&self) -> Result<usize, EncodingError> {
        T::boxed_array_encoded_size(self)
    }

    fn encoded_bytes<'a>(&self, buffer: &'a mut [u8]) -> Result<&'a mut [u8], EncodingError> {
        <T as BoxArrayEncodable>::encoded_bytes(self, buffer)
    }

    fn decode(buffer: &[u8]) -> Result<(Self, &[u8]), EncodingError>
    where
        Self: Sized,
    {
        <T as BoxArrayEncodable>::decode(buffer)
    }
}

#[cfg(test)]
#[allow(unused)]
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
            let mut buffer = vec![0; usize_encoded_size($value)];
            assert_eq!(buffer.len(), $size);
            let remaining = encode_usize_var(&$value, &mut buffer)?;
            assert!(remaining.is_empty());
            let (result, rest) = decode_usize_var(&buffer)?;
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
}
