//! Basic types of compact_encoding.
use std::convert::TryFrom;
use std::fmt;
use std::ops::Range;

const U16_SIGNIFIER: u8 = 0xfd;
const U32_SIGNIFIER: u8 = 0xfe;
const U64_SIGNIFIER: u8 = 0xff;

/// Specific type [EncodingError]
#[derive(fmt::Debug)]
pub enum EncodingErrorKind {
    /// Encoding or decoding did not stay between [State] `start` and `end`.
    OutOfBounds,
    /// Buffer data overflowed type during encoding or decoding.
    Overflow,
    /// Buffer contained invalid data during decoding.
    InvalidData,
}

/// Encoding/decoding error.
#[derive(fmt::Debug)]
pub struct EncodingError {
    /// Specific type of error
    pub kind: EncodingErrorKind,
    /// Message for the error
    pub message: String,
}

impl EncodingError {
    /// Create EncodingError
    pub fn new(kind: EncodingErrorKind, message: &str) -> Self {
        Self {
            kind,
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

/// State.
#[derive(Debug, Clone)]
pub struct State {
    /// Start position
    start: usize,
    /// End position
    end: usize,
}

impl Default for State {
    /// Create empty state
    fn default() -> Self {
        Self::new()
    }
}

impl State {
    /// Create empty state
    pub fn new() -> State {
        State::new_with_start_and_end(0, 0)
    }

    /// Create a state and buffer with an already known size.
    /// With this, you can/must skip the preencode step.
    pub fn new_with_size(size: usize) -> (State, Box<[u8]>) {
        (
            State::new_with_start_and_end(0, size),
            vec![0; size].into_boxed_slice(),
        )
    }

    /// Create a state with a start and end already known.
    pub fn new_with_start_and_end(start: usize, end: usize) -> State {
        State { start, end }
    }

    /// Create a state from existing buffer.
    pub fn from_buffer(buffer: &[u8]) -> State {
        State::new_with_start_and_end(0, buffer.len())
    }

    /// Start value
    pub fn start(&self) -> usize {
        self.start
    }

    /// Set start value
    pub fn set_start(&mut self, value: usize) -> Result<(), EncodingError> {
        if value > self.end {
            return Err(EncodingError::new(
                EncodingErrorKind::OutOfBounds,
                &format!("Value exceeded state.end: {} > {}", value, self.end),
            ));
        }
        self.start = value;
        Ok(())
    }

    /// End value
    pub fn end(&self) -> usize {
        self.end
    }

    /// Set end value
    pub fn set_end(&mut self, value: usize) {
        self.end = value;
    }

    /// Add to start handling overflow and out of bounds.
    pub fn add_start(&mut self, increment: usize) -> Result<usize, EncodingError> {
        self.start = self.start.checked_add(increment).ok_or_else(|| {
            EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!(
                    "State.start overflowed: {} + {} > {}",
                    self.start,
                    increment,
                    usize::MAX
                ),
            )
        })?;
        if self.start > self.end {
            Err(EncodingError::new(
                EncodingErrorKind::OutOfBounds,
                &format!(
                    "State.start exceeded state.end: {} > {}",
                    self.start, self.end
                ),
            ))
        } else {
            Ok(self.start)
        }
    }

    /// Add to end handling overflow
    pub fn add_end(&mut self, increment: usize) -> Result<usize, EncodingError> {
        self.end = self.end.checked_add(increment).ok_or_else(|| {
            EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!(
                    "State.end overflowed: {} + {} > {}",
                    self.end,
                    increment,
                    usize::MAX
                ),
            )
        })?;
        Ok(self.end)
    }

    /// After calling preencode(), this allocates the right size buffer to the heap.
    /// Follow this with the same number of encode() steps to fill the created buffer.
    pub fn create_buffer(&self) -> Box<[u8]> {
        vec![0; self.end].into_boxed_slice()
    }

    /// Safely set single byte to buffer at state.start and then increment state.start, returning
    /// new state.start.
    pub fn set_byte_to_buffer(
        &mut self,
        value: u8,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        if buffer.len() <= self.start {
            Err(EncodingError::new(
                EncodingErrorKind::OutOfBounds,
                &format!(
                    "Length of buffer {} too small to fit single byte",
                    buffer.len()
                ),
            ))
        } else {
            buffer[self.start] = value;
            self.add_start(1)
        }
    }

    /// Safely set byte slice to buffer at state.start and then increment state.start with slice
    /// length, returning new state.start.
    pub fn set_slice_to_buffer(
        &mut self,
        value: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.set_slice_to_buffer_fixed(value, buffer, value.len())
    }

    /// Safely set byte slice of fixed len to buffer at state.start and then increment state.start with slice
    /// length, returning new state.start.
    pub fn set_slice_to_buffer_fixed(
        &mut self,
        value: &[u8],
        buffer: &mut [u8],
        size: usize,
    ) -> Result<usize, EncodingError> {
        if value.len() < size {
            return Err(EncodingError::new(
                EncodingErrorKind::OutOfBounds,
                &format!(
                    "Length of value {} too small to fit fixed size {}",
                    value.len(),
                    size
                ),
            ));
        }
        let value_end = size.checked_add(self.start).ok_or_else(|| {
            EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!(
                    "Value end overflowed: {} + {} > {}",
                    size,
                    self.start,
                    usize::MAX
                ),
            )
        })?;
        if buffer.len() < value_end {
            Err(EncodingError::new(
                EncodingErrorKind::OutOfBounds,
                &format!(
                    "Length of buffer {} too small to fit slice of length {}",
                    buffer.len(),
                    size
                ),
            ))
        } else {
            buffer[self.start..value_end].copy_from_slice(value);
            self.add_start(size)
        }
    }

    /// Validate `size` can be decoded from `buffer`, return current start.
    pub fn validate(&mut self, size: usize, buffer: &[u8]) -> Result<Range<usize>, EncodingError> {
        let value_end = size.checked_add(self.start).ok_or_else(|| {
            EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!(
                    "Value end overflowed during validate: {} + {} > {}",
                    size,
                    self.start,
                    usize::MAX
                ),
            )
        })?;

        if buffer.len() < value_end {
            Err(EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!("Buffer length {} too small for size {}", buffer.len(), size,),
            ))
        } else {
            Ok(self.start..value_end)
        }
    }

    /// Preencode a string slice
    pub fn preencode_str(&mut self, value: &str) -> Result<usize, EncodingError> {
        self.preencode_usize_var(&value.len())?;
        self.add_end(value.len())
    }

    /// Encode a string slice
    pub fn encode_str(&mut self, value: &str, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        let len = value.len();
        self.encode_usize_var(&len, buffer)?;
        self.set_slice_to_buffer(value.as_bytes(), buffer)
    }

    /// Decode a String
    pub fn decode_string(&mut self, buffer: &[u8]) -> Result<String, EncodingError> {
        let len = self.decode_usize_var(buffer)?;
        let range = self.validate(len, buffer)?;
        let value = std::str::from_utf8(&buffer[range]).map_err(|err| {
            EncodingError::new(
                EncodingErrorKind::InvalidData,
                &format!("String is invalid UTF-8, {err}"),
            )
        })?;
        self.add_start(len)?;
        Ok(value.to_string())
    }

    /// Preencode a variable length usigned int
    pub fn preencode_uint_var<T: From<u32> + Ord>(
        &mut self,
        uint: &T,
    ) -> Result<usize, EncodingError> {
        let increment: usize = if *uint < T::from(U16_SIGNIFIER.into()) {
            1
        } else if *uint <= T::from(0xffff) {
            3
        } else if *uint <= T::from(0xffffffff) {
            5
        } else {
            9
        };
        self.add_end(increment)
    }

    /// Decode a fixed length u8
    pub fn decode_u8(&mut self, buffer: &[u8]) -> Result<u8, EncodingError> {
        self.validate(1, buffer)?;
        let value: u8 = buffer[self.start];
        self.add_start(1)?;
        Ok(value)
    }

    /// Decode a fixed length u16
    pub fn decode_u16(&mut self, buffer: &[u8]) -> Result<u16, EncodingError> {
        self.validate(2, buffer)?;
        let value: u16 = (buffer[self.start] as u16) | ((buffer[self.start + 1] as u16) << 8);
        self.add_start(2)?;
        Ok(value)
    }

    /// Encode a variable length u32
    pub fn encode_u32_var(
        &mut self,
        value: &u32,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        if *value < U16_SIGNIFIER.into() {
            let bytes = value.to_le_bytes();
            self.set_byte_to_buffer(bytes[0], buffer)
        } else if *value <= 0xffff {
            self.set_byte_to_buffer(U16_SIGNIFIER, buffer)?;
            self.encode_uint16_bytes(&value.to_le_bytes(), buffer)
        } else {
            self.set_byte_to_buffer(U32_SIGNIFIER, buffer)?;
            self.encode_uint32_bytes(&value.to_le_bytes(), buffer)
        }
    }

    /// Encode u32 to 4 LE bytes.
    pub fn encode_u32(&mut self, uint: u32, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_uint32_bytes(&uint.to_le_bytes(), buffer)
    }

    /// Decode a variable length u32
    #[allow(clippy::comparison_chain)]
    pub fn decode_u32_var(&mut self, buffer: &[u8]) -> Result<u32, EncodingError> {
        self.validate(1, buffer)?;
        let first = buffer[self.start];
        self.add_start(1)?;
        if first < U16_SIGNIFIER {
            Ok(first.into())
        } else if first == U16_SIGNIFIER {
            Ok(self.decode_u16(buffer)?.into())
        } else {
            self.decode_u32(buffer)
        }
    }

    /// Decode a fixed length u32
    pub fn decode_u32(&mut self, buffer: &[u8]) -> Result<u32, EncodingError> {
        self.validate(4, buffer)?;
        let value: u32 = (buffer[self.start] as u32)
            | ((buffer[self.start + 1] as u32) << 8)
            | ((buffer[self.start + 2] as u32) << 16)
            | ((buffer[self.start + 3] as u32) << 24);
        self.add_start(4)?;
        Ok(value)
    }

    /// Encode a variable length u64
    pub fn encode_u64_var(
        &mut self,
        value: &u64,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        if *value < U16_SIGNIFIER.into() {
            let bytes = value.to_le_bytes();
            self.set_byte_to_buffer(bytes[0], buffer)
        } else if *value <= 0xffff {
            self.set_byte_to_buffer(U16_SIGNIFIER, buffer)?;
            self.encode_uint16_bytes(&value.to_le_bytes(), buffer)
        } else if *value <= 0xffffffff {
            self.set_byte_to_buffer(U32_SIGNIFIER, buffer)?;
            self.encode_uint32_bytes(&value.to_le_bytes(), buffer)
        } else {
            self.set_byte_to_buffer(U64_SIGNIFIER, buffer)?;
            self.encode_uint64_bytes(&value.to_le_bytes(), buffer)
        }
    }

    /// Encode u64 to 8 LE bytes.
    pub fn encode_u64(&mut self, uint: u64, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_uint64_bytes(&uint.to_le_bytes(), buffer)
    }

    /// Decode a variable length u64
    pub fn decode_u64_var(&mut self, buffer: &[u8]) -> Result<u64, EncodingError> {
        self.validate(1, buffer)?;
        let first = buffer[self.start];
        self.add_start(1)?;
        if first < U16_SIGNIFIER {
            Ok(first.into())
        } else if first == U16_SIGNIFIER {
            Ok(self.decode_u16(buffer)?.into())
        } else if first == U32_SIGNIFIER {
            Ok(self.decode_u32(buffer)?.into())
        } else {
            self.decode_u64(buffer)
        }
    }

    /// Decode a fixed length u64
    pub fn decode_u64(&mut self, buffer: &[u8]) -> Result<u64, EncodingError> {
        self.validate(8, buffer)?;
        let value: u64 = (buffer[self.start] as u64)
            | ((buffer[self.start + 1] as u64) << 8)
            | ((buffer[self.start + 2] as u64) << 16)
            | ((buffer[self.start + 3] as u64) << 24)
            | ((buffer[self.start + 4] as u64) << 32)
            | ((buffer[self.start + 5] as u64) << 40)
            | ((buffer[self.start + 6] as u64) << 48)
            | ((buffer[self.start + 7] as u64) << 56);
        self.add_start(8)?;
        Ok(value)
    }

    /// Preencode a byte buffer
    pub fn preencode_buffer(&mut self, value: &[u8]) -> Result<usize, EncodingError> {
        let len = value.len();
        self.preencode_usize_var(&len)?;
        self.add_end(len)
    }

    /// Preencode a vector byte buffer
    pub fn preencode_buffer_vec(&mut self, value: &Vec<u8>) -> Result<usize, EncodingError> {
        let len = value.len();
        self.preencode_usize_var(&len)?;
        self.add_end(len)
    }

    /// Encode a byte buffer
    pub fn encode_buffer(
        &mut self,
        value: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        let len = value.len();
        self.encode_usize_var(&len, buffer)?;
        self.set_slice_to_buffer(value, buffer)
    }

    /// Decode a byte buffer
    pub fn decode_buffer(&mut self, buffer: &[u8]) -> Result<Box<[u8]>, EncodingError> {
        Ok(self.decode_buffer_vec(buffer)?.into_boxed_slice())
    }

    /// Decode a vector byte buffer
    pub fn decode_buffer_vec(&mut self, buffer: &[u8]) -> Result<Vec<u8>, EncodingError> {
        let len = self.decode_usize_var(buffer)?;
        let range = self.validate(len, buffer)?;
        let value = buffer[range].to_vec();
        self.add_start(value.len())?;
        Ok(value)
    }

    /// Preencode a raw byte buffer. Only possible to use if this is the last value
    /// of the State.
    pub fn preencode_raw_buffer(&mut self, value: &Vec<u8>) -> Result<usize, EncodingError> {
        self.add_end(value.len())
    }

    /// Encode a raw byte buffer. Only possible to use if this is the last value
    /// of the State.
    pub fn encode_raw_buffer(
        &mut self,
        value: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.set_slice_to_buffer(value, buffer)
    }

    /// Decode a raw byte buffer. Only possible to use if this is the last value
    /// of the State.
    pub fn decode_raw_buffer(&mut self, buffer: &[u8]) -> Result<Vec<u8>, EncodingError> {
        if self.start >= self.end {
            return Err(EncodingError::new(
                EncodingErrorKind::OutOfBounds,
                &format!("State.start {} >= state.end {}", self.start, self.end),
            ));
        }
        let range = self.validate(self.end - self.start, buffer)?;
        let value = buffer[range].to_vec();
        self.start = self.end;
        Ok(value)
    }

    /// Preencode a fixed 16 byte buffer
    pub fn preencode_fixed_16(&mut self) -> Result<usize, EncodingError> {
        self.add_end(16)
    }

    /// Encode a fixed 16 byte buffer
    pub fn encode_fixed_16(
        &mut self,
        value: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.set_slice_to_buffer_fixed(value, buffer, 16)
    }

    /// Decode a fixed 16 byte buffer
    pub fn decode_fixed_16(&mut self, buffer: &[u8]) -> Result<Box<[u8]>, EncodingError> {
        let range = self.validate(16, buffer)?;
        let value = buffer[range].to_vec().into_boxed_slice();
        self.add_start(16)?;
        Ok(value)
    }

    /// Preencode a fixed 32 byte buffer
    pub fn preencode_fixed_32(&mut self) -> Result<usize, EncodingError> {
        self.add_end(32)
    }

    /// Encode a fixed 32 byte buffer
    pub fn encode_fixed_32(
        &mut self,
        value: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.set_slice_to_buffer_fixed(value, buffer, 32)
    }

    /// Decode a fixed 32 byte buffer
    pub fn decode_fixed_32(&mut self, buffer: &[u8]) -> Result<Box<[u8]>, EncodingError> {
        let range = self.validate(32, buffer)?;
        let value = buffer[range].to_vec().into_boxed_slice();
        self.add_start(32)?;
        Ok(value)
    }

    /// Preencode a string array
    pub fn preencode_string_array(&mut self, value: &Vec<String>) -> Result<usize, EncodingError> {
        let len = value.len();
        self.preencode_usize_var(&len)?;
        for string_value in value.iter() {
            self.preencode_str(string_value)?;
        }
        Ok(self.end)
    }

    /// Encode a String array
    pub fn encode_string_array(
        &mut self,
        value: &Vec<String>,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        let len = value.len();
        self.encode_usize_var(&len, buffer)?;
        for string_value in value {
            self.encode_str(string_value, buffer)?;
        }
        Ok(self.end)
    }

    /// Decode a String array
    pub fn decode_string_array(&mut self, buffer: &[u8]) -> Result<Vec<String>, EncodingError> {
        let len = self.decode_usize_var(buffer)?;
        let mut value = Vec::with_capacity(len);
        for _ in 0..len {
            value.push(self.decode_string(buffer)?);
        }
        Ok(value)
    }

    /// Preencode an u32 array
    pub fn preencode_u32_array(&mut self, value: &Vec<u32>) -> Result<usize, EncodingError> {
        let len = value.len();
        self.preencode_usize_var(&len)?;
        let total_len = len.checked_mul(4).ok_or_else(|| {
            EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!(
                    "Vec<u32> total length overflowed: {} * 4 > {}",
                    len,
                    usize::MAX
                ),
            )
        })?;
        self.add_end(total_len)
    }

    /// Encode an u32 array
    pub fn encode_u32_array(
        &mut self,
        value: &Vec<u32>,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        let len = value.len();
        self.encode_usize_var(&len, buffer)?;
        for entry in value {
            self.encode_u32(*entry, buffer)?;
        }
        Ok(self.start())
    }

    /// Decode an u32 array
    pub fn decode_u32_array(&mut self, buffer: &[u8]) -> Result<Vec<u32>, EncodingError> {
        let len = self.decode_usize_var(buffer)?;
        let mut value: Vec<u32> = Vec::with_capacity(len);
        for _ in 0..len {
            value.push(self.decode_u32(buffer)?);
        }
        Ok(value)
    }

    /// Preencode a fixed 32 byte value array
    pub fn preencode_fixed_32_array(
        &mut self,
        value: &Vec<[u8; 32]>,
    ) -> Result<usize, EncodingError> {
        let len = value.len();
        self.preencode(&len)?;
        let size = len.checked_mul(32).ok_or_else(|| {
            EncodingError::new(
                EncodingErrorKind::Overflow,
                &format!(
                    "Vec<[u8; 32]> byte size overflowed: {} * 32 > {}",
                    len,
                    usize::MAX
                ),
            )
        })?;
        self.add_end(size)?;
        Ok(self.end())
    }

    /// Encode a fixed 32 byte value array
    pub fn encode_fixed_32_array(
        &mut self,
        value: &Vec<[u8; 32]>,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.encode(&value.len(), buffer)?;
        for entry in value {
            self.set_slice_to_buffer_fixed(entry, buffer, 32)?;
        }
        Ok(self.start())
    }

    /// Decode a fixed 32 byte value array
    pub fn decode_fixed_32_array(&mut self, buffer: &[u8]) -> Result<Vec<[u8; 32]>, EncodingError> {
        let len: usize = self.decode(buffer)?;
        let mut entries: Vec<[u8; 32]> = Vec::with_capacity(len);
        for _ in 0..len {
            let range = self.validate(32, buffer)?;
            entries.push(buffer[range].try_into().map_err(|err| {
                EncodingError::new(
                    EncodingErrorKind::InvalidData,
                    &format!("Could not convert byte slice to [u8; 32], {err}"),
                )
            })?);
            self.add_start(32)?;
        }
        Ok(entries)
    }

    /// Preencode a variable length usize
    pub fn preencode_usize_var(&mut self, value: &usize) -> Result<usize, EncodingError> {
        // This repeats the logic from above that works for u8 -> u64, but sadly not usize
        let increment: usize = if *value < U16_SIGNIFIER.into() {
            1
        } else if *value <= 0xffff {
            3
        } else if *value <= 0xffffffff {
            5
        } else {
            9
        };
        self.add_end(increment)
    }

    /// Encode a variable length usize
    pub fn encode_usize_var(
        &mut self,
        value: &usize,
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        if *value < U16_SIGNIFIER.into() {
            let bytes = value.to_le_bytes();
            self.set_byte_to_buffer(bytes[0], buffer)
        } else if *value <= 0xffff {
            self.set_byte_to_buffer(U16_SIGNIFIER, buffer)?;
            self.encode_uint16_bytes(&value.to_le_bytes(), buffer)
        } else if *value <= 0xffffffff {
            self.set_byte_to_buffer(U32_SIGNIFIER, buffer)?;
            self.encode_uint32_bytes(&value.to_le_bytes(), buffer)
        } else {
            self.set_byte_to_buffer(U64_SIGNIFIER, buffer)?;
            self.encode_uint64_bytes(&value.to_le_bytes(), buffer)
        }
    }

    /// Decode a variable length usize.
    pub fn decode_usize_var(&mut self, buffer: &[u8]) -> Result<usize, EncodingError> {
        self.validate(1, buffer)?;
        let first = buffer[self.start];
        self.add_start(1)?;
        // NB: the from_le_bytes needs a [u8; 2] and that can't be efficiently
        // created from a byte slice.
        if first < U16_SIGNIFIER {
            Ok(first.into())
        } else if first == U16_SIGNIFIER {
            Ok(self.decode_u16(buffer)?.into())
        } else if first == U32_SIGNIFIER {
            usize::try_from(self.decode_u32(buffer)?).map_err(|_| {
                EncodingError::new(
                    EncodingErrorKind::Overflow,
                    "Attempted converting to a 32 bit usize on below 32 bit system",
                )
            })
        } else {
            usize::try_from(self.decode_u64(buffer)?).map_err(|_| {
                EncodingError::new(
                    EncodingErrorKind::Overflow,
                    "Attempted converting to a 64 bit usize on below 64 bit system",
                )
            })
        }
    }

    /// Encode a 2 byte unsigned integer. NB: assumes `bytes` buffer large enough, hence not public!
    fn encode_uint16_bytes(
        &mut self,
        bytes: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.set_slice_to_buffer(&bytes[..2], buffer)
    }

    /// Encode a 4 byte unsigned integer. NB: assumes `bytes` buffer large enough, hence not public!
    fn encode_uint32_bytes(
        &mut self,
        bytes: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.encode_uint16_bytes(bytes, buffer)?;
        self.set_slice_to_buffer(&bytes[2..4], buffer)
    }

    /// Encode an 8 byte unsigned integer. NB: assumes `bytes` buffer large enough, hence not public!
    fn encode_uint64_bytes(
        &mut self,
        bytes: &[u8],
        buffer: &mut [u8],
    ) -> Result<usize, EncodingError> {
        self.encode_uint32_bytes(bytes, buffer)?;
        self.set_slice_to_buffer(&bytes[4..8], buffer)
    }
}

/// Compact Encoding
pub trait CompactEncoding<T>
where
    T: fmt::Debug,
{
    /// Preencode
    fn preencode(&mut self, value: &T) -> Result<usize, EncodingError>;

    /// Encode
    fn encode(&mut self, value: &T, buffer: &mut [u8]) -> Result<usize, EncodingError>;

    /// Decode
    fn decode(&mut self, buffer: &[u8]) -> Result<T, EncodingError>;
}
