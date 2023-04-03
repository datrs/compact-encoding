//! Generic compact encodings
use crate::EncodingErrorKind;

use super::{CompactEncoding, EncodingError, State};

impl CompactEncoding<String> for State {
    fn preencode(&mut self, value: &String) -> Result<usize, EncodingError> {
        self.preencode_str(value)
    }

    fn encode(&mut self, value: &String, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_str(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<String, EncodingError> {
        self.decode_string(buffer)
    }
}

impl CompactEncoding<u8> for State {
    fn preencode(&mut self, _: &u8) -> Result<usize, EncodingError> {
        self.add_end(1)
    }

    fn encode(&mut self, value: &u8, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        buffer[self.start()] = *value;
        self.add_start(1)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<u8, EncodingError> {
        let value = buffer[self.start()];
        self.add_start(1)?;
        Ok(value)
    }
}

impl CompactEncoding<u32> for State {
    fn preencode(&mut self, value: &u32) -> Result<usize, EncodingError> {
        self.preencode_uint_var(value)
    }

    fn encode(&mut self, value: &u32, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_u32_var(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<u32, EncodingError> {
        self.decode_u32_var(buffer)
    }
}

impl CompactEncoding<u64> for State {
    fn preencode(&mut self, value: &u64) -> Result<usize, EncodingError> {
        self.preencode_uint_var(value)
    }

    fn encode(&mut self, value: &u64, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_u64_var(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<u64, EncodingError> {
        self.decode_u64_var(buffer)
    }
}

impl CompactEncoding<usize> for State {
    fn preencode(&mut self, value: &usize) -> Result<usize, EncodingError> {
        self.preencode_usize_var(value)
    }

    fn encode(&mut self, value: &usize, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_usize_var(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<usize, EncodingError> {
        self.decode_usize_var(buffer)
    }
}

impl CompactEncoding<Box<[u8]>> for State {
    fn preencode(&mut self, value: &Box<[u8]>) -> Result<usize, EncodingError> {
        self.preencode_buffer(value)
    }

    fn encode(&mut self, value: &Box<[u8]>, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_buffer(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<Box<[u8]>, EncodingError> {
        self.decode_buffer(buffer)
    }
}

impl CompactEncoding<Vec<u8>> for State {
    fn preencode(&mut self, value: &Vec<u8>) -> Result<usize, EncodingError> {
        self.preencode_buffer_vec(value)
    }

    fn encode(&mut self, value: &Vec<u8>, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_buffer(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<Vec<u8>, EncodingError> {
        self.decode_buffer_vec(buffer)
    }
}

impl CompactEncoding<Vec<u32>> for State {
    fn preencode(&mut self, value: &Vec<u32>) -> Result<usize, EncodingError> {
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

    fn encode(&mut self, value: &Vec<u32>, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        let len = value.len();
        self.encode_usize_var(&len, buffer)?;
        for entry in value {
            self.encode_u32(*entry, buffer)?;
        }
        Ok(self.start())
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<Vec<u32>, EncodingError> {
        let len = self.decode_usize_var(buffer)?;
        let mut value: Vec<u32> = Vec::with_capacity(len);
        for _ in 0..len {
            value.push(self.decode_u32(buffer)?);
        }
        Ok(value)
    }
}

impl CompactEncoding<Vec<String>> for State {
    fn preencode(&mut self, value: &Vec<String>) -> Result<usize, EncodingError> {
        self.preencode_string_array(value)
    }

    fn encode(&mut self, value: &Vec<String>, buffer: &mut [u8]) -> Result<usize, EncodingError> {
        self.encode_string_array(value, buffer)
    }

    fn decode(&mut self, buffer: &[u8]) -> Result<Vec<String>, EncodingError> {
        self.decode_string_array(buffer)
    }
}
