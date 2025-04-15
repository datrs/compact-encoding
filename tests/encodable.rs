use compact_encoding::{
    create_buffer,
    encodable::{create_buffer, CompactEncoding},
    map_decode, map_encodables,
    types::EncodingError,
};

// The max value for 1 byte length is 252
const MAX_ONE_BYTE_UINT: u8 = 252;

// The min value for 2 byte length is 253
const MIN_TWO_BYTE_UINT: u8 = 253;

#[test]
fn cenc_basic() -> Result<(), EncodingError> {
    let str_value_1 = "foo";
    let str_value_2 = (0..MAX_ONE_BYTE_UINT).map(|_| "X").collect::<String>();
    let u32_value_3: u32 = u32::MAX;
    let u32_value_4: u32 = 0xF0E1D2C3;

    let mut buff = create_buffer!(str_value_1, str_value_2, u32_value_3, u32_value_4);
    assert_eq!(buff.len(), 1 + 3 + 1 + 252 + 1 + 4 + 1 + 4);

    let rest = map_encodables!(
        &mut buff,
        str_value_1,
        str_value_2,
        u32_value_3,
        u32_value_4
    );
    assert!(rest.is_empty());
    let (result, remaning_buff) = map_decode!(&buff, [String, String, u32, u32]);
    assert!(remaning_buff.is_empty());

    assert_eq!(result.0, str_value_1);
    assert_eq!(result.1, str_value_2);
    assert_eq!(result.2, u32_value_3);
    assert_eq!(result.3, u32_value_4);
    Ok(())
}

#[test]
fn cenc_string_long() -> Result<(), EncodingError> {
    let value = (0..MIN_TWO_BYTE_UINT).map(|_| "X").collect::<String>();
    assert_eq!(value.len(), 253);
    let mut buffer = create_buffer!(value);
    assert_eq!(buffer.len(), 1 + 2 + 253);

    let rest = map_encodables!(&mut buffer, value);
    assert!(rest.is_empty());

    let ((result,), rest) = map_decode!(&buffer, [String]);
    assert!(rest.is_empty());
    assert_eq!(result, value);
    Ok(())
}

#[test]
fn cenc_u32_as_u16() -> Result<(), EncodingError> {
    let value: u32 = u16::MAX.into();
    let mut buffer = create_buffer!(value);
    // 1 byte for u16 signifier, 2 bytes for length
    assert_eq!(buffer.len(), 1 + 2);
    let rest = map_encodables!(&mut buffer, value);
    assert!(rest.is_empty());

    let ((result,), rest) = map_decode!(&buffer, [u32]);
    assert!(rest.is_empty());
    assert_eq!(result, value);
    Ok(())
}

#[test]
fn cenc_u32_as_u8() -> Result<(), EncodingError> {
    let value: u32 = MAX_ONE_BYTE_UINT.into();
    let mut buffer = create_buffer!(value);
    // 1 byte for data
    assert_eq!(buffer.len(), 1);
    let rest = map_encodables!(&mut buffer, value);
    assert!(rest.is_empty());

    let ((result,), rest) = map_decode!(&buffer, [u32]);
    assert!(rest.is_empty());
    assert_eq!(result, value);
    Ok(())
}

#[test]
fn cenc_u64() -> Result<(), EncodingError> {
    let value: u64 = 0xF0E1D2C3B4A59687;
    let mut buffer = create_buffer!(value);
    // 1 byte for u64 signifier, 8 bytes for length
    assert_eq!(buffer.len(), 1 + 8);
    let rest = map_encodables!(&mut buffer, value);
    assert!(rest.is_empty());
    let ((result,), rest) = map_decode!(&buffer, [u64]);
    assert!(rest.is_empty());
    assert_eq!(result, value);
    Ok(())
}

#[test]
fn cenc_u64_as_u32() -> Result<(), EncodingError> {
    let value: u64 = u32::MAX.into();
    let mut buffer = create_buffer!(value);
    // 1 byte for u32 signifier, 4 bytes for length
    assert_eq!(buffer.len(), 1 + 4);
    let rest = map_encodables!(&mut buffer, value);
    assert!(rest.is_empty());
    let ((result,), rest) = map_decode!(&buffer, [u64]);
    assert!(rest.is_empty());
    assert_eq!(result, value);
    Ok(())
}

#[test]
fn cenc_buffer() -> Result<(), EncodingError> {
    let buf_value_1 = vec![0xFF, 0x00].into_boxed_slice();
    let buf_value_2 = vec![0xEE, 0x11, 0x22].into_boxed_slice();

    let mut buffer = create_buffer!(buf_value_1, buf_value_2);
    // 1 byte for length, 2 bytes for data
    // 1 byte for length, 3 bytes for data
    assert_eq!(buffer.len(), 1 + 2 + 1 + 3);
    let rest = map_encodables!(&mut buffer, buf_value_1, buf_value_2);
    assert!(rest.is_empty());
    let (result, rest) = map_decode!(&buffer, [Box<[u8]>, Box<[u8]>]);
    assert!(rest.is_empty());
    assert_eq!(result.0, buf_value_1);
    assert_eq!(result.1, buf_value_2);
    Ok(())
}

#[test]
fn cenc_vec() -> Result<(), EncodingError> {
    let buf_value_1: Vec<u8> = vec![0xFF, 0x00];
    let buf_value_2: Vec<u32> = vec![0xFFFFFFFF, 0x11223344, 0x99887766];

    let mut buffer = create_buffer!(buf_value_1, buf_value_2);
    // 1 byte for length, 2 bytes for data
    // 1 byte for length, 4*3 bytes for data
    assert_eq!(buffer.len(), 1 + 2 + 1 + 12);

    let rest = map_encodables!(&mut buffer, buf_value_1, buf_value_2);
    assert!(rest.is_empty());
    let (result, rest) = map_decode!(&buffer, [Vec<u8>, Vec<u32>]);
    assert!(rest.is_empty());
    assert_eq!(result.0, buf_value_1);
    assert_eq!(result.1, buf_value_2);
    Ok(())
}

#[test]
fn cenc_string_array() -> Result<(), EncodingError> {
    let value = vec!["first".to_string(), "second".to_string()];
    let mut buffer = create_buffer!(value);
    // 1 byte for array length,
    // 1 byte for string length, 5 bytes for string,
    // 1 byte for string length, 6 bytes for string
    assert_eq!(buffer.len(), 1 + 1 + 5 + 1 + 6);
    let rest = map_encodables!(&mut buffer, value);
    assert!(rest.is_empty());
    let ((result,), rest) = map_decode!(&buffer, [Vec<String>]);
    assert!(rest.is_empty());
    assert_eq!(result, value);
    Ok(())
}

#[test]
fn cenc_fixed_and_raw() -> Result<(), EncodingError> {
    let buf_value_1: [u8; 16] = [0xEE; 16];
    let buf_value_2: [u8; 32] = [0xFF; 32];
    let buf_value_3: [u8; 3] = [0xFF, 0x11, 0x99];

    let mut buffer = create_buffer!(buf_value_1, buf_value_2, buf_value_3);
    // 1 byte for length, 2 bytes for data
    // 1 byte for length, 4*3 bytes for data
    assert_eq!(buffer.len(), 16 + 32 + 3);

    let rest = map_encodables!(&mut buffer, buf_value_1, buf_value_2, buf_value_3);
    assert!(rest.is_empty());
    let (result, rest) = map_decode!(&buffer, [[u8; 16], [u8; 32], [u8; 3]]);
    assert!(rest.is_empty());
    assert_eq!(result.0, buf_value_1);
    assert_eq!(result.1, buf_value_2);
    assert_eq!(result.2, buf_value_3);
    Ok(())
}

#[test]
fn cenc_32_byte_array() -> Result<(), EncodingError> {
    let empty_array: Vec<[u8; 32]> = vec![];
    let one_array: Vec<[u8; 32]> = vec![[0; 32]];
    let many_array: Vec<[u8; 32]> = vec![[1; 32], [2; 32], [3; 32]];
    let data = vec![empty_array.clone(), one_array.clone(), many_array.clone()];
    let expected_size = 1 + 1 + 32 + 1 + (3 * 32);

    let mut buffer = create_buffer(&data)?;
    assert_eq!(buffer.len(), expected_size);

    let rest = map_encodables!(&mut buffer, empty_array, one_array, many_array);
    assert!(rest.is_empty());

    let (result, rest) = map_decode!(&buffer, [Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<[u8;32]>]);
    assert!(rest.is_empty());
    assert_eq!(result.0, data[0]);
    assert_eq!(result.1, data[1]);
    assert_eq!(result.2, data[2]);
    Ok(())
}
