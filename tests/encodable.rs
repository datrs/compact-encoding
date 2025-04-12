use compact_encoding::{
    create_buffer,
    encodable::{create_buffer, CompactEncodable},
    map_decode, map_encodables,
    types::EncodingError,
};

// The max value for 1 byte length is 252
const MAX_ONE_BYTE_UINT: u8 = 252;

// The min value for 2 byte length is 253
const _MIN_TWO_BYTE_UINT: u8 = 253;

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

    let (result, rest) = map_decode!(&buffer, [Vec<[u8; 32]>, Vec<[u8; 32]>, Vec<[u8;32]>])?;
    assert!(rest.is_empty());
    assert_eq!(result.0, data[0]);
    assert_eq!(result.1, data[1]);
    assert_eq!(result.2, data[2]);
    Ok(())
}

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
    let (result, remaning_buff) = map_decode!(&buff, [String, String, u32, u32])?;
    dbg!(remaning_buff);
    assert!(remaning_buff.is_empty());

    assert_eq!(result.0, str_value_1);
    assert_eq!(result.1, str_value_2);
    assert_eq!(result.2, u32_value_3);
    assert_eq!(result.3, u32_value_4);
    Ok(())
}
