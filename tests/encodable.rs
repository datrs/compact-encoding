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
    let _str_value_1 = "foo";
    let str_value_2 = (0..MAX_ONE_BYTE_UINT).map(|_| "X").collect::<String>();
    let u32_value_3: u32 = u32::MAX;
    let u32_value_4: u32 = 0xF0E1D2C3;

    let mut _buff = create_buffer!(str_value_2, u32_value_3, u32_value_4);
    assert_eq!(_buff.len(), 1 + 252 + 1 + 4 + 1 + 4);

    //let rest = map_encodables!(buf, str_value_1, str_value_2, u32_value_3, u32_value_4);
    /*
    // Strings: 1 byte for length, 3/252 bytes for content
    // u32: 1 byte for u32 signifier, 4 bytes for data
    assert_eq!(buffer.len(), 1 + 3 + 1 + 252 + 1 + 4 + 1 + 4);
    enc_state.encode_str(str_value_1, &mut buffer)?;
    enc_state.encode(&str_value_2, &mut buffer)?;
    enc_state.encode(&u32_value_3, &mut buffer)?;
    enc_state.encode(&u32_value_4, &mut buffer)?;
    let mut dec_state = State::from_buffer(&buffer);
    let str_value_1_ret: String = dec_state.decode(&buffer)?;
    assert_eq!(str_value_1, str_value_1_ret);
    let str_value_2_ret: String = dec_state.decode(&buffer)?;
    assert_eq!(str_value_2, str_value_2_ret);
    let u32_value_3_ret: u32 = dec_state.decode(&buffer)?;
    assert_eq!(u32_value_3, u32_value_3_ret);
    let u32_value_4_ret: u32 = dec_state.decode(&buffer)?;
    assert_eq!(u32_value_4, u32_value_4_ret);
    */
    Ok(())
}
