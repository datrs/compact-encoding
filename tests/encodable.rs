use compact_encoding::{
    encodable::{create_buffer, map_encode, CompactEncodable},
    map_decode, map_encodables,
    types::EncodingError,
};

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
    assert_eq!(result.0, data[0]);
    assert_eq!(result.1, data[1]);
    assert_eq!(result.2, data[2]);
    Ok(())
}
