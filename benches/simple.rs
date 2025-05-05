use std::time::Instant;

use compact_encoding::{map_decode, map_encode, sum_encoded_size, CompactEncoding, EncodingError};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

const U32_VALUE: u32 = 0xF0E1D2C3;
const STR_VALUE: &str = "foo";
const U64_VALUE: u64 = u64::MAX;

fn preencode() -> Result<usize, EncodingError> {
    Ok(sum_encoded_size!(U32_VALUE, STR_VALUE, U64_VALUE))
}

fn encode(buffer: &mut [u8]) -> Result<(), EncodingError> {
    let _ = map_encode!(buffer, U32_VALUE, STR_VALUE, U64_VALUE);
    Ok(())
}

fn decode(buffer: &[u8]) -> Result<(), EncodingError> {
    map_decode!(buffer, [u32, String, u64]);
    Ok(())
}

fn create_buffer(encoded_size: usize) -> Box<[u8]> {
    vec![0; encoded_size].into_boxed_slice()
}

fn preencode_generic_simple(c: &mut Criterion) {
    c.bench_function("preencode generic simple", |b| {
        b.iter(preencode);
    });
}

fn create_buffer_generic_simple(c: &mut Criterion) {
    c.bench_function("create buffer generic simple", |b| {
        b.iter_custom(|iters| {
            let encoded_size = preencode().unwrap();
            let start = Instant::now();
            for _ in 0..iters {
                black_box(create_buffer(encoded_size));
            }
            start.elapsed()
        });
    });
}

#[allow(clippy::unit_arg)]
fn encode_generic_simple(c: &mut Criterion) {
    c.bench_function("encode generic simple", |b| {
        b.iter_custom(|iters| {
            let encoded_size = preencode().unwrap();
            let buffer = create_buffer(encoded_size);
            let start = Instant::now();
            for _ in 0..iters {
                let mut buffer = buffer.clone();
                black_box(encode(&mut buffer).unwrap());
            }
            start.elapsed()
        });
    });
}

#[allow(clippy::unit_arg)]
fn decode_generic_simple(c: &mut Criterion) {
    c.bench_function("decode generic simple", |b| {
        b.iter_custom(|iters| {
            let encoded_size = preencode().unwrap();
            let mut buffer = vec![0_u8; encoded_size];
            encode(&mut buffer).unwrap();
            let start = Instant::now();
            for _ in 0..iters {
                let buffer = buffer.clone();
                black_box(decode(&buffer).unwrap());
            }
            start.elapsed()
        });
    });
}

criterion_group!(
    benches,
    preencode_generic_simple,
    create_buffer_generic_simple,
    encode_generic_simple,
    decode_generic_simple,
);
criterion_main!(benches);
