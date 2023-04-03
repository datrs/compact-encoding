use std::time::Instant;

use compact_encoding::{CompactEncoding, State};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

const U32_VALUE: u32 = 0xF0E1D2C3;
const STR_VALUE: &str = "foo";
const U64_VALUE: u64 = u64::MAX;

fn preencode() -> State {
    let mut enc_state = State::new();
    enc_state.preencode(&U32_VALUE).unwrap();
    enc_state.preencode_str(STR_VALUE).unwrap();
    enc_state.preencode(&U64_VALUE).unwrap();
    enc_state
}

fn encode(enc_state: &mut State, buffer: &mut [u8]) {
    enc_state.encode(&U32_VALUE, buffer).unwrap();
    enc_state.encode_str(STR_VALUE, buffer).unwrap();
    enc_state.encode(&U64_VALUE, buffer).unwrap();
}

fn decode(dec_state: &mut State, buffer: &[u8]) {
    let _: u32 = dec_state.decode(buffer).unwrap();
    let _: String = dec_state.decode(buffer).unwrap();
    let _: u64 = dec_state.decode(buffer).unwrap();
}

fn preencode_generic_simple(c: &mut Criterion) {
    c.bench_function("preencode generic simple", |b| {
        b.iter(preencode);
    });
}

fn create_buffer_generic_simple(c: &mut Criterion) {
    c.bench_function("create buffer generic simple", |b| {
        b.iter_custom(|iters| {
            let enc_state = preencode();
            let start = Instant::now();
            for _ in 0..iters {
                black_box(enc_state.create_buffer());
            }
            start.elapsed()
        });
    });
}

#[allow(clippy::unit_arg)]
fn encode_generic_simple(c: &mut Criterion) {
    c.bench_function("encode generic simple", |b| {
        b.iter_custom(|iters| {
            let enc_state = preencode();
            let buffer = enc_state.create_buffer();
            let start = Instant::now();
            for _ in 0..iters {
                let mut enc_state = enc_state.clone();
                let mut buffer = buffer.clone();
                black_box(encode(&mut enc_state, &mut buffer));
            }
            start.elapsed()
        });
    });
}

#[allow(clippy::unit_arg)]
fn decode_generic_simple(c: &mut Criterion) {
    c.bench_function("decode generic simple", |b| {
        b.iter_custom(|iters| {
            let mut enc_state = preencode();
            let mut buffer = enc_state.create_buffer();
            encode(&mut enc_state, &mut buffer);
            let dec_state = State::from_buffer(&buffer);
            let start = Instant::now();
            for _ in 0..iters {
                let mut dec_state = dec_state.clone();
                let buffer = buffer.clone();
                black_box(decode(&mut dec_state, &buffer));
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
