use criterion::{black_box, criterion_group, criterion_main, Criterion};
use mexset::MexSet;

fn basics_u128() {
    let mut set: MexSet<u128> = MexSet::new();
    for x in 0..10000 {
        set.insert(x);
        set.minimum_excluded();
    }

    for x in 0..10000 {
        set.remove(&x);
        set.minimum_excluded();
    }
}

fn basics_u64() {
    let mut set: MexSet<u64> = MexSet::new();
    for x in 0..10000 {
        set.insert(x);
        set.minimum_excluded();
    }

    for x in 0..10000 {
        set.remove(&x);
        set.minimum_excluded();
    }
}

fn basics_u32() {
    let mut set: MexSet<u32> = MexSet::new();
    for x in 0..10000 {
        set.insert(x);
        set.minimum_excluded();
    }

    for x in 0..10000 {
        set.remove(&x);
        set.minimum_excluded();
    }
}

fn basics_u16() {
    let mut set: MexSet<u16> = MexSet::new();
    for x in 0..10000 {
        set.insert(x);
        set.minimum_excluded();
    }

    for x in 0..10000 {
        set.remove(&x);
        set.minimum_excluded();
    }
}

fn with_range_u128() {
    MexSet::<u128>::with_range(10000);
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("basics u128", |b| b.iter(|| black_box(basics_u128())));
    c.bench_function("basics u64", |b| b.iter(|| black_box(basics_u64())));
    c.bench_function("basics u32", |b| b.iter(|| black_box(basics_u32())));
    c.bench_function("basics u16", |b| b.iter(|| black_box(basics_u16())));
    c.bench_function("with_range_u128", |b| b.iter(|| black_box(with_range_u128())));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);