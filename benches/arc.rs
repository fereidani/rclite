use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rclite::Arc as RcliteArc;
use std::sync::Arc;

// A simple struct to test reference counting
#[derive(Debug)]
struct TestStruct {
    x: u8,
    y: u8,
}

fn create_arc_benchmark(c: &mut Criterion) {
    c.bench_function("rclite::Arc::new", |b| {
        b.iter(|| {
            let data = black_box([42; 1024]);

            RcliteArc::new(data)
        })
    });
    c.bench_function("std::sync::Arc::new", |b| {
        b.iter(|| {
            let data = black_box([42; 1024]);

            Arc::new(data)
        })
    });
}

fn clone_arc_benchmark(c: &mut Criterion) {
    let std_arc = Arc::new([42; 1024]);
    let rclite_arc = RcliteArc::new([42; 1024]);
    c.bench_function("rclite::Arc::clone", |b| {
        b.iter(|| RcliteArc::clone(&rclite_arc))
    });
    c.bench_function("std::sync::Arc::clone", |b| b.iter(|| Arc::clone(&std_arc)));
}

fn drop_arc_benchmark(c: &mut Criterion) {
    let std_arc = Arc::new([42; 1024]);
    let rclite_arc = RcliteArc::new([42; 1024]);
    c.bench_function("rclite::Arc::drop", |b| {
        b.iter(|| {
            let cloned = RcliteArc::clone(&rclite_arc);
            std::mem::drop(black_box(cloned));
        })
    });
    c.bench_function("std::sync::Arc::drop", |b| {
        b.iter(|| {
            let cloned = Arc::clone(&std_arc);
            std::mem::drop(black_box(cloned));
        })
    });
}

// Benchmark accessing fields of a reference-counted object
fn access_arc_benchmark(c: &mut Criterion) {
    let obj = Arc::new(black_box(TestStruct { x: 0, y: 0 }));
    let rclite_obj = RcliteArc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("rclite::Arc::access", |b| {
        b.iter(|| {
            let x = black_box(rclite_obj.x);
            let y = black_box(rclite_obj.y);
            assert_eq!(x, 0);
            assert_eq!(y, 0);
            (x, y)
        })
    });
    c.bench_function("std::sync::Arc::access", |b| {
        b.iter(|| {
            let x = black_box(obj.x);
            let y = black_box(obj.y);
            assert_eq!(x, 0);
            assert_eq!(y, 0);
            (x, y)
        })
    });
}

criterion_group!(
    arc_bench,
    access_arc_benchmark,
    create_arc_benchmark,
    clone_arc_benchmark,
    drop_arc_benchmark
);
criterion_main!(arc_bench);
