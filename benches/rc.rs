use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rclite::Rc as RcliteRc;
use std::rc::Rc as StdRc;

// A simple struct to test reference counting
#[derive(Debug)]
struct TestStruct {
    x: u8,
    y: u8,
}

// Benchmark the creation of a new reference-counted object
fn new_rc_benchmark(c: &mut Criterion) {
    c.bench_function("rclite::Rc::new", |b| {
        b.iter(|| {
            let obj = RcliteRc::new(black_box(TestStruct { x: 0, y: 0 }));
            black_box(obj)
        })
    });
    c.bench_function("std::rc::Rc::new", |b| {
        b.iter(|| {
            let obj = StdRc::new(black_box(TestStruct { x: 0, y: 0 }));
            black_box(obj)
        })
    });
}

// Benchmark cloning a reference-counted object
fn clone_rc_benchmark(c: &mut Criterion) {
    let rclite_obj = RcliteRc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("rclite::Rc::clone", |b| {
        b.iter(|| {
            let obj_clone = black_box(rclite_obj.clone());
            black_box(obj_clone)
        })
    });
    let obj = StdRc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("std::rc::Rc::clone", |b| {
        b.iter(|| {
            let obj_clone = black_box(obj.clone());
            black_box(obj_clone)
        })
    });
}

// Benchmark dropping a reference-counted object
fn drop_rc_benchmark(c: &mut Criterion) {
    let rclite_obj = RcliteRc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("rclite::Rc::drop", |b| {
        b.iter(|| {
            let obj_clone = black_box(rclite_obj.clone());
            drop(obj_clone);
        })
    });
    let obj = StdRc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("std::rc::Rc::drop", |b| {
        b.iter(|| {
            let obj_clone = black_box(obj.clone());
            drop(obj_clone);
        })
    });
}

// Benchmark accessing fields of a reference-counted object
fn access_rc_benchmark(c: &mut Criterion) {
    println!();

    let rclite_obj = RcliteRc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("rclite::Rc::access", |b| {
        b.iter(|| {
            let x = black_box(rclite_obj.x);
            let y = black_box(rclite_obj.y);
            assert_eq!(x, 0);
            assert_eq!(y, 0);
            (x, y)
        })
    });
    let obj = StdRc::new(black_box(TestStruct { x: 0, y: 0 }));
    c.bench_function("std::rc::Rc::access", |b| {
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
    rc_benches,
    access_rc_benchmark,
    new_rc_benchmark,
    clone_rc_benchmark,
    drop_rc_benchmark,
);

criterion_main!(rc_benches);
