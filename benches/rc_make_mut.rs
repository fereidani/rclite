use criterion::{criterion_group, criterion_main, Criterion};
use rclite::Rc as RcLite;
use std::rc::Rc;

fn bench_rc_make_mut_unique(c: &mut Criterion) {
    {
        let mut rc = RcLite::new(42);
        c.bench_function("rclite_make_mut_unique", |b| {
            b.iter(|| {
                let mut_ref = RcLite::make_mut(&mut rc);
                *mut_ref = !*mut_ref;
            })
        });
    }
    {
        let mut rc = Rc::new(42);
        c.bench_function("rc_make_mut_unique", |b| {
            b.iter(|| {
                let mut_ref = Rc::make_mut(&mut rc);
                *mut_ref = !*mut_ref;
            })
        });
    }
}

fn bench_rc_make_mut_not_unique(c: &mut Criterion) {
    {
        let rc = RcLite::new(42);

        c.bench_function("rclite_make_mut_not_unique", |b| {
            b.iter(|| {
                let mut rc_clone = RcLite::clone(&rc);
                let mut_ref = RcLite::make_mut(&mut rc_clone);
                //assert_eq!(*mut_ref, 42);
                *mut_ref = !*mut_ref;
            })
        });

        assert_eq!(*rc, 42);
    }
    {
        let rc = Rc::new(42);

        c.bench_function("rc_make_mut_not_unique", |b| {
            b.iter(|| {
                let mut rc_clone = Rc::clone(&rc);
                let mut_ref = Rc::make_mut(&mut rc_clone);
                //assert_eq!(*mut_ref, 42);
                *mut_ref = !*mut_ref;
            })
        });
        assert_eq!(*rc, 42);
        //assert_eq!(*rc_clone, 42);
    }
}

criterion_group!(
    benches,
    bench_rc_make_mut_unique,
    bench_rc_make_mut_not_unique,
);

criterion_main!(benches);
