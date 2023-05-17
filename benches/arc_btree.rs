use criterion::{criterion_group, criterion_main, Criterion};
macro_rules! create_test {
    ($Arc:ident) => {
        use criterion::black_box;
        use rayon::prelude::*;
        #[derive(Clone)]
        struct Node {
            left: Option<$Arc<Node>>,
            right: Option<$Arc<Node>>,
        }

        const MIN_DEPTH: u32 = 4;

        fn trees(max_depth: u32) -> $Arc<Node> {
            let long_lasting_node = create_tree(max_depth);
            (4..=max_depth).step_by(2).for_each(|depth| {
                let iterations = 1 << (max_depth - depth + MIN_DEPTH);
                let check = loops(iterations, depth);
                black_box(check);
            });

            black_box(check_tree(long_lasting_node.clone()));
            long_lasting_node
        }

        fn loops(iterations: u32, depth: u32) -> u32 {
            (0..iterations)
                .into_par_iter()
                .map(|_| check_tree(create_tree(depth)))
                .sum()
        }

        fn check_tree(node: $Arc<Node>) -> u32 {
            node.left
                .clone()
                .zip(node.right.clone())
                .map_or(1, |(left, right)| check_tree(left) + check_tree(right) + 1)
        }

        fn create_tree(depth: u32) -> $Arc<Node> {
            if depth > 0 {
                $Arc::new(Node {
                    left: Some(create_tree(depth - 1)),
                    right: Some(create_tree(depth - 1)),
                })
            } else {
                $Arc::new(Node {
                    left: None,
                    right: None,
                })
            }
        }
    };
}
fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("rclite_arc_btree", |b| {
        use rclite::Arc;
        create_test!(Arc);
        b.iter(|| {
            drop(trees(16));
        })
    });
    c.bench_function("std_arc_btree", |b| {
        use std::sync::Arc;
        create_test!(Arc);
        b.iter(|| {
            drop(trees(16));
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
