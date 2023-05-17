use criterion::{criterion_group, criterion_main, Criterion};

macro_rules! create_test {
    ($Rc:ident) => {
        #[derive(Debug)]
        pub struct Node<T> {
            value: T,
            left: Option<$Rc<Node<T>>>,
            right: Option<$Rc<Node<T>>>,
        }

        impl<T> Node<T> {
            pub fn new(value: T) -> Self {
                Self {
                    value,
                    left: None,
                    right: None,
                }
            }
        }

        pub fn create_tree(depth: i32) -> $Rc<Node<i32>> {
            if depth == 0 {
                return $Rc::new(Node::new(0));
            }
            $Rc::new(Node {
                value: depth,
                left: Some(create_tree(depth - 1)),
                right: Some(create_tree(depth - 1)),
            })
        }

        pub fn tree_traversal(node: &$Rc<Node<i32>>) -> i32 {
            let mut sum = node.value;
            if let Some(left) = &node.left {
                sum += tree_traversal(left);
            }
            if let Some(right) = &node.right {
                sum += tree_traversal(right);
            }
            sum
        }
    };
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("binary-tree rclite::Rc", |b| {
        use rclite::Rc;
        create_test!(Rc);
        let tree = create_tree(20);
        b.iter(|| tree_traversal(&tree))
    });
    c.bench_function("binary-tree std::Rc", |b| {
        use std::rc::Rc;
        create_test!(Rc);
        let tree = create_tree(20);
        b.iter(|| tree_traversal(&tree))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
