use std::{thread, time::Duration};

use rclite::Arc;

#[test]
fn simple() {
    let a = Arc::new(!0usize);
    drop(a);
}

#[test]
fn multithread() {
    let a = Arc::new(!0usize);
    for _ in 0..8 {
        let a = a.clone();
        thread::spawn(move || {
            if *a != !0 {
                panic!("Whaaat, invalid somehow?")
            }
        });
    }
    std::thread::sleep(Duration::from_millis(100));
}

#[test]
fn multi_multithread() {
    let a = Arc::new(!0usize);
    for _ in 0..8 {
        let a = a.clone();
        thread::spawn(move || {
            for _ in 0..8 {
                let a = a.clone();
                thread::spawn(move || {
                    if *a != !0 {
                        panic!("Whaaat, invalid somehow?")
                    }
                });
            }
        });
    }
    std::thread::sleep(Duration::from_millis(100));
}
