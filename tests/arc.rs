use std::{thread, time::Duration};

use rclite::Arc;

#[test]
fn simple() {
    let a = Arc::new(!0usize);
    drop(a);
}

#[cfg(miri)]
const THREAD_COUNT: usize = 2;
#[cfg(not(miri))]
const THREAD_COUNT: usize = 8;

#[test]
fn multithread() {
    let a = Arc::new(!0usize);
    for _ in 0..THREAD_COUNT {
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
    for _ in 0..THREAD_COUNT {
        let a = a.clone();
        thread::spawn(move || {
            for _ in 0..THREAD_COUNT {
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
