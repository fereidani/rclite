use rclite::Rc;

#[test]
fn simple() {
    let a = Rc::new(!0usize);
    drop(a);
}

#[test]
fn cloned() {
    let a = Rc::new(!0usize);
    let _b = a.clone();
    let _c = a.clone();
    let _d = a;
}
