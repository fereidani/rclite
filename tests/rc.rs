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

#[cfg(feature = "enum-ptr")]
#[test]
fn aligned() {
    // alignment: bool < ucount
    assert_eq!(<Rc<bool> as enum_ptr::Aligned>::ALIGNMENT, 4);
    // alignment: u128 > ucount
    assert_eq!(<Rc<u128> as enum_ptr::Aligned>::ALIGNMENT, 16);
}
