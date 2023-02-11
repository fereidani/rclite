extern crate alloc;
use crate::ucount;
use alloc::boxed::Box;
use core::{cell::UnsafeCell, fmt, marker::PhantomData, ops::Deref, ptr};

struct RcInner<T> {
    data: T,
    counter: UnsafeCell<ucount>,
}

/// Rc<T> is a reference-counting pointer for single-threaded use. It provides
/// shared ownership of a value of type T that is stored in the heap. When you
/// clone an Rc, it creates a new pointer to the same heap allocation. When the
/// last Rc pointer to the allocation is destroyed, the stored value is also
/// dropped.
pub struct Rc<T> {
    ptr: ptr::NonNull<RcInner<T>>,
    phantom: PhantomData<Box<RcInner<T>>>,
}

impl<T> Rc<T> {
    /// Constructs a new `Rc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let tada = Rc::new("Tada!");
    /// ```
    #[inline(always)]
    pub fn new(data: T) -> Rc<T> {
        let inner = Box::new(RcInner {
            data,
            counter: UnsafeCell::new(1),
        });
        Rc {
            ptr: Box::leak(inner).into(),
            phantom: PhantomData,
        }
    }
    #[inline(always)]
    fn inner(&self) -> &RcInner<T> {
        // SAFETY: inner is protected by counter, it will not get released unless drop
        // of the last owner get called.
        unsafe { self.ptr.as_ref() }
    }
    unsafe fn decrease_counter(&self) -> ucount {
        let counter = &mut *self.inner().counter.get();
        *counter -= 1;
        *counter
    }
    unsafe fn increase_counter(&self) -> ucount {
        let counter = &mut *self.inner().counter.get();
        *counter = counter.wrapping_add(1);
        *counter
    }
}

impl<T> Deref for Rc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner().data
    }
}

impl<T> From<T> for Rc<T> {
    #[inline(always)]
    fn from(value: T) -> Self {
        Rc::new(value)
    }
}

impl<T> Clone for Rc<T> {
    fn clone(&self) -> Self {
        // SAFETY: counter is ensured to be used in single threaded environment only
        let counter = unsafe { self.increase_counter() };
        if counter == 0 {
            panic!("reference counter overflow");
        }
        Self {
            ptr: self.ptr,
            phantom: self.phantom,
        }
    }
}

impl<T> Drop for Rc<T> {
    fn drop(&mut self) {
        // SAFETY: counter is ensured to be used in single threaded environment only
        let counter = unsafe { self.decrease_counter() };
        if counter == 0 {
            unsafe { Box::from_raw(self.ptr.as_mut()) };
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Rc<T>")
    }
}
