extern crate alloc;
use crate::{ucount, AtomicCounter};
use alloc::boxed::Box;
use core::{fmt, marker::PhantomData, ops::Deref, ptr, sync::atomic::Ordering};

struct ArcInner<T> {
    data: T,
    counter: AtomicCounter,
}

/// The Arc<T> type represents a thread-safe reference-counting pointer, where
/// "Arc" stands for "Atomically Reference Counted". It provides shared
/// ownership of a value of type T, stored on the heap. When you call the clone
/// method on Arc, a new instance of Arc is created that points to the same heap
/// allocation as the original Arc, and the reference count is increased. Once
/// the last Arc pointer to a given allocation is destroyed, the inner value
/// stored in that allocation is also dropped.
///
/// Because shared references in Rust are read-only by default, you cannot
/// modify the value stored inside an Arc. If you need to modify it, use the
/// Mutex, RwLock, or one of the Atomic types.
///
/// Please note that this type is only available on platforms that support
/// atomic loads and stores of pointers, which includes all platforms that
/// support the std crate but not those that only support the alloc crate. You
/// can check if a platform supports this type at compile time by using the
/// #[cfg(target_has_atomic ="ptr")] attribute.
///
/// ## Thread Safety
///
/// Arc<T> is a thread-safe reference-counting pointer, meaning it's safe to use
/// in multithreaded environments. However, this comes at a cost, as atomic
/// operations are slower than regular memory accesses. If you're not sharing
/// reference-counted values between threads, consider using Rc<T> instead,
/// which has lower overhead.
///
/// Arc<T> can be used with [Send] and [Sync] types only, so make sure that the
/// type T you're using with it implements these traits. Keep in mind that
/// Arc<T> only ensures thread safety for the reference count, not the data
/// stored in it. To make the data itself thread-safe, you may need to pair
/// Arc<T> with a [std::sync] type, such as [Mutex<T>][mutex].
///
/// # Cloning references
///
/// Creating a new reference from an existing reference-counted pointer is done
/// using the `Clone` trait implemented for [`Arc<T>`][Arc]
///
/// ```
/// use rclite::Arc;
/// let foo = Arc::new(vec![1.0, 2.0, 3.0]);
/// // The two syntaxes below are equivalent.
/// let a = foo.clone();
/// let b = Arc::clone(&foo);
/// // a, b, and foo are all Arcs that point to the same memory location
/// ```
// Arc<T> can be used as if it were of type T by using the [Deref][deref] trait. To call methods of
// Arc<T>, use fully qualified syntax, such as Arc::clone(). You can also call traits like Clone on
// Arc<T> using fully qualified syntax. The choice between using fully qualified syntax or
// method-call syntax is a matter of personal preference.
///
/// ```
/// use rclite::Arc;
///
/// let arc = Arc::new(());
/// // Method-call syntax
/// let arc2 = arc.clone();
/// // Fully qualified syntax
/// let arc3 = Arc::clone(&arc);
/// ```
pub struct Arc<T> {
    ptr: ptr::NonNull<ArcInner<T>>,
    phantom: PhantomData<Box<T>>,
}

unsafe impl<T: Sync + Send> Send for Arc<T> {}
unsafe impl<T: Sync + Send> Sync for Arc<T> {}

impl<T> Arc<T> {
    /// Constructs a new `Arc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let tada = Arc::new("Tada!".to_string());
    /// ```
    #[inline(always)]
    pub fn new(data: T) -> Arc<T> {
        let inner = Box::new(ArcInner {
            data,
            counter: AtomicCounter::new(1),
        });
        Arc {
            ptr: Box::leak(inner).into(),
            phantom: PhantomData,
        }
    }
    #[inline(always)]
    fn inner(&self) -> &ArcInner<T> {
        // SAFETY: inner is protected by counter, it will not get released unless drop
        // of the last owner get called.
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> Deref for Arc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner().data
    }
}

impl<T> From<T> for Arc<T> {
    #[inline(always)]
    fn from(value: T) -> Self {
        Arc::new(value)
    }
}

impl<T> Clone for Arc<T> {
    fn clone(&self) -> Self {
        if self.inner().counter.fetch_add(1, Ordering::Relaxed) == ucount::MAX {
            panic!("reference counter overflow");
        }
        Self {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T> Drop for Arc<T> {
    fn drop(&mut self) {
        if self.inner().counter.fetch_sub(1, Ordering::AcqRel) == 1 {
            // SAFETY: this is the last owner of the ptr, it is safe to drop data
            unsafe { Box::from_raw(self.ptr.as_ptr()) };
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Arc<T>")
    }
}
