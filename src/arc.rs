use crate::{ucount, AtomicCounter};
use alloc::boxed::Box;
use core::{fmt, marker::PhantomData, ops::Deref, pin::Pin, ptr::NonNull, sync::atomic::Ordering};

// The barrier prevents the counter value from overflowing, ensuring that
// dropping an [`Arc<T>`] won't cause an incorrect drop of the `ArcInner` and a
// dangling pointer for other references. The barrier allows enough space
// between overflows based on the max possible number of CPU cores in the
// system, making it impossible for an [`Arc<T>`] counter to actually overflow to 1,
// no matter how many concurrent overflows occur. so if after panic thread
// unwinds, other threads can safely continue using their own Arc references.
#[cfg(target_pointer_width = "64")]
const BARRIER: ucount = 256;
#[cfg(target_pointer_width = "32")]
const BARRIER: ucount = 8;
#[cfg(target_pointer_width = "16")]
const BARRIER: ucount = 0;
#[cfg(target_pointer_width = "8")]
const BARRIER: ucount = 0;

struct ArcInner<T> {
    data: T,
    counter: AtomicCounter,
}

/// The [`Arc<T>`] type represents a thread-safe reference-counting pointer,
/// where "Arc" stands for "Atomically Reference Counted". It provides shared
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
/// [`Arc<T>`] is a thread-safe reference-counting pointer, meaning it's safe to
/// use in multithreaded environments. However, this comes at a cost, as atomic
/// operations are slower than regular memory accesses. If you're not sharing
/// reference-counted values between threads, consider using
/// [`Rc<T>`][`crate::Rc<T>`] instead, which has lower overhead.
///
/// [`Arc<T>`] can be used with [Send] and [Sync] types only, so make sure that
/// the type T you're using with it implements these traits. Keep in mind that
/// [`Arc<T>`] only ensures thread safety for the reference count, not the data
/// stored in it. To make the data itself thread-safe, you may need to pair
/// [`Arc<T>`] with a `Send`+`Sync` type, such as `std::sync::Mutex<T>`.
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
// [`Arc<T>`] can be used as if it were of type T by using the [Deref][deref] trait. To call methods
// of [`Arc<T>`], use fully qualified syntax, such as Arc::clone(). You can also call traits like
// Clone on [`Arc<T>`] using fully qualified syntax. The choice between using fully qualified syntax
// or method-call syntax is a matter of personal preference.
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
    ptr: NonNull<ArcInner<T>>,
    phantom: PhantomData<Box<T>>,
}

unsafe impl<T: Sync + Send> Send for Arc<T> {}
unsafe impl<T: Sync + Send> Sync for Arc<T> {}

impl<T> Arc<T> {
    /// Constructs a new [`Arc<T>`].
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

    /// Constructs a new `Pin<Arc<T>>`. If `T` does not implement `Unpin`, then
    /// `data` will be pinned in memory and unable to be moved.
    #[inline(always)]
    #[must_use]
    pub fn pin(data: T) -> Pin<Arc<T>> {
        unsafe { Pin::new_unchecked(Arc::new(data)) }
    }

    /// Gives you a pointer to the data. The reference count stays the same and
    /// the [`Arc<T>`] isn't used up. The pointer stays valid as long as there are
    /// strong references to the [`Arc<T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let x = Arc::new("hello".to_owned());
    /// let y = Arc::clone(&x);
    /// let x_ptr = Arc::as_ptr(&x);
    /// assert_eq!(x_ptr, Arc::as_ptr(&y));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        // SAFETY: ptr is valid, as self is a valid instance of [`Arc<T>`]
        self.ptr.as_ptr() as *const T
    }

    /// Turns [`Arc<T>`] into a raw pointer, must be converted back to [`Arc<T>`] with
    /// [`Arc::from_raw`] to avoid memory leak.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let x = Arc::new("hello".to_owned());
    /// let x_ptr = Arc::into_raw(x);
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// // reconstruct arc to drop the reference and avoid memory leaks
    /// unsafe { Arc::from_raw(x_ptr) };
    /// ```
    pub fn into_raw(this: Self) -> *const T {
        let ptr = Self::as_ptr(&this);
        core::mem::forget(this);
        ptr
    }

    /// Constructs an [`Arc<T>`] from a raw pointer. The raw pointer must have
    /// been from [`Arc<U>::into_raw`] where U and T must have the same size
    /// and alignment. Improper use may lead to memory unsafe operations.
    ///
    /// # Safety
    /// It's only safe to construct back references that are generated with
    /// [`Arc::into_raw`], converting any other references may lead to undefined
    /// behaivior.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let x = Arc::new("hello".to_owned());
    /// let x_ptr = Arc::into_raw(x);
    ///
    /// unsafe {
    ///     // Convert back to an [`Arc<T>`] to prevent leak.
    ///     let x = Arc::from_raw(x_ptr);
    ///     assert_eq!(&*x, "hello");
    ///
    ///     // Further calls to [`Arc::from_raw(x_ptr)`] would be memory-unsafe.
    /// }
    ///
    /// // The memory was freed when `x` went out of scope above, so `x_ptr` is now dangling!
    /// ```
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        // SAFETY: ptr offset is same as ArcInner struct offset no recalculation of
        // offset is required
        Arc {
            ptr: NonNull::new_unchecked(ptr as *mut ArcInner<T>),
            phantom: PhantomData,
        }
    }

    /// Gets the number of strong pointers to an allocation. Be careful as
    /// another thread can change the count at any time.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let five = Arc::new(5);
    /// let _also_five = Arc::clone(&five);
    ///
    /// // This assertion is deterministic because we haven't shared
    /// // the [`Arc<T>`] between threads.
    /// assert_eq!(2, Arc::strong_count(&five));
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn strong_count(&self) -> ucount {
        self.inner().counter.load(Ordering::Acquire)
    }

    /// Compares if two Arcs reference the same allocation, similar to ptr::eq.
    /// Note: The same caveats apply when comparing dyn Trait pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let five = Arc::new(5);
    /// let same_five = Arc::clone(&five);
    /// let other_five = Arc::new(5);
    ///
    /// assert!(Arc::ptr_eq(&five, &same_five));
    /// assert!(!Arc::ptr_eq(&five, &other_five));
    /// ```
    ///
    /// [`ptr::eq`]: core::ptr::eq "ptr::eq"
    #[inline(always)]
    #[must_use]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr.as_ptr() == other.ptr.as_ptr()
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
    #[inline(always)]
    fn clone(&self) -> Self {
        if self.inner().counter.fetch_add(1, Ordering::Relaxed) >= ucount::MAX - BARRIER {
            // turn back the counter to its initial state as this function will not return a
            // valid [`Arc<T>`]
            self.inner().counter.fetch_sub(1, Ordering::Relaxed);
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
