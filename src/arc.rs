use crate::{ucount, AtomicCounter};
use alloc::boxed::Box;
use core::{
    cell::UnsafeCell,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Deref,
    pin::Pin,
    ptr::NonNull,
    sync::atomic::{fence, Ordering},
};

// The barrier prevents the counter value from overflowing, ensuring that
// dropping an [`Arc<T>`] won't cause an incorrect drop of the `ArcInner` and a
// dangling pointer for other references. The barrier allows enough space
// between overflows based on the max possible number of CPU cores in the
// system, making it impossible for an [`Arc<T>`] counter to actually overflow
// to 1, no matter how many concurrent overflows occur. so if after panic thread
// unwinds, other threads can safely continue using their own Arc references.
#[cfg(target_pointer_width = "64")]
const BARRIER: ucount = 256;
#[cfg(target_pointer_width = "32")]
const BARRIER: ucount = 8;

#[repr(C)]
struct ArcInner<T> {
    data: UnsafeCell<T>,
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
            data: UnsafeCell::new(data),
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
    /// the [`Arc<T>`] isn't used up. The pointer stays valid as long as there
    /// are strong references to the [`Arc<T>`].
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

    /// Turns [`Arc<T>`] into a raw pointer, must be converted back to
    /// [`Arc<T>`] with [`Arc::from_raw`] to avoid memory leak.
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
    #[inline(always)]
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
    #[inline(always)]
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
    pub fn strong_count(&self) -> usize {
        self.inner().counter.load(Ordering::Acquire) as usize
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

    /// If there's only one strong reference, returns the inner value. If not,
    /// returns an error with the Arc passed in.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let x = Arc::new(3);
    /// assert_eq!(Arc::try_unwrap(x).unwrap(), 3);
    ///
    /// let x = Arc::new(4);
    /// let _y = Arc::clone(&x);
    /// assert_eq!(*Arc::try_unwrap(x).unwrap_err(), 4);
    /// ```
    #[inline(always)]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        if Arc::strong_count(&this) == 1 {
            // SAFETY: there is only one reference to Arc it's safe to move out value of T
            // from Arc and destroy the container
            unsafe {
                let inner = Box::from_raw(this.ptr.as_ptr());
                core::mem::forget(this);
                let val = core::ptr::read(inner.data.get());
                core::mem::forget(inner.data);
                Ok(val)
            }
        } else {
            Err(this)
        }
    }

    /// If there's only one reference to T, remove it. Otherwise, make a copy of
    /// T. If rc_t is of type [`Arc<T>`], this function works like
    /// (*rc_t).clone(), but will avoid copying the value if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ptr;
    /// # use rclite::Arc;
    /// let inner = String::from("test");
    /// let ptr = inner.as_ptr();
    ///
    /// let rc = Arc::new(inner);
    /// let inner = Arc::unwrap_or_clone(rc);
    /// // The inner value was not cloned
    /// assert!(ptr::eq(ptr, inner.as_ptr()));
    ///
    /// let rc = Arc::new(inner);
    /// let rc2 = rc.clone();
    /// let inner = Arc::unwrap_or_clone(rc);
    /// // Because there were 2 references, we had to clone the inner value.
    /// assert!(!ptr::eq(ptr, inner.as_ptr()));
    /// // `rc2` is the last reference, so when we unwrap it we get back
    /// // the original `String`.
    /// let inner = Arc::unwrap_or_clone(rc2);
    /// assert!(ptr::eq(ptr, inner.as_ptr()));
    /// ```
    #[inline(always)]
    pub fn unwrap_or_clone(this: Self) -> T
    where
        T: Clone,
    {
        Arc::try_unwrap(this).unwrap_or_else(|rc| (*rc).clone())
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
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*(self.inner().data.get() as *const T) }
    }
}

impl<T> From<T> for Arc<T> {
    #[inline(always)]
    fn from(value: T) -> Self {
        Arc::new(value)
    }
}

#[inline(never)]
fn drop_arc_no_inline<T>(ptr: NonNull<ArcInner<T>>) {
    drop(Arc {
        ptr,
        phantom: PhantomData,
    })
}

impl<T> Clone for Arc<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        if self.inner().counter.fetch_add(1, Ordering::Relaxed) >= ucount::MAX - BARRIER {
            // turn back the counter to its initial state as this function will not return a
            // valid [`Arc<T>`]. It uses `drop_arc_no_inline` to drop value to reduce
            // overhead of clone inlining in user code.
            drop_arc_no_inline(self.ptr);
            panic!("reference counter overflow");
        }
        Self {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T> Drop for Arc<T> {
    #[inline(always)]
    fn drop(&mut self) {
        if self.inner().counter.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }
        fence(Ordering::Acquire);
        // SAFETY: this is the last owner of the ptr, it is safe to drop data
        unsafe { Box::from_raw(self.ptr.as_ptr()) };
    }
}

impl<T: Hash> Hash for Arc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: fmt::Display> fmt::Display for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: fmt::Debug> fmt::Debug for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T> fmt::Pointer for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(&**self as *const T), f)
    }
}

impl<T: Default> Default for Arc<T> {
    #[inline(always)]
    fn default() -> Arc<T> {
        Arc::new(Default::default())
    }
}

impl<T: PartialEq> PartialEq for Arc<T> {
    #[inline(always)]
    fn eq(&self, other: &Arc<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: Eq> Eq for Arc<T> {}

impl<T: PartialOrd> PartialOrd for Arc<T> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Arc<T>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }

    #[inline(always)]
    fn lt(&self, other: &Arc<T>) -> bool {
        **self < **other
    }

    #[inline(always)]
    fn le(&self, other: &Arc<T>) -> bool {
        **self <= **other
    }

    #[inline(always)]
    fn gt(&self, other: &Arc<T>) -> bool {
        **self > **other
    }

    #[inline(always)]
    fn ge(&self, other: &Arc<T>) -> bool {
        **self >= **other
    }
}

impl<T: Ord> Ord for Arc<T> {
    #[inline(always)]
    fn cmp(&self, other: &Arc<T>) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T> Unpin for Arc<T> {}
