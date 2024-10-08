use crate::{ucount, AtomicCounter};
use alloc::{alloc::dealloc, boxed::Box};
use branches::unlikely;
use core::{
    alloc::Layout,
    cell::UnsafeCell,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
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
const BARRIER: ucount = 512;
#[cfg(target_pointer_width = "32")]
const BARRIER: ucount = 64;

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
/// [`Arc<T>`] with a `Send`+`Sync` type, such as `rclite::Mutex<T>`.
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
    #[inline]
    pub fn new(data: T) -> Arc<T> {
        let inner = Box::new(ArcInner {
            data: UnsafeCell::new(data),
            counter: AtomicCounter::new(1),
        });
        Arc {
            // Safety: box is always not null
            ptr: unsafe { NonNull::new_unchecked(Box::leak(inner)) },
            phantom: PhantomData,
        }
    }

    /// Constructs a new `Pin<Arc<T>>`. If `T` does not implement `Unpin`, then
    /// `data` will be pinned in memory and unable to be moved.
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        if this.is_unique() {
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

    #[inline(always)]
    fn inner(&self) -> &ArcInner<T> {
        // SAFETY: inner is protected by counter, it will not get released unless drop
        // of the last owner get called.
        unsafe { self.ptr.as_ref() }
    }

    /// Returns `true` if this is the only reference to the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let mut data = Arc::new(String::from("Hello"));
    ///
    /// assert!(Arc::get_mut(&mut data).is_some()); // returns true because data is unique
    ///
    /// let mut data_clone = Arc::clone(&data);
    ///
    /// assert!(Arc::get_mut(&mut data).is_none()); // returns false because data is not unique
    /// assert!(Arc::get_mut(&mut data_clone).is_none()); // returns false because data_clone is not unique
    /// ```
    #[inline]
    fn is_unique(&self) -> bool {
        self.inner().counter.load(Ordering::Acquire) == 1
    }

    /// Returns a mutable reference to the inner value of the given `Arc` if
    /// this is the only `Arc` pointing to it.
    ///
    /// Returns [`None`] otherwise because it is not safe to mutate a shared
    /// value.
    ///
    /// See also [`make_mut`][make_mut], which clones the inner value when there
    /// are other `Arc` pointers.
    ///
    /// [make_mut]: Arc::make_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let mut x = Arc::new(3);
    ///
    /// // Get a mutable reference to the inner value.
    /// *Arc::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(*x, 4);
    ///
    /// // There are now two Arcs pointing to the same value, so `get_mut()` returns `None`.
    /// let _y = Arc::clone(&x);
    /// assert!(Arc::get_mut(&mut x).is_none());
    /// ```
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if this.is_unique() {
            // It is safe to return a mutable reference to the inner value because
            // this is the only Arc pointing to it.
            unsafe { Some(Arc::get_mut_unchecked(this)) }
        } else {
            None
        }
    }

    /// Returns a mutable reference into the given `Arc` without checking if it
    /// is safe to do so.
    ///
    /// This method is faster than [`get_mut`] since it avoids any runtime
    /// checks. However, it is unsafe to use unless you can guarantee that
    /// no other `Arc` pointers to the same allocation exist and that they are
    /// not dereferenced or have active borrows for the duration
    /// of the returned borrow.
    ///
    /// # Safety
    ///
    /// You can use `get_mut_unchecked` if all of the following conditions are
    /// met:
    ///
    /// * No other `Arc` pointers to the same allocation exist.
    /// * The inner type of all `Arc` pointers is exactly the same (including
    ///   lifetimes).
    /// * No other `Arc` pointers are dereferenced or have active borrows for
    ///   the duration of the returned mutable borrow.
    ///
    /// These conditions are trivially satisfied immediately after creating a
    /// new `Arc` with `Arc::new`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let mut x = Arc::new(String::new());
    /// unsafe {
    ///     Arc::get_mut_unchecked(&mut x).push_str("foo")
    /// }
    /// assert_eq!(*x, "foo");
    /// ```
    ///
    /// [`get_mut`]: Arc::get_mut
    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        unsafe { &mut *(*this.ptr.as_ptr()).data.get() }
    }

    // The non-inlined portion of `drop` that simply invokes the destructor.
    // We rely on the compiler to determine whether it is beneficial to inline the
    // destructor or not. Unlike the standard library, we don't explicitly mark
    // this section as inline(never) and leave it to the compiler's discretion to
    // decide if inlining the function is cheap and necessary.
    unsafe fn drop_slow(&mut self) {
        let _ = Box::from_raw(self.ptr.as_ptr());
    }

    /// Returns the inner value of the `Arc` if it's the only strong reference.
    ///
    /// If the `Arc` has multiple strong references, `None` is returned.
    /// If `Arc::into_inner` is called on every clone of this `Arc`, exactly one
    /// of the calls will return the inner value, ensuring it's not dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let x = Arc::new(3);
    /// let y = Arc::clone(&x);
    ///
    /// let x_thread = std::thread::spawn(|| Arc::into_inner(x));
    /// let y_thread = std::thread::spawn(|| Arc::into_inner(y));
    ///
    /// let x_inner_value = x_thread.join().unwrap();
    /// let y_inner_value = y_thread.join().unwrap();
    ///
    /// assert!(matches!(
    ///     (x_inner_value, y_inner_value),
    ///     (None, Some(3)) | (Some(3), None)
    /// ));
    /// ```
    pub fn into_inner(this: Self) -> Option<T> {
        let this = core::mem::ManuallyDrop::new(this);

        let inner = this.inner();

        if inner.counter.fetch_sub(1, Ordering::Release) != 1 {
            // if it's not sole owner of the Arc, return None, it's safe to not manually
            // drop `this` as we manually semantically removed it from the counter
            return None;
        }

        inner.counter.load(Ordering::Acquire);

        Some(unsafe {
            // Move data out of ArcInner
            let value = core::ptr::read(inner.data.get());
            // Deallocate the pointer of ArcInner but avoid running Drop of data, as data is
            // semantically moved.
            dealloc(this.ptr.as_ptr() as *mut u8, Layout::new::<ArcInner<T>>());
            value
        })
    }
}

impl<T: Clone> Arc<T> {
    /// If there is only one reference to T, removes it and returns it.
    /// Otherwise, creates a copy of T and returns it. If `rc_t` is an
    /// [`Arc<T>`], this function behaves like calling `(*rc_t).clone()`,
    /// but avoids copying the value if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let inner = String::from("test");
    /// let ptr = inner.as_ptr();
    ///
    /// let rc = Arc::new(inner);
    /// let inner = Arc::unwrap_or_clone(rc);
    /// // The inner value was not cloned
    /// assert_eq!(ptr, inner.as_ptr());
    ///
    /// let rc = Arc::new(inner);
    /// let rc2 = rc.clone();
    /// let inner = Arc::unwrap_or_clone(rc);
    /// // Because there were 2 references, we had to clone the inner value.
    /// assert_ne!(ptr, inner.as_ptr());
    /// // `rc2` is the last reference, so when we unwrap it we get back
    /// // the original `String`.
    /// let inner = Arc::unwrap_or_clone(rc2);
    /// assert_eq!(ptr, inner.as_ptr());
    /// ```
    #[inline]
    pub fn unwrap_or_clone(this: Self) -> T {
        Arc::try_unwrap(this).unwrap_or_else(|rc| (*rc).clone())
    }

    /// Creates a new Arc<T> object that is a clone of the current Arc<T>
    /// object.
    ///
    /// # Arguments
    ///
    /// * `self` - A reference to the current Arc<T> object to be cloned.
    ///
    /// # Returns
    ///
    /// A new Arc<T> object that shares the same data as the original Arc<T>
    /// object in a new memory location.
    ///
    /// # Performance Considerations
    ///
    /// By pre-allocating memory and writing the cloned data to it, this
    /// function can potentially improve performance by avoiding unnecessary
    /// memory copy operations.
    #[inline]
    fn optimized_clone(&self) -> Arc<T> {
        let mut buffer: Box<MaybeUninit<ArcInner<T>>> = Box::new(MaybeUninit::uninit());
        let ptr = unsafe {
            (*buffer.as_ptr()).data.get().write(T::clone(self));
            (*buffer.as_mut_ptr()).counter = AtomicCounter::new(1);
            NonNull::new_unchecked(Box::leak(buffer) as *mut _ as *mut ArcInner<T>)
        };
        Arc {
            ptr,
            phantom: PhantomData,
        }
    }

    /// Returns a mutable reference to the inner value of the given `Arc`,
    /// ensuring that it has unique ownership.
    ///
    /// If there are other `Arc` pointers to the same allocation, then
    /// `make_mut` will clone the inner value to a new allocation to ensure
    /// unique ownership. This is also referred to as "clone-on-write".
    ///
    /// Unlike `get_mut`, which only returns a mutable reference if there are no
    /// other pointers to the same allocation, `make_mut` always returns a
    /// mutable reference to the unique allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let mut data = Arc::new(5);
    ///
    /// *Arc::make_mut(&mut data) += 1;         // Won't clone anything
    /// let mut other_data = Arc::clone(&data); // Won't clone inner data
    /// *Arc::make_mut(&mut data) += 1;         // Clones inner data
    /// *Arc::make_mut(&mut data) += 1;         // Won't clone anything
    /// *Arc::make_mut(&mut other_data) *= 2;   // Won't clone anything
    ///
    /// // Now `data` and `other_data` point to different allocations.
    /// assert_eq!(*data, 8);
    /// assert_eq!(*other_data, 12);
    /// ```
    ///
    /// # See also
    ///
    /// * [`get_mut`]: Returns a mutable reference to the inner value of the
    ///   given `Arc`, but only if there are no other pointers to the same
    ///   allocation.
    /// * [`clone`]: Clones the `Arc` pointer, but not the inner value.
    ///
    /// [`get_mut`]: Arc::get_mut
    /// [`clone`]: Clone::clone
    #[inline]
    pub fn make_mut(this: &mut Arc<T>) -> &mut T {
        if !this.is_unique() {
            *this = this.optimized_clone();
        }
        unsafe { Self::get_mut_unchecked(this) }
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
fn drop_arc_and_panic_no_inline<T>(ptr: NonNull<ArcInner<T>>) {
    drop(Arc {
        ptr,
        phantom: PhantomData,
    });
    panic!("reference counter overflow");
}

impl<T> Clone for Arc<T> {
    #[inline]
    fn clone(&self) -> Self {
        let count = self.inner().counter.fetch_add(1, Ordering::Relaxed);
        if unlikely(count >= ucount::MAX - BARRIER) {
            // turn back the counter to its initial state as this function will not return a
            // valid [`Arc<T>`]. It uses `drop_arc_and_panic_no_inline` to drop value to
            // reduce overhead of clone inlining in user code.
            drop_arc_and_panic_no_inline(self.ptr);
        }
        Self {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T> Drop for Arc<T> {
    #[inline]
    fn drop(&mut self) {
        if self.inner().counter.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }
        fence(Ordering::Acquire);
        // SAFETY: this is the last owner of the ptr, it is safe to drop data
        unsafe { self.drop_slow() };
    }
}

impl<T: Hash> Hash for Arc<T> {
    #[inline]
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
    #[inline]
    fn default() -> Arc<T> {
        Arc::new(Default::default())
    }
}

impl<T: PartialEq> PartialEq for Arc<T> {
    #[inline]
    fn eq(&self, other: &Arc<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: Eq> Eq for Arc<T> {}

impl<T: PartialOrd> PartialOrd for Arc<T> {
    #[inline]
    fn partial_cmp(&self, other: &Arc<T>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }

    #[inline]
    fn lt(&self, other: &Arc<T>) -> bool {
        **self < **other
    }

    #[inline]
    fn le(&self, other: &Arc<T>) -> bool {
        **self <= **other
    }

    #[inline]
    fn gt(&self, other: &Arc<T>) -> bool {
        **self > **other
    }

    #[inline]
    fn ge(&self, other: &Arc<T>) -> bool {
        **self >= **other
    }
}

impl<T: Ord> Ord for Arc<T> {
    #[inline]
    fn cmp(&self, other: &Arc<T>) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

/// This trait allows for a value to be borrowed as a reference to a given type.
/// It is typically used for generic code that can work with borrowed values of
/// different types.
///
/// This implementation for `Rc<T>` allows for an `Rc<T>` to be borrowed as a
/// shared reference to `T`.
impl<T> core::borrow::Borrow<T> for Arc<T> {
    #[inline(always)]
    fn borrow(&self) -> &T {
        self
    }
}

/// An implementation of the `AsRef` trait for `Arc<T>`.
///
/// This allows an `Arc<T>` to be treated as a reference to `T`.
///
/// # Examples
///
/// ```
/// use rclite::Arc;
///
/// let data = Arc::new(42);
/// let reference: &i32 = data.as_ref();
/// assert_eq!(*reference, 42);
/// ```
impl<T> AsRef<T> for Arc<T> {
    /// Returns a reference to the inner value of the `Arc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Arc;
    ///
    /// let data = Arc::new("Hello, world!".to_string());
    /// let reference: &String = data.as_ref();
    /// assert_eq!(reference, "Hello, world!");
    /// ```
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T> Unpin for Arc<T> {}

#[cfg(feature = "enum-ptr")]
unsafe impl<T> enum_ptr::Aligned for Arc<T> {
    const ALIGNMENT: usize = align_of::<ArcInner<T>>();
}
