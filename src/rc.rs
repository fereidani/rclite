use crate::ucount;
use alloc::boxed::Box;
use branches::{assume, unlikely};
use core::{
    cell::Cell,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
    ops::Deref,
    pin::Pin,
    ptr::NonNull,
};

#[repr(C)]
struct RcInner<T> {
    data: T,
    counter: Cell<ucount>,
}

/// [`Rc<T>`] is a reference-counting pointer for single-threaded use, for
/// multi-threaded use cases you should use [`Arc<T>`][`crate::Arc<T>`].
/// [`Rc<T>`] provides shared ownership of a value of type T that is stored in
/// the heap. When you clone an Rc, it creates a new pointer to the same heap
/// allocation. When the last Rc pointer to the allocation is destroyed, the
/// stored value is also dropped.
pub struct Rc<T> {
    ptr: NonNull<RcInner<T>>,
    phantom: PhantomData<Box<RcInner<T>>>,
}

impl<T> Rc<T> {
    /// Constructs a new [`Rc<T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let tada = Rc::new("Tada!");
    /// ```
    #[inline]
    pub fn new(data: T) -> Rc<T> {
        Rc {
            // Safety: box is always not null
            ptr: unsafe {
                NonNull::new_unchecked(Box::leak(Box::new(RcInner {
                    data,
                    counter: Cell::new(1),
                })))
            },
            phantom: PhantomData,
        }
    }

    #[inline(always)]
    fn inner(&self) -> &RcInner<T> {
        // SAFETY: inner is protected by counter, it will not get released unless drop
        // of the last owner get called.
        unsafe { self.ptr.as_ref() }
    }

    #[inline]
    fn inner_mut(&mut self) -> &mut RcInner<T> {
        // SAFETY: inner is protected by counter, it will not get released unless drop
        // of the last owner get called.
        unsafe { self.ptr.as_mut() }
    }

    /// Constructs a new `Pin<Rc<T>>`. If `T` does not implement `Unpin`, then
    /// `value` will be pinned in memory and unable to be moved.
    #[inline]
    #[must_use]
    pub fn pin(value: T) -> Pin<Rc<T>> {
        unsafe { Pin::new_unchecked(Rc::new(value)) }
    }

    /// Gives you a pointer to the data. The reference count stays the same and
    /// the [`Rc<T>`] isn't used up. The pointer stays valid as long as there
    /// are strong references to the [`Rc<T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let x = Rc::new("hello".to_owned());
    /// let y = Rc::clone(&x);
    /// let x_ptr = Rc::as_ptr(&x);
    /// assert_eq!(x_ptr, Rc::as_ptr(&y));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    #[inline]
    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        // SAFETY: ptr is valid, as self is a valid instance of [`Rc<T>`]
        self.ptr.as_ptr() as *const T
    }

    /// Turns [`Rc<T>`] into a raw pointer, must be converted back to [`Rc<T>`]
    /// with [`Rc::from_raw`] to avoid memory leak.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let x = Rc::new("hello".to_owned());
    /// let x_ptr = Rc::into_raw(x);
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// // reconstruct Rc to drop the reference and avoid memory leaks
    /// unsafe { Rc::from_raw(x_ptr) };
    /// ```
    #[inline]
    pub fn into_raw(this: Self) -> *const T {
        let ptr = Self::as_ptr(&this);
        core::mem::forget(this);
        ptr
    }

    /// Constructs an [`Rc<T>`] from a raw pointer. The raw pointer must have
    /// been from [`Rc<U>::into_raw`] where U and T must have the same size
    /// and alignment. Improper use may lead to memory unsafe operations.
    ///
    /// # Safety
    /// It's only safe to construct back references that are generated with
    /// [`Rc::into_raw`], converting any other references may lead to undefined
    /// behaivior.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let x = Rc::new("hello".to_owned());
    /// let x_ptr = Rc::into_raw(x);
    ///
    /// unsafe {
    ///     // Convert back to an [`Rc<T>`] to prevent leak.
    ///     let x = Rc::from_raw(x_ptr);
    ///     assert_eq!(&*x, "hello");
    ///
    ///     // Further calls to [`Rc::from_raw(x_ptr)`] would be memory-unsafe.
    /// }
    ///
    /// // The memory was freed when `x` went out of scope above, so `x_ptr` is now dangling!
    /// ```
    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        // SAFETY: ptr offset is same as RcInner struct offset no recalculation of
        // offset is required
        Rc {
            ptr: NonNull::new_unchecked(ptr as *mut RcInner<T>),
            phantom: PhantomData,
        }
    }

    /// Gets the number of strong pointers to an allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let five = Rc::new(5);
    /// let _also_five = Rc::clone(&five);
    ///
    /// // This assertion is deterministic because we haven't shared
    /// // the [`Rc<T>`] between threads.
    /// assert_eq!(2, Rc::strong_count(&five));
    /// ```
    #[inline]
    #[must_use]
    pub fn strong_count(&self) -> usize {
        self.inner().counter.get() as usize
    }

    /// Compares if two [`Rc<T>`]s reference the same allocation, similar to
    /// ptr::eq. Note: The same caveats apply when comparing dyn Trait
    /// pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let five = Rc::new(5);
    /// let same_five = Rc::clone(&five);
    /// let other_five = Rc::new(5);
    ///
    /// assert!(Rc::ptr_eq(&five, &same_five));
    /// assert!(!Rc::ptr_eq(&five, &other_five));
    /// ```
    ///
    /// [`ptr::eq`]: core::ptr::eq "ptr::eq"
    #[inline]
    #[must_use]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr.as_ptr() == other.ptr.as_ptr()
    }

    /// Returns `true` if this is the only reference to the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let mut data = Rc::new(String::from("Hello"));
    ///
    /// assert!(Rc::get_mut(&mut data).is_some()); // returns true because data is unique
    ///
    /// let mut data_clone = Rc::clone(&data);
    ///
    /// assert!(Rc::get_mut(&mut data).is_none()); // returns false because data is not unique
    /// assert!(Rc::get_mut(&mut data_clone).is_none()); // returns false because data_clone is not unique
    /// ```
    #[inline]
    fn is_unique(&self) -> bool {
        self.inner().counter.get() == 1
    }

    /// Returns a mutable reference to the inner value of an Rc, but only if
    /// there are no other references to it. Returns None otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let mut x = Rc::new(3);
    /// *Rc::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(*x, 4);
    ///
    /// let _y = Rc::clone(&x);
    /// assert!(Rc::get_mut(&mut x).is_none());
    /// ```
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if this.is_unique() {
            // SAFETY: there is only one reference to Rc it's safe to make a mutable
            // reference
            Some(&mut this.inner_mut().data)
        } else {
            None
        }
    }

    /// Returns a mutable reference into the given `Rc` without checking if it
    /// is safe to do so.
    ///
    /// This method is faster than [`get_mut`] since it avoids any runtime
    /// checks. However, it is unsafe to use unless you can guarantee that
    /// no other `Rc` pointers to the same allocation exist and that they are
    /// not dereferenced or have active borrows for the duration
    /// of the returned borrow.
    ///
    /// # Safety
    ///
    /// You can use `get_mut_unchecked` if all of the following conditions are
    /// met:
    ///
    /// * No other `Rc` pointers to the same allocation exist.
    /// * The inner type of all `Rc` pointers is exactly the same (including
    ///   lifetimes).
    /// * No other `Rc` pointers are dereferenced or have active borrows for the
    ///   duration of the returned mutable borrow.
    ///
    /// These conditions are trivially satisfied immediately after creating a
    /// new `Rc` with `Rc::new`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let mut x = Rc::new(String::new());
    /// unsafe {
    ///     Rc::get_mut_unchecked(&mut x).push_str("foo")
    /// }
    /// assert_eq!(*x, "foo");
    /// ```
    ///
    /// [`get_mut`]: Rc::get_mut
    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        &mut this.inner_mut().data
    }

    /// If there's only one strong reference, returns the inner value. If not,
    /// returns an error with the Rc passed in.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let x = Rc::new(3);
    /// assert_eq!(Rc::try_unwrap(x).unwrap(), 3);
    ///
    /// let x = Rc::new(4);
    /// let _y = Rc::clone(&x);
    /// assert_eq!(*Rc::try_unwrap(x).unwrap_err(), 4);
    /// ```
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        if this.is_unique() {
            // SAFETY: there is only one reference to Rc it's safe to move out value of T
            // from Rc and destroy the container
            unsafe {
                let inner = Box::from_raw(this.ptr.as_ptr());
                core::mem::forget(this);
                let val = inner.data;
                Ok(val)
            }
        } else {
            Err(this)
        }
    }

    // The non-inlined portion of `drop` that simply invokes the destructor.
    // We rely on the compiler to determine whether it is beneficial to inline the
    // destructor or not. Unlike the standard library, we don't explicitly mark
    // this section as inline(never) and leave it to the compiler's discretion to
    // decide if inlining the function is cheap and necessary.
    unsafe fn drop_slow(&mut self) {
        let _ = Box::from_raw(self.ptr.as_ptr());
    }

    /// Extracts and returns the inner value from an `Rc` if it has exactly one
    /// strong reference.
    ///
    /// If the `Rc` has more than one strong reference or outstanding weak
    /// references, it returns `None` and drops the `Rc`.
    ///
    /// By calling `Rc::into_inner` on every clone of this `Rc`, it is
    /// guaranteed that exactly one of the calls will return the inner
    /// value. This ensures that the inner value is not dropped.
    ///
    /// Example:
    /// ```
    /// use rclite::Rc;
    ///
    /// let value = Rc::new(42);
    /// let cloned1 = Rc::clone(&value);
    /// let cloned2 = Rc::clone(&value);
    /// // it's not sole owner so it will be dropped and will return none
    /// assert!(Rc::into_inner(cloned1).is_none());
    /// // it's not sole owner so it will be dropped and will return none
    /// assert!(Rc::into_inner(value).is_none());
    /// // it is sole reference to the data so it will return the data inside
    /// assert_eq!(Rc::into_inner(cloned2).unwrap(), 42);
    /// ```
    ///
    /// This function is equivalent to `Rc::try_unwrap(this).ok()`. (Note that
    /// these are not equivalent for [`Arc`](crate::sync::Arc), due to race
    /// conditions that do not apply to `Rc`.
    pub fn into_inner(this: Self) -> Option<T> {
        Rc::try_unwrap(this).ok()
    }
}

impl<T: Clone> Rc<T> {
    /// If there's only one reference to T, remove it. Otherwise, make a copy of
    /// T. If rc_t is of type [`Rc<T>`], this function works like
    /// (*rc_t).clone(), but will avoid copying the value if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let inner = String::from("test");
    /// let ptr = inner.as_ptr();
    ///
    /// let rc = Rc::new(inner);
    /// let inner = Rc::unwrap_or_clone(rc);
    /// // The inner value was not cloned
    /// assert_eq!(ptr, inner.as_ptr());
    ///
    /// let rc = Rc::new(inner);
    /// let rc2 = rc.clone();
    /// let inner = Rc::unwrap_or_clone(rc);
    /// // Because there were 2 references, we had to clone the inner value.
    /// assert_ne!(ptr, inner.as_ptr());
    /// // `rc2` is the last reference, so when we unwrap it we get back
    /// // the original `String`.
    /// let inner = Rc::unwrap_or_clone(rc2);
    /// assert_eq!(ptr, inner.as_ptr());
    /// ```
    #[inline]
    pub fn unwrap_or_clone(this: Self) -> T {
        Rc::try_unwrap(this).unwrap_or_else(|rc| (*rc).clone())
    }

    /// Creates a new Rc<T> object that is a clone of the current Rc<T> object.
    ///
    /// # Arguments
    ///
    /// * `self` - A reference to the current Rc<T> object to be cloned.
    ///
    /// # Returns
    ///
    /// A new Rc<T> object that shares the same data as the original Rc<T>
    /// object in a new memory location.
    ///
    /// # Performance Considerations
    ///
    /// By pre-allocating memory and writing the cloned data to it, this
    /// function can potentially improve performance by avoiding unnecessary
    /// memory copy operations.
    fn optimized_clone(&self) -> Rc<T> {
        let mut buffer: Box<MaybeUninit<RcInner<T>>> = Box::new(MaybeUninit::uninit());
        let ptr = unsafe {
            (&mut (*buffer.as_mut_ptr()).data as *mut T).write(T::clone(self));
            (*buffer.as_mut_ptr()).counter = Cell::new(1);
            NonNull::new_unchecked(Box::leak(buffer) as *mut _ as *mut RcInner<T>)
        };
        Rc {
            ptr,
            phantom: PhantomData,
        }
    }

    /// Returns a mutable reference to the inner value of the given `Rc`,
    /// ensuring that it has unique ownership.
    ///
    /// If there are other `Rc` pointers to the same allocation, then
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
    /// use rclite::Rc;
    ///
    /// let mut data = Rc::new(5);
    ///
    /// *Rc::make_mut(&mut data) += 1;         // Won't clone anything
    /// let mut other_data = Rc::clone(&data); // Won't clone inner data
    /// *Rc::make_mut(&mut data) += 1;         // Clones inner data
    /// *Rc::make_mut(&mut data) += 1;         // Won't clone anything
    /// *Rc::make_mut(&mut other_data) *= 2;   // Won't clone anything
    ///
    /// // Now `data` and `other_data` point to different allocations.
    /// assert_eq!(*data, 8);
    /// assert_eq!(*other_data, 12);
    /// ```
    ///
    /// # See also
    ///
    /// * [`get_mut`]: Returns a mutable reference to the inner value of the
    ///   given `Rc`, but only if there are no other pointers to the same
    ///   allocation.
    /// * [`clone`]: Clones the `Rc` pointer, but not the inner value.
    ///
    /// [`get_mut`]: Rc::get_mut
    /// [`clone`]: Clone::clone
    #[inline]
    pub fn make_mut(this: &mut Rc<T>) -> &mut T {
        if !this.is_unique() {
            *this = this.optimized_clone();
        }
        unsafe { Self::get_mut_unchecked(this) }
    }
}

impl<T> Deref for Rc<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &(self.inner().data)
    }
}

impl<T> From<T> for Rc<T> {
    #[inline(always)]
    fn from(value: T) -> Self {
        Rc::new(value)
    }
}

impl<T> Clone for Rc<T> {
    #[inline]
    fn clone(&self) -> Self {
        let counter = &self.inner().counter;
        let value = counter.get();
        unsafe { assume(value != 0) };
        let value = value.wrapping_add(1);
        // SAFETY: counter is ensured to be used in single threaded environment only
        if unlikely(value == 0) {
            panic!("reference counter overflow");
        }
        counter.set(value);
        Self {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T> Drop for Rc<T> {
    #[inline]
    fn drop(&mut self) {
        let counter = &self.inner().counter;
        let value = counter.get();
        unsafe {
            assume(value != 0);
        }
        if value != 1 {
            let value = value.wrapping_sub(1);
            counter.set(value);
        } else {
            unsafe { self.drop_slow() };
        }
    }
}

impl<T: Hash> Hash for Rc<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T> fmt::Pointer for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(&**self as *const T), f)
    }
}

impl<T: Default> Default for Rc<T> {
    #[inline]
    fn default() -> Rc<T> {
        Rc::new(Default::default())
    }
}

impl<T: PartialEq> PartialEq for Rc<T> {
    #[inline]
    fn eq(&self, other: &Rc<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: Eq> Eq for Rc<T> {}

impl<T: PartialOrd> PartialOrd for Rc<T> {
    #[inline]
    fn partial_cmp(&self, other: &Rc<T>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }

    #[inline]
    fn lt(&self, other: &Rc<T>) -> bool {
        **self < **other
    }

    #[inline]
    fn le(&self, other: &Rc<T>) -> bool {
        **self <= **other
    }

    #[inline]
    fn gt(&self, other: &Rc<T>) -> bool {
        **self > **other
    }

    #[inline]
    fn ge(&self, other: &Rc<T>) -> bool {
        **self >= **other
    }
}

impl<T: Ord> Ord for Rc<T> {
    #[inline]
    fn cmp(&self, other: &Rc<T>) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

/// This trait allows for a value to be borrowed as a reference to a given type.
/// It is typically used for generic code that can work with borrowed values of
/// different types.
///
/// This implementation for `Rc<T>` allows for an `Rc<T>` to be borrowed as a
/// shared reference to `T`.
impl<T> core::borrow::Borrow<T> for Rc<T> {
    #[inline(always)]
    fn borrow(&self) -> &T {
        self
    }
}

/// An implementation of the `AsRef` trait for `Rc<T>`.
///
/// This allows an `Rc<T>` to be treated as a reference to `T`.
///
/// # Examples
///
/// ```
/// use rclite::Rc;
///
/// let data = Rc::new(42);
/// let reference: &i32 = data.as_ref();
/// assert_eq!(*reference, 42);
/// ```
impl<T> AsRef<T> for Rc<T> {
    /// Returns a reference to the inner value of the `Rc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rclite::Rc;
    ///
    /// let data = Rc::new("Hello, world!".to_string());
    /// let reference: &String = data.as_ref();
    /// assert_eq!(reference, "Hello, world!");
    /// ```
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T> Unpin for Rc<T> {}

#[cfg(feature = "enum-ptr")]
unsafe impl<T> enum_ptr::Aligned for Rc<T> {
    const ALIGNMENT: usize = align_of::<RcInner<T>>();
}
