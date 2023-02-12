use crate::ucount;
use alloc::boxed::Box;
use core::{cell::UnsafeCell, fmt, marker::PhantomData, ops::Deref, pin::Pin, ptr, ptr::NonNull};

struct RcInner<T> {
    data: UnsafeCell<T>,
    counter: UnsafeCell<ucount>,
}

/// [`Rc<T>`] is a reference-counting pointer for single-threaded use, for
/// multi-threaded use cases you should use [`Arc<T>`][`crate::Arc<T>`]. [`Rc<T>`] provides
/// shared ownership of a value of type T that is stored in the heap. When you
/// clone an Rc, it creates a new pointer to the same heap allocation. When the
/// last Rc pointer to the allocation is destroyed, the stored value is also
/// dropped.
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
    #[inline(always)]
    pub fn new(data: T) -> Rc<T> {
        let inner = Box::new(RcInner {
            data: UnsafeCell::new(data),
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

    /// Constructs a new `Pin<Rc<T>>`. If `T` does not implement `Unpin`, then
    /// `value` will be pinned in memory and unable to be moved.
    #[must_use]
    pub fn pin(value: T) -> Pin<Rc<T>> {
        unsafe { Pin::new_unchecked(Rc::new(value)) }
    }

    /// Gives you a pointer to the data. The reference count stays the same and
    /// the [`Rc<T>`] isn't used up. The pointer stays valid as long as there are
    /// strong references to the [`Rc<T>`].
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
    #[inline(always)]
    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        // SAFETY: ptr is valid, as self is a valid instance of [`Rc<T>`]
        self.ptr.as_ptr() as *const T
    }

    /// Turns [`Rc<T>`] into a raw pointer, must be converted back to [`Rc<T>`] with
    /// [`Rc::from_raw`] to avoid memory leak.
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
    #[inline(always)]
    #[must_use]
    pub fn strong_count(&self) -> ucount {
        // SAFETY: as self is a valid reference inner is valid reference in this
        // lifetime
        unsafe { *self.inner().counter.get() }
    }

    /// Compares if two [`Rc<T>`]s reference the same allocation, similar to ptr::eq.
    /// Note: The same caveats apply when comparing dyn Trait pointers.
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
    #[inline(always)]
    #[must_use]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr.as_ptr() == other.ptr.as_ptr()
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
        if Rc::strong_count(this) == 1 {
            // SAFETY: there is only one reference to Rc it's safe to make a mutable
            // reference
            Some(unsafe { &mut *this.inner().data.get() })
        } else {
            None
        }
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
        if Rc::strong_count(&this) == 1 {
            // SAFETY: there is only one reference to Rc it's safe to move out value of T
            // from Rc and destroy the container
            unsafe {
                let inner = Box::from_raw(this.ptr.as_ptr());
                core::mem::forget(this);
                let val = ptr::read(inner.data.get());
                core::mem::forget(inner.data);
                Ok(val)
            }
        } else {
            Err(this)
        }
    }

    /// If there's only one reference to T, remove it. Otherwise, make a copy of
    /// T. If rc_t is of type [`Rc<T>`], this function works like
    /// (*rc_t).clone(), but will avoid copying the value if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ptr;
    /// # use rclite::Rc;
    /// let inner = String::from("test");
    /// let ptr = inner.as_ptr();
    ///
    /// let rc = Rc::new(inner);
    /// let inner = Rc::unwrap_or_clone(rc);
    /// // The inner value was not cloned
    /// assert!(ptr::eq(ptr, inner.as_ptr()));
    ///
    /// let rc = Rc::new(inner);
    /// let rc2 = rc.clone();
    /// let inner = Rc::unwrap_or_clone(rc);
    /// // Because there were 2 references, we had to clone the inner value.
    /// assert!(!ptr::eq(ptr, inner.as_ptr()));
    /// // `rc2` is the last reference, so when we unwrap it we get back
    /// // the original `String`.
    /// let inner = Rc::unwrap_or_clone(rc2);
    /// assert!(ptr::eq(ptr, inner.as_ptr()));
    /// ```
    #[inline]
    pub fn unwrap_or_clone(this: Self) -> T
    where
        T: Clone,
    {
        Rc::try_unwrap(this).unwrap_or_else(|rc| (*rc).clone())
    }

    #[inline(always)]
    unsafe fn decrease_counter(&self) -> ucount {
        let counter = &mut *self.inner().counter.get();
        *counter = counter.wrapping_sub(1);
        *counter
    }

    #[inline(always)]
    unsafe fn increase_counter(&self) -> ucount {
        let counter = &mut *self.inner().counter.get();
        *counter = counter.wrapping_add(1);
        *counter
    }
}

impl<T> Deref for Rc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        // SAFETY: data will not be shared as mutable unless there is a single owner for
        // the data
        unsafe { &*(self.inner().data.get() as *const T) }
    }
}

impl<T> From<T> for Rc<T> {
    #[inline(always)]
    fn from(value: T) -> Self {
        Rc::new(value)
    }
}

impl<T> Clone for Rc<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        // SAFETY: counter is ensured to be used in single threaded environment only
        let counter = unsafe { self.increase_counter() };
        if counter == 0 {
            unsafe { self.decrease_counter() };
            panic!("reference counter overflow");
        }
        Self {
            ptr: self.ptr,
            phantom: PhantomData,
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
