//! The code is based on https://github.com/matklad/once_cell

#![no_std]

use core::{
    cell::UnsafeCell,
    fmt,
    mem::MaybeUninit,
    ptr,
    sync::atomic::{AtomicU8, Ordering},
};

// Three states that a OnceCell can be in, encoded into the lower bits of `state` in
// the OnceCell structure.
const INCOMPLETE: u8 = 0x0;
const RUNNING: u8 = 0x1;
const COMPLETE: u8 = 0x2;

/// A cell which can be written to only once.
///
/// Unlike `:td::cell::RefCell`, a `OnceCell` provides simple `&`
/// references to the contents.
///
/// # Example
/// ```
/// use nostd_cell::OnceCell;
///
/// let cell = OnceCell::new();
/// assert!(cell.get().is_none());
///
/// let value: &String = cell.get_or_init(|| {
///     "Hello, World!".to_string()
/// });
/// assert_eq!(value, "Hello, World!");
/// assert!(cell.get().is_some());
/// ```
pub struct OnceCell<T> {
    inner: UnsafeCell<MaybeUninit<T>>,
    state: AtomicU8,
}

impl<T> Default for OnceCell<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for OnceCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.get() {
            Some(v) => f.debug_tuple("OnceCell").field(v).finish(),
            None => f.write_str("OnceCell(Uninit)"),
        }
    }
}

impl<T: Clone> Clone for OnceCell<T> {
    fn clone(&self) -> OnceCell<T> {
        let res = OnceCell::new();
        if let Some(value) = self.get() {
            match res.set(value.clone()) {
                Ok(()) => (),
                Err(_) => unreachable!(),
            }
        }
        res
    }
}

impl<T: PartialEq> PartialEq for OnceCell<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<T: Eq> Eq for OnceCell<T> {}

impl<T> From<T> for OnceCell<T> {
    fn from(value: T) -> Self {
        OnceCell {
            inner: UnsafeCell::new(MaybeUninit::new(value)),
            state: AtomicU8::new(COMPLETE),
        }
    }
}

impl<T> OnceCell<T> {
    /// Creates a new empty cell.
    pub const fn new() -> OnceCell<T> {
        OnceCell {
            inner: UnsafeCell::new(MaybeUninit::uninit()),
            state: AtomicU8::new(INCOMPLETE),
        }
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get(&self) -> Option<&T> {
        if self.is_complete_acquire() {
            Some(self.get_unsafe())
        } else {
            None
        }
    }

    /// Gets the mutable reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.is_complete_acquire() {
            Some(unsafe { &mut *(*self.inner.get()).as_mut_ptr() })
        } else {
            None
        }
    }

    fn is_complete_acquire(&self) -> bool {
        self.state.load(Ordering::Acquire) == COMPLETE
    }

    fn get_unsafe(&self) -> &T {
        unsafe { &*(*self.inner.get()).as_ptr() }
    }

    fn set_unsafe(&self, value: T) {
        unsafe {
            ptr::write((*self.inner.get()).as_mut_ptr(), value);
            self.state.store(COMPLETE, Ordering::Release);
        }
    }

    /// Sets the contents of this cell to `value`.
    ///
    /// Returns `Ok(())` if the cell was empty and `Err(value)` if it was
    /// full.
    ///
    /// # Example
    /// ```
    /// use nostd_cell::OnceCell;
    ///
    /// let cell = OnceCell::new();
    /// assert!(cell.get().is_none());
    ///
    /// assert_eq!(cell.set(92), Ok(()));
    /// assert_eq!(cell.set(62), Err(62));
    ///
    /// assert!(cell.get().is_some());
    /// ```
    pub fn set(&self, value: T) -> Result<(), T> {
        let state = self
            .state
            .compare_and_swap(INCOMPLETE, RUNNING, Ordering::AcqRel);
        if state == INCOMPLETE {
            self.set_unsafe(value);
        } else {
            return Err(value);
        }
        Ok(())
    }

    /// Gets the contents of the cell, initializing it with `f`
    /// if the cell was empty.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. Doing
    /// so results in a panic.
    ///
    /// # Example
    /// ```
    /// use nostd_cell::OnceCell;
    ///
    /// let cell = OnceCell::new();
    /// let value = cell.get_or_init(|| 92);
    /// assert_eq!(value, &92);
    /// let value = cell.get_or_init(|| unreachable!());
    /// assert_eq!(value, &92);
    /// ```
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        enum Void {}
        match self.get_or_try_init(|| Ok::<T, Void>(f())) {
            Ok(val) => val,
            Err(void) => match void {},
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if
    /// the cell was empty. If the cell was empty and `f` failed, an
    /// error is returned.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. Doing
    /// so results in a panic.
    ///
    /// # Example
    /// ```
    /// use nostd_cell::OnceCell;
    ///
    /// let cell = OnceCell::new();
    /// assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
    /// assert!(cell.get().is_none());
    /// let value = cell.get_or_try_init(|| -> Result<i32, ()> {
    ///     Ok(92)
    /// });
    /// assert_eq!(value, Ok(&92));
    /// assert_eq!(cell.get(), Some(&92))
    /// ```
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let state = self
            .state
            .compare_and_swap(INCOMPLETE, RUNNING, Ordering::AcqRel);
        match state {
            COMPLETE => {
                return Ok(self.get_unsafe());
            }
            INCOMPLETE => {
                // In case f() panics, OnceCell will be permanently empty (in RUNNING state).
                match f() {
                    Ok(value) => {
                        self.set_unsafe(value);
                        return Ok(self.get_unsafe());
                    }
                    Err(err) => {
                        self.state.store(INCOMPLETE, Ordering::Release);
                        return Err(err);
                    }
                }
            }
            _ => {
                // It would be great to return error here, but API doesn't allow it.
                panic!("reentrant init");
            }
        }
    }

    /// Consumes the `OnceCell`, returning the wrapped value.
    ///
    /// Returns `None` if the cell was empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use nostd_cell::OnceCell;
    ///
    /// let cell: OnceCell<String> = OnceCell::new();
    /// assert_eq!(cell.into_inner(), None);
    ///
    /// let cell = OnceCell::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.into_inner(), Some("hello".to_string()));
    /// ```
    pub fn into_inner(self) -> Option<T> {
        // Because `into_inner` takes `self` by value, the compiler statically verifies
        // that it is not currently borrowed. So it is safe to move out `Option<T>`.
        if self.is_complete_acquire() {
            Some(unsafe { self.inner.into_inner().assume_init() })
        } else {
            None
        }
    }
}
