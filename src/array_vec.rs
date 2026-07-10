/// A sequence of contiguous elements like a [`Vec`](alloc::vec::Vec), but backed by a fixed-length array.
///
/// An `ArrayVec` thus has a concept of being full, and pushing into a full `ArrayVec` fails.
pub struct ArrayVec<T, const CAPACITY: usize> {
	inner: [core::mem::MaybeUninit<T>; CAPACITY],
	len: usize,
}

impl<T, const CAPACITY: usize> ArrayVec<T, CAPACITY> {
	pub const fn new() -> Self {
		Self {
			inner: [const { core::mem::MaybeUninit::uninit() }; CAPACITY],
			len: 0,
		}
	}

	/// # Errors
	///
	/// Returns the given element if this `ArrayVec` is already full.
	pub const fn push(&mut self, element: T) -> Result<(), T> {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		match self.inner.get_mut(self.len) {
			Some(slot) => {
				slot.write(element);
				self.len += 1;
				Ok(())
			},
			None => Err(element),
		}
	}

	/// # Safety
	///
	/// Requires `self.len() < CAPACITY`.
	pub(crate) const unsafe fn push_unchecked(&mut self, element: T) {
		let result = self.push(element);
		unsafe { result.unwrap_unchecked(); }
	}

	pub const fn pop(&mut self) -> Option<T> {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		let new_len = self.len.checked_sub(1)?;
		self.len = new_len;
		let element = &self.inner[new_len];
		let element = unsafe { element.assume_init_read() };
		Some(element)
	}
}

impl<T, const CAPACITY: usize> Clone for ArrayVec<T, CAPACITY> where T: Clone {
	fn clone(&self) -> Self {
		let inner = unsafe { clone_inner(&self.inner, self.len) };
		Self {
			inner,
			len: self.len,
		}
	}
}

impl<T, const CAPACITY: usize> core::fmt::Debug for ArrayVec<T, CAPACITY> where T: core::fmt::Debug {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		<[_]>::fmt(self, f)
	}
}

const impl<T, const CAPACITY: usize> Default for ArrayVec<T, CAPACITY> {
	fn default() -> Self {
		Self::new()
	}
}

const impl<T, const CAPACITY: usize> core::ops::Deref for ArrayVec<T, CAPACITY> {
	type Target = [T];

	fn deref(&self) -> &Self::Target {
		unsafe { deref_inner(&self.inner, self.len) }
	}
}

const impl<T, const CAPACITY: usize> core::ops::DerefMut for ArrayVec<T, CAPACITY> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		unsafe { self.inner[..self.len].assume_init_mut() }
	}
}

const impl<T, const CAPACITY: usize> Drop for ArrayVec<T, CAPACITY> where T: [const] core::marker::Destruct {
	fn drop(&mut self) {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		unsafe { self.inner[..self.len].assume_init_drop(); }
	}
}

impl<T, const CAPACITY: usize> Extend<T> for ArrayVec<T, CAPACITY> {
	fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item = T> {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		let (written, _) = self.inner[self.len..].write_iter(iter);
		self.len += written.len();
	}
}

impl<T, const CAPACITY: usize> FromIterator<T> for ArrayVec<T, CAPACITY> {
	fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item = T> {
		let mut result = Self::new();
		result.extend(iter);
		result
	}
}

impl<T, const CAPACITY: usize> IntoIterator for ArrayVec<T, CAPACITY> {
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = core::array::IntoIter<T, CAPACITY>;

	fn into_iter(mut self) -> Self::IntoIter {
		let (inner, len) = unsafe { take_inner(&mut self) };
		let range = 0..len;
		unsafe { core::array::IntoIter::new_unchecked(inner, range) }
	}
}

const impl<T, const CAPACITY: usize> PartialEq for ArrayVec<T, CAPACITY> where T: [const] PartialEq {
	fn eq(&self, other: &Self) -> bool {
		<[_]>::eq(&**self, &**other)
	}
}

const impl<T, const CAPACITY: usize, const N: usize> PartialEq<[T; N]> for ArrayVec<T, CAPACITY> where T: [const] PartialEq {
	fn eq(&self, other: &[T; N]) -> bool {
		<[_]>::eq(&**self, other)
	}
}

const impl<T, const CAPACITY: usize> Eq for ArrayVec<T, CAPACITY> where T: [const] Eq {}

impl<T, const N: usize, const CAPACITY: usize> TryFrom<[T; N]> for ArrayVec<T, CAPACITY> {
	type Error = [T; N];

	fn try_from(arr: [T; N]) -> Result<Self, Self::Error> {
		if CAPACITY >= N {
			let mut result = Self::new();
			unsafe { core::ptr::copy(&raw const arr, result.inner.as_mut_ptr().cast(), N); }
			core::mem::forget(arr);
			Ok(result)
		}
		else {
			Err(arr)
		}
	}
}

const impl<T, const CAPACITY: usize, const N: usize> TryFrom<ArrayVec<T, CAPACITY>> for [T; N] where T: [const] core::marker::Destruct {
	type Error = ArrayVec<T, CAPACITY>;

	fn try_from(mut arr: ArrayVec<T, CAPACITY>) -> Result<Self, Self::Error> {
		if arr.len == N {
			let result = unsafe { core::mem::transmute_copy::<[core::mem::MaybeUninit<T>; CAPACITY], [core::mem::MaybeUninit<T>; N]>(&arr.inner) };
			let result = unsafe { core::mem::MaybeUninit::array_assume_init(result) };
			arr.len = 0;
			Ok(result)
		}
		else {
			Err(arr)
		}
	}
}

unsafe fn clone_inner<T, const CAPACITY: usize>(src: &[core::mem::MaybeUninit<T>; CAPACITY], len: usize) -> [core::mem::MaybeUninit<T>; CAPACITY] where T: Clone {
	unsafe { core::hint::assert_unchecked(len <= src.len()) };

	let mut result = [const { core::mem::MaybeUninit::uninit() }; CAPACITY];
	let src = unsafe { src[..len].assume_init_ref() };
	result[..len].write_clone_of_slice(src);
	result
}

const unsafe fn deref_inner<T, const CAPACITY: usize>(arr: &[core::mem::MaybeUninit<T>; CAPACITY], len: usize) -> &[T] {
	unsafe { core::hint::assert_unchecked(len <= arr.len()) };

	unsafe { arr[..len].assume_init_ref() }
}

const unsafe fn take_inner<T, const CAPACITY: usize>(arr: &mut ArrayVec<T, CAPACITY>) -> ([core::mem::MaybeUninit<T>; CAPACITY], usize) {
	let result = unsafe { core::ptr::read(&raw const arr.inner) };
	let len = core::mem::replace(&mut arr.len, 0);
	(result, len)
}
