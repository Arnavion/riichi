use generic_array::{
	ArrayLength,
	GenericArray,
};

use crate::CmpIgnoreRed;

/// A sequence of contiguous elements like a [`Vec`](alloc::vec::Vec), but backed by a fixed-length array.
///
/// An `ArrayVec` thus has a concept of being full, and pushing into a full `ArrayVec` fails.
pub struct ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	inner: GenericArray<core::mem::MaybeUninit<T>, CAPACITY>,
	len: usize,
}

impl<T, CAPACITY> ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	pub const fn new() -> Self {
		Self {
			inner: GenericArray::uninit(),
			len: 0,
		}
	}

	/// # Errors
	///
	/// Returns the given element if this `ArrayVec` is already full.
	pub fn push(&mut self, element: T) -> Result<(), T> {
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
	pub(crate) unsafe fn push_unchecked(&mut self, element: T) {
		let result = self.push(element);
		unsafe { result.unwrap_unchecked(); }
	}

	pub fn pop(&mut self) -> Option<T> {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		let new_len = self.len.checked_sub(1)?;
		self.len = new_len;
		let element = &self.inner[new_len];
		let element = unsafe { element.assume_init_read() };
		Some(element)
	}

	pub(crate) fn into_combinations(mut self) -> ArrayVecIntoCombinations<T, CAPACITY> {
		let (inner, len) = unsafe { take_inner(&mut self) };
		ArrayVecIntoCombinations {
			inner,
			combinations: Combinations::new(len),
		}
	}
}

impl<T, CAPACITY> Clone for ArrayVec<T, CAPACITY> where T: Clone, CAPACITY: ArrayLength {
	fn clone(&self) -> Self {
		let inner = unsafe { clone_inner(&self.inner, self.len) };
		Self {
			inner,
			len: self.len,
		}
	}
}

impl<T, CAPACITY> CmpIgnoreRed for ArrayVec<T, CAPACITY> where T: CmpIgnoreRed, CAPACITY: ArrayLength {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		<[_]>::cmp_ignore_red(&**self, &**other)
	}
}

impl<T, CAPACITY> core::fmt::Debug for ArrayVec<T, CAPACITY> where T: core::fmt::Debug, CAPACITY: ArrayLength {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		<[_]>::fmt(self, f)
	}
}

impl<T, CAPACITY> Default for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	fn default() -> Self {
		Self::new()
	}
}

impl<T, CAPACITY> core::ops::Deref for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	type Target = [T];

	fn deref(&self) -> &Self::Target {
		unsafe { deref_inner(&self.inner, self.len) }
	}
}

impl<T, CAPACITY> core::ops::DerefMut for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	fn deref_mut(&mut self) -> &mut Self::Target {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		unsafe { self.inner[..self.len].assume_init_mut() }
	}
}

impl<T, CAPACITY> Drop for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	fn drop(&mut self) {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		unsafe { self.inner[..self.len].assume_init_drop(); }
	}
}

impl<T, CAPACITY> Extend<T> for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item = T> {
		for element in iter {
			if self.push(element).is_err() {
				return;
			}
		}
	}
}

impl<T, CAPACITY> FromIterator<T> for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item = T> {
		let mut result = Self::new();
		result.extend(iter);
		result
	}
}

impl<T, CAPACITY> IntoIterator for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = ArrayVecIntoIter<T, CAPACITY>;

	fn into_iter(mut self) -> Self::IntoIter {
		let (inner, len) = unsafe { take_inner(&mut self) };
		let range = 0..len;
		ArrayVecIntoIter { inner, range }
	}
}

impl<T, CAPACITY> PartialEq for ArrayVec<T, CAPACITY> where T: PartialEq, CAPACITY: ArrayLength {
	fn eq(&self, other: &Self) -> bool {
		<[_]>::eq(&**self, &**other)
	}
}

impl<T, CAPACITY, const N: usize> PartialEq<[T; N]> for ArrayVec<T, CAPACITY> where T: PartialEq, CAPACITY: ArrayLength {
	fn eq(&self, other: &[T; N]) -> bool {
		<[_]>::eq(&**self, other)
	}
}

impl<T, CAPACITY> Eq for ArrayVec<T, CAPACITY> where T: Eq, CAPACITY: ArrayLength {}

impl<T, N, CAPACITY> TryFrom<GenericArray<T, N>> for ArrayVec<T, CAPACITY> where N: ArrayLength, CAPACITY: ArrayLength {
	type Error = GenericArray<T, N>;

	fn try_from(arr: GenericArray<T, N>) -> Result<Self, Self::Error> {
		if CAPACITY::USIZE >= N::USIZE {
			let mut result = Self::new();
			unsafe { core::ptr::copy(&raw const arr, result.inner.as_mut_ptr().cast(), N::USIZE); }
			core::mem::forget(arr);
			Ok(result)
		}
		else {
			Err(arr)
		}
	}
}

impl<T, CAPACITY, N> TryFrom<ArrayVec<T, CAPACITY>> for GenericArray<T, N> where CAPACITY: ArrayLength, N: ArrayLength {
	type Error = ArrayVec<T, CAPACITY>;

	fn try_from(mut arr: ArrayVec<T, CAPACITY>) -> Result<Self, Self::Error> {
		if arr.len == N::USIZE {
			let result = unsafe { core::mem::transmute_copy::<GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, GenericArray<core::mem::MaybeUninit<T>, N>>(&arr.inner) };
			let result = unsafe { GenericArray::assume_init(result) };
			arr.len = 0;
			Ok(result)
		}
		else {
			Err(arr)
		}
	}
}

pub struct ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	inner: GenericArray<core::mem::MaybeUninit<T>, CAPACITY>,
	range: core::ops::Range<usize>,
}

impl<T, CAPACITY> Clone for ArrayVecIntoIter<T, CAPACITY> where T: Clone, CAPACITY: ArrayLength {
	fn clone(&self) -> Self {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end <= self.inner.len()) };

		let mut inner = GenericArray::uninit();
		let src = unsafe { self.inner[self.range.clone()].assume_init_ref() };
		inner[self.range.clone()].write_clone_of_slice(src);
		Self {
			inner,
			range: self.range.clone(),
		}
	}
}

impl<T, CAPACITY> Default for ArrayVecIntoIter<T, CAPACITY> where T: core::fmt::Debug, CAPACITY: ArrayLength {
	fn default() -> Self {
		Self {
			inner: GenericArray::uninit(),
			range: 0..0,
		}
	}
}

impl<T, CAPACITY> core::fmt::Debug for ArrayVecIntoIter<T, CAPACITY> where T: core::fmt::Debug, CAPACITY: ArrayLength {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end <= self.inner.len()) };

		let inner = unsafe { self.inner[self.range.clone()].assume_init_ref() };
		f.debug_struct("ArrayVecIntoIter").field("inner", &inner).finish()
	}
}

impl<T, CAPACITY> Drop for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	fn drop(&mut self) {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end <= self.inner.len()) };

		unsafe { self.inner[self.range.clone()].assume_init_drop(); }
	}
}

impl<T, CAPACITY> Iterator for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end <= self.inner.len()) };

		let i = self.range.next()?;
		let element = unsafe { self.inner[i].assume_init_read() };
		Some(element)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.range.size_hint()
	}
}

impl<T, CAPACITY> DoubleEndedIterator for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	fn next_back(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end <= self.inner.len()) };

		let i = self.range.next_back()?;
		let element = unsafe { self.inner[i].assume_init_read() };
		Some(element)
	}
}

impl<T, CAPACITY> ExactSizeIterator for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {}

impl<T, CAPACITY> core::iter::FusedIterator for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {}

pub(crate) struct ArrayVecIntoCombinations<T, CAPACITY> where CAPACITY: ArrayLength {
	inner: GenericArray<core::mem::MaybeUninit<T>, CAPACITY>,
	combinations: Combinations,
}

impl<T, CAPACITY> Clone for ArrayVecIntoCombinations<T, CAPACITY> where T: Clone, CAPACITY: ArrayLength {
	fn clone(&self) -> Self {
		let inner = unsafe { clone_inner(&self.inner, self.combinations.n) };
		Self {
			inner,
			combinations: self.combinations.clone(),
		}
	}
}

impl<T, CAPACITY> core::fmt::Debug for ArrayVecIntoCombinations<T, CAPACITY> where T: core::fmt::Debug, CAPACITY: ArrayLength {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let inner = unsafe { deref_inner(&self.inner, self.combinations.n) };
		f.debug_struct("ArrayVecIntoCombinations")
			.field("inner", &inner)
			.field("combinations", &self.combinations)
			.finish()
	}
}

impl<T, CAPACITY> Iterator for ArrayVecIntoCombinations<T, CAPACITY> where T: Clone, CAPACITY: ArrayLength {
	type Item = (T, T);

	fn next(&mut self) -> Option<Self::Item> {
		let (i1, i2) = self.combinations.next()?;
		unsafe { core::hint::assert_unchecked(i1 < self.inner.len()); }
		unsafe { core::hint::assert_unchecked(i2 < self.inner.len()); }
		Some((
			(unsafe { self.inner[i1].assume_init_ref() }).clone(),
			(unsafe { self.inner[i2].assume_init_ref() }).clone(),
		))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.combinations.size_hint()
	}
}

impl<T, CAPACITY> ExactSizeIterator for ArrayVecIntoCombinations<T, CAPACITY> where Self: Iterator, CAPACITY: ArrayLength {}

impl<T, CAPACITY> core::iter::FusedIterator for ArrayVecIntoCombinations<T, CAPACITY> where Self: Iterator, CAPACITY: ArrayLength {}

#[derive(Clone, Debug)]
struct Combinations {
	n: usize,
	i1: usize,
	i2: usize,
}

impl Combinations {
	const fn new(n: usize) -> Self {
		Self { n, i1: 0, i2: 1 }
	}
}

impl Iterator for Combinations {
	type Item = (usize, usize);

	fn next(&mut self) -> Option<Self::Item> {
		if self.i2 >= self.n {
			debug_assert_eq!(self.size_hint().0, 0);
			None
		}
		else {
			let current_size_hint = self.size_hint().0;
			let result = Some((self.i1, self.i2));
			if self.i2 + 1 < self.n {
				self.i2 += 1;
			}
			else {
				self.i1 += 1;
				self.i2 = self.i1 + 1;
			}
			let new_size_hint = self.size_hint().0;
			debug_assert_eq!(new_size_hint, current_size_hint - 1);
			result
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		//  (n - i1)(n - i1 - 1)
		// ---------------------- - (i2 - i1 - 1)
		//           2
		let len = ((self.n - self.i1) * (self.n - self.i1).wrapping_sub(1) / 2).wrapping_add(self.i1).wrapping_add(1).wrapping_sub(self.i2);
		(len, Some(len))
	}
}

impl ExactSizeIterator for Combinations {}

impl core::iter::FusedIterator for Combinations {}

unsafe fn clone_inner<T, CAPACITY>(src: &GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, len: usize) -> GenericArray<core::mem::MaybeUninit<T>, CAPACITY> where T: Clone, CAPACITY: ArrayLength {
	unsafe { core::hint::assert_unchecked(len <= src.len()) };

	let mut result = GenericArray::uninit();
	let src = unsafe { src[..len].assume_init_ref() };
	result[..len].write_clone_of_slice(src);
	result
}

unsafe fn deref_inner<T, CAPACITY>(arr: &GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, len: usize) -> &[T] where CAPACITY: ArrayLength {
	unsafe { core::hint::assert_unchecked(len <= arr.len()) };

	unsafe { arr[..len].assume_init_ref() }
}

const unsafe fn take_inner<T, CAPACITY>(arr: &mut ArrayVec<T, CAPACITY>) -> (GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, usize) where CAPACITY: ArrayLength {
	let result = unsafe { core::ptr::read(&raw const arr.inner) };
	let len = core::mem::replace(&mut arr.len, 0);
	(result, len)
}
