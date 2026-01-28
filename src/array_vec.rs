use crate::CmpIgnoreRed;

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

	pub(crate) fn into_combinations(mut self) -> ArrayVecIntoCombinations<T, CAPACITY> {
		let (inner, len) = unsafe { take_inner(&mut self) };
		ArrayVecIntoCombinations {
			inner,
			combinations: Combinations::new(len),
		}
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

impl<T, const CAPACITY: usize> const CmpIgnoreRed for ArrayVec<T, CAPACITY> where T: const CmpIgnoreRed {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		<[_]>::cmp_ignore_red(&**self, &**other)
	}
}

impl<T, const CAPACITY: usize> core::fmt::Debug for ArrayVec<T, CAPACITY> where T: core::fmt::Debug {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		<[_]>::fmt(self, f)
	}
}

impl<T, const CAPACITY: usize> const Default for ArrayVec<T, CAPACITY> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T, const CAPACITY: usize> const core::ops::Deref for ArrayVec<T, CAPACITY> {
	type Target = [T];

	fn deref(&self) -> &Self::Target {
		unsafe { deref_inner(&self.inner, self.len) }
	}
}

impl<T, const CAPACITY: usize> const core::ops::DerefMut for ArrayVec<T, CAPACITY> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		unsafe { core::hint::assert_unchecked(self.len <= self.inner.len()) };

		unsafe { self.inner[..self.len].assume_init_mut() }
	}
}

impl<T, const CAPACITY: usize> const Drop for ArrayVec<T, CAPACITY> where T: [const] core::marker::Destruct {
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

impl<T, const CAPACITY: usize> const PartialEq for ArrayVec<T, CAPACITY> where T: [const] PartialEq {
	fn eq(&self, other: &Self) -> bool {
		<[_]>::eq(&**self, &**other)
	}
}

impl<T, const CAPACITY: usize, const N: usize> const PartialEq<[T; N]> for ArrayVec<T, CAPACITY> where T: [const] PartialEq {
	fn eq(&self, other: &[T; N]) -> bool {
		<[_]>::eq(&**self, other)
	}
}

impl<T, const CAPACITY: usize> const Eq for ArrayVec<T, CAPACITY> where T: [const] Eq {}

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

impl<T, const CAPACITY: usize, const N: usize> const TryFrom<ArrayVec<T, CAPACITY>> for [T; N] where T: [const] core::marker::Destruct {
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

pub(crate) struct ArrayVecIntoCombinations<T, const CAPACITY: usize> {
	inner: [core::mem::MaybeUninit<T>; CAPACITY],
	combinations: Combinations,
}

impl<T, const CAPACITY: usize> Clone for ArrayVecIntoCombinations<T, CAPACITY> where T: Clone {
	fn clone(&self) -> Self {
		let inner = unsafe { clone_inner(&self.inner, self.combinations.n) };
		Self {
			inner,
			combinations: self.combinations.clone(),
		}
	}
}

impl<T, const CAPACITY: usize> core::fmt::Debug for ArrayVecIntoCombinations<T, CAPACITY> where T: core::fmt::Debug {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let inner = unsafe { deref_inner(&self.inner, self.combinations.n) };
		f.debug_struct("ArrayVecIntoCombinations")
			.field("inner", &inner)
			.field("combinations", &self.combinations)
			.finish()
	}
}

impl<T, const CAPACITY: usize> Iterator for ArrayVecIntoCombinations<T, CAPACITY> where T: Clone {
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

impl<T, const CAPACITY: usize> ExactSizeIterator for ArrayVecIntoCombinations<T, CAPACITY> where Self: Iterator {}

impl<T, const CAPACITY: usize> core::iter::FusedIterator for ArrayVecIntoCombinations<T, CAPACITY> where Self: Iterator {}

unsafe impl<T, const CAPACITY: usize> core::iter::TrustedLen for ArrayVecIntoCombinations<T, CAPACITY> where Self: Iterator {}

#[derive_const(Clone)]
#[derive(Debug)]
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

unsafe impl core::iter::TrustedLen for Combinations {}

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
