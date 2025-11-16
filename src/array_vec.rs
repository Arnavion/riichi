use generic_array::{
	ArrayLength,
	GenericArray,
};

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
		match self.inner.get_mut(self.len) {
			Some(slot) => {
				slot.write(element);
				self.len += 1;
				Ok(())
			},
			None => Err(element),
		}
	}

	pub fn pop(&mut self) -> Option<T> {
		let new_len = self.len.checked_sub(1)?;
		self.len = new_len;
		let element = &self.inner[new_len];
		let element = unsafe { element.assume_init_read() };
		Some(element)
	}

	pub(crate) fn into_combinations(mut self) -> ArrayVecIntoCombinations<T, CAPACITY> {
		let (inner, len) = unsafe { take_inner(&raw const self.inner, &mut self.len) };
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
		// TODO(rustup): Replace this with `slice::assume_init_mut` when that is stabilized.
		unsafe { &mut *(&raw mut self.inner[..self.len] as *mut [T]) }
	}
}

impl<T, CAPACITY> Drop for ArrayVec<T, CAPACITY> where CAPACITY: ArrayLength {
	fn drop(&mut self) {
		unsafe { core::ptr::drop_in_place::<[T]>(&raw mut **self); }
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

impl<T, CAPACITY> TryFrom<ArrayVec<T, CAPACITY>> for GenericArray<T, CAPACITY> where CAPACITY: ArrayLength {
	type Error = ArrayVec<T, CAPACITY>;

	fn try_from(mut arr: ArrayVec<T, CAPACITY>) -> Result<Self, Self::Error> {
		if arr.len == CAPACITY::USIZE {
			let (arr, _) = unsafe { take_inner(&raw const arr.inner, &mut arr.len) };
			let arr = unsafe { GenericArray::assume_init(arr) };
			Ok(arr)
		}
		else {
			Err(arr)
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
		let (inner, len) = unsafe { take_inner(&raw const self.inner, &mut self.len) };
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

pub struct ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	inner: GenericArray<core::mem::MaybeUninit<T>, CAPACITY>,
	range: core::ops::Range<usize>,
}

impl<T, CAPACITY> Drop for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	fn drop(&mut self) {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };

		// TODO(rustup): Replace this with `slice::assume_init_mut` when that is stabilized.
		let rest = unsafe { &mut *(&raw mut self.inner[self.range.clone()] as *mut [T]) };
		unsafe { core::ptr::drop_in_place::<[T]>(rest); }
	}
}

impl<T, CAPACITY> Iterator for ArrayVecIntoIter<T, CAPACITY> where CAPACITY: ArrayLength {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };

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
	fn new(n: usize) -> Self {
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
		//          (n - i1 - 1)
		// (n - i1)-------------- - (i2 - i1 - 1)
		//               2
		let len = ((self.n - self.i1) * (self.n - self.i1).wrapping_sub(1) / 2).wrapping_add(self.i1).wrapping_add(1).wrapping_sub(self.i2);
		(len, Some(len))
	}
}

impl ExactSizeIterator for Combinations {}

impl core::iter::FusedIterator for Combinations {}

unsafe fn clone_inner<T, CAPACITY>(src: &GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, len: usize) -> GenericArray<core::mem::MaybeUninit<T>, CAPACITY> where T: Clone, CAPACITY: ArrayLength {
	let mut result = GenericArray::uninit();
	for (dst, src) in result.iter_mut().zip(src).take(len) {
		let src = unsafe { src.assume_init_ref() };
		dst.write(src.clone());
	}
	result
}

unsafe fn deref_inner<T, CAPACITY>(arr: &GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, len: usize) -> &[T] where CAPACITY: ArrayLength {
	// TODO(rustup): Replace this with `slice::assume_init_ref` when that is stabilized.
	unsafe { &*(&raw const arr[..len] as *const [T]) }
}

unsafe fn take_inner<T, CAPACITY>(arr: *const GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, len: &mut usize) -> (GenericArray<core::mem::MaybeUninit<T>, CAPACITY>, usize) where CAPACITY: ArrayLength {
	let result = unsafe { core::ptr::read(arr) };
	let len = core::mem::replace(len, 0);
	(result, len)
}
