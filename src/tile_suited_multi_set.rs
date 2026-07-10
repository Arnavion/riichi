use crate::{
	Tile, Tile34Set, Tile37Set,
};

/// Similar to [`Tile37MultiSet`](crate::Tile37MultiSet) but stores tiles internally in a different layout
/// that is conducive to decomposing into melds.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
pub struct Tile37SuitedMultiSet<const NT: usize>(Tile37SuitedMultiSetInner);

// Common implementation independent of `NT` to combat monomorphization bloat.
#[derive(Copy, Debug)]
#[derive_const(Eq, PartialEq)]
pub(crate) struct Tile37SuitedMultiSetInner {
	counts: [u32; 4],
	totals: [u8; 4],
}

impl<const NT: usize> Tile37SuitedMultiSet<NT> {
	pub fn new(ts: &[Tile; NT]) -> Tile37SuitedMultiSet<NT> {
		fn simd_select_lt<const N: usize>(ts: core::simd::Simd<u8, N>, t: Tile) -> core::simd::Simd<u8, N> {
			core::simd::Select::select(
				core::simd::cmp::SimdPartialOrd::simd_lt(ts, core::simd::Simd::splat(t as u8)),
				core::simd::Simd::splat(1),
				core::simd::Simd::splat(0),
			)
		}

		let mut inner = Tile37SuitedMultiSetInner::default();

		let ts = unsafe { &*<*const [Tile; NT]>::cast::<[u8; NT]>(ts) };
		let ts = core::simd::Simd::from_array(*ts);

		let is: core::simd::Simd<u8, _> = core::simd::Simd::splat(3) - (simd_select_lt(ts, t!(1p)) + simd_select_lt(ts, t!(1s)) + simd_select_lt(ts, t!(E)));

		let offsets: core::simd::Simd<u8, _> =
			((ts - core::simd::Simd::splat(t!(1m) as u8)) >> 1) +
			core::simd::Simd::splat(3) -
			(simd_select_lt(ts, t!(0m)) + simd_select_lt(ts, t!(0p)) + simd_select_lt(ts, t!(0s))) -
			(is * core::simd::Simd::splat(10));
		let offsets: core::simd::Simd<u32, _> = core::simd::Simd::splat(1) << core::simd::num::SimdUint::cast::<u32>(offsets * core::simd::Simd::splat(3));

		for i in 0..4 {
			let valid = core::simd::cmp::SimdPartialEq::simd_eq(is, core::simd::Simd::splat(i));
			let i = usize::from(i);
			inner.counts[i] = core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(valid, offsets, core::simd::Simd::splat(0_u32)));
			inner.totals[i] = core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(valid, core::simd::Simd::splat(1_u8), core::simd::Simd::splat(0_u8)));
		}

		Self(inner)
	}

	#[cfg(use_core_simd)]
	pub(crate) const fn contains(&self, t: Tile) -> bool {
		self.0.contains(t)
	}

	pub(crate) const fn push(self, t: Tile) -> Tile37SuitedMultiSet<{ NT + 1 }> {
		let mut inner = self.0;
		inner.push(t);
		Tile37SuitedMultiSet(inner)
	}

	pub(crate) const fn remove(self, t: Tile) -> Option<Tile37SuitedMultiSet<{ NT - 1 }>> {
		let mut inner = self.0;
		if inner.remove(t) { Some(Tile37SuitedMultiSet(inner)) } else { None }
	}

	pub(crate) const unsafe fn remove_unchecked(self, t: Tile) -> Tile37SuitedMultiSet<{ NT - 1 }> {
		let mut inner = self.0;
		unsafe { inner.remove_unchecked(t); }
		Tile37SuitedMultiSet(inner)
	}

	pub(crate) fn tenpai(&self) -> Tile37Set {
		tenpai((*self).into(), self.0.totals)
	}

	#[cfg(use_core_simd)]
	#[expect(clippy::wrong_self_convention)]
	pub(crate) fn to_counts(&self) -> core::simd::Simd<u8, 34> {
		self.0.to_counts()
	}
}

const impl<const NT: usize> AsRef<Tile37SuitedMultiSetInner> for Tile37SuitedMultiSet<NT> {
	fn as_ref(&self) -> &Tile37SuitedMultiSetInner {
		&self.0
	}
}

const impl Default for Tile37SuitedMultiSet<0> {
	fn default() -> Self {
		Self(Tile37SuitedMultiSetInner::default())
	}
}

const impl<const NT: usize> TryFrom<Tile37SuitedMultiSetInner> for Tile37SuitedMultiSet<NT> {
	type Error = ();

	fn try_from(inner: Tile37SuitedMultiSetInner) -> Result<Self, Self::Error> {
		if (inner.totals[0] + inner.totals[1] + inner.totals[2] + inner.totals[3]) as usize == NT {
			Ok(Self(inner))
		}
		else {
			Err(())
		}
	}
}

impl<const NT: usize> IntoIterator for Tile37SuitedMultiSet<NT> {
	type Item = <Self::IntoIter as Iterator>::Item;
	type IntoIter = Tile37SuitedMultiSetIntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl Tile37SuitedMultiSetInner {
	#[cfg(use_core_simd)]
	const fn contains(&self, t: Tile) -> bool {
		let (i, offset) = Self::offset_of(t);
		(self.counts[i] & 0b111 << (offset * 3)) != 0
	}

	const fn push(&mut self, t: Tile) {
		let (i, offset) = Self::offset_of(t);
		self.counts[i] += 0b1 << (offset * 3);
		self.totals[i] += 1;
	}

	const fn remove(&mut self, t: Tile) -> bool {
		let (i, offset) = Self::offset_of(t);
		let count = self.counts[i] >> (offset * 3) & 0b111;
		if count == 0 { return false; }
		self.counts[i] -= 0b1 << (offset * 3);
		self.totals[i] -= 1;
		true
	}

	pub(crate) const fn remove_all(&mut self, t: Tile) -> u8 {
		let (i, offset) = Self::offset_of(t);
		let count = (self.counts[i] >> (offset * 3) & 0b111) as u8;
		self.counts[i] &= !(0b111 << (offset * 3));
		self.totals[i] -= count;
		count
	}

	const unsafe fn remove_unchecked(&mut self, t: Tile) {
		let (i, offset) = Self::offset_of(t);
		self.counts[i] -= 0b1 << (offset * 3);
		self.totals[i] -= 1;
	}

	const fn offset_of(t: Tile) -> (usize, usize) {
		let i = 3 - (usize::from(t < t!(1p)) + usize::from(t < t!(1s)) + usize::from(t < t!(E)));
		let offset =
			((t as usize - t!(1m) as usize) >> 1)
			+ 3 - (usize::from(t < t!(0m)) + usize::from(t < t!(0p)) + usize::from(t < t!(0s)))
			- 10 * i;
		(i, offset)
	}

	pub(crate) fn man(&self) -> (u32, u8) {
		(self.counts[0], self.totals[0])
	}

	pub(crate) fn pin(&self) -> (u32, u8) {
		(self.counts[1], self.totals[1])
	}

	pub(crate) fn sou(&self) -> (u32, u8) {
		(self.counts[2], self.totals[2])
	}

	pub(crate) fn ji(&self) -> (u32, u8) {
		(self.counts[3], self.totals[3])
	}

	#[cfg(use_core_simd)]
	#[expect(clippy::wrong_self_convention)]
	fn to_counts(&self) -> core::simd::Simd<u8, 34> {
		const SHIFTS: core::simd::Simd<u32, 34> = core::simd::Simd::from_array([
			0, 3, 6, 9, 12, 15, 18, 21, 24,
			0, 3, 6, 9, 12, 15, 18, 21, 24,
			0, 3, 6, 9, 12, 15, 18, 21, 24,
			0, 3, 6, 9, 12, 15, 18,
		]);

		let counts012 = core::simd::Simd::<_, 3>::from_slice(&self.counts);
		let counts012 =
			(counts012 & core::simd::Simd::splat(0b000_000_000_000_000_111_111_111_111_111)) +
			((counts012 & core::simd::Simd::splat(0b111_111_111_111_111_000_000_000_000_000)) >> 3);
		let counts = core::simd::simd_swizzle!(counts012.resize::<4>(self.counts[3]), [
			0, 0, 0, 0, 0, 0, 0, 0, 0,
			1, 1, 1, 1, 1, 1, 1, 1, 1,
			2, 2, 2, 2, 2, 2, 2, 2, 2,
			3, 3, 3, 3, 3, 3, 3,
		]);
		let counts = counts >> SHIFTS;
		let counts = counts & core::simd::Simd::splat(0b111);
		core::simd::num::SimdUint::cast::<u8>(counts)
	}

	#[expect(clippy::wrong_self_convention)]
	pub(crate) const fn to_simd(&self) -> core::simd::Simd<u32, 4> {
		core::simd::Simd::from_array(self.counts)
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl Clone for Tile37SuitedMultiSetInner {
	fn clone(&self) -> Self {
		*self
	}
}

#[expect(clippy::derivable_impls)] // clippy wants this to be replaced with `#[derive_const(Default)]`, but libcore does not impl `const Default for [T; N]`
const impl Default for Tile37SuitedMultiSetInner {
	fn default() -> Self {
		Self {
			counts: [0; 4],
			totals: [0; 4],
		}
	}
}

const impl<const NT: usize> From<Tile37SuitedMultiSet<NT>> for Tile37SuitedMultiSetInner {
	fn from(outer: Tile37SuitedMultiSet<NT>) -> Self {
		outer.0
	}
}

impl IntoIterator for Tile37SuitedMultiSetInner {
	type Item = <Self::IntoIter as Iterator>::Item;
	type IntoIter = Tile37SuitedMultiSetIntoIter;

	fn into_iter(self) -> Self::IntoIter {
		Tile37SuitedMultiSetIntoIter { counts: self.counts, offset_i: 0 }
	}
}

#[derive(Debug)]
pub struct Tile37SuitedMultiSetIntoIter {
	counts: [u32; 4],
	offset_i: u8,
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl Clone for Tile37SuitedMultiSetIntoIter {
	fn clone(&self) -> Self {
		Self {
			counts: self.counts,
			offset_i: self.offset_i,
		}
	}
}

impl Iterator for Tile37SuitedMultiSetIntoIter {
	type Item = (Tile, core::num::NonZero<u8>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let counts = self.counts.get_mut(usize::from(self.offset_i))?;

			#[expect(clippy::cast_possible_truncation)]
			let offset_b =
				if let Some(ctz) = counts.lowest_one() {
					(ctz as u8) / 3
				}
				else {
					self.offset_i += 1;
					continue;
				};

			let tile = match self.offset_i {
				0 => (((offset_b - u8::from(offset_b >= 5)) << 1) | u8::from(offset_b == 5)) + t!(1m) as u8,
				1 => (((offset_b - u8::from(offset_b >= 5)) << 1) | u8::from(offset_b == 5)) + t!(1p) as u8,
				2 => (((offset_b - u8::from(offset_b >= 5)) << 1) | u8::from(offset_b == 5)) + t!(1s) as u8,
				3 => (offset_b << 1) + t!(E) as u8,
				_ => unsafe { core::hint::unreachable_unchecked(); },
			};
			let tile = unsafe { core::mem::transmute::<u8, Tile>(tile) };
			let count = *counts >> (offset_b * 3) & 0b111;
			let count = unsafe { core::num::NonZero::new_unchecked(count as u8) };
			*counts &= !(0b111 << (offset_b * 3));
			return Some((tile, count));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let any_non_zero = core::simd::cmp::SimdPartialEq::simd_ne(core::simd::Simd::from_array(self.counts), core::simd::Simd::splat(0)).any();
		(usize::from(any_non_zero), None)
	}
}

impl core::iter::FusedIterator for Tile37SuitedMultiSetIntoIter {}

impl<const NT: usize> From<Tile37SuitedMultiSet<NT>> for Tile37Set {
	fn from(set: Tile37SuitedMultiSet<NT>) -> Self {
		const fn to_set(count: u32) -> u32 {
			count.extract_bits(0b001_001_001_001_001_001_001_001_001_001)
		}

		let sets = core::simd::Simd::from_array(set.0.counts);
		let mut sets = sets | (sets >> core::simd::Simd::splat(1)) | (sets >> core::simd::Simd::splat(2));
		sets[0] = to_set(sets[0]);
		sets[1] = to_set(sets[1]);
		sets[2] = to_set(sets[2]);
		// `sets[3]` only has seven useful bits so it can use a smaller `extract_bits` mask than `sets[0..=2]`.
		// But when using vectorization, that ends up generating extra code just for handling `sets[3]`.
		// Using the same `extract_bits` mask as `sets[0..=2]` allows the `extract_bits` operation to be vectorized over all `sets[..]`
		// and ends up being a net benefit.
		sets[3] = if cfg!(use_core_simd) { to_set(sets[3]) } else { sets[3].extract_bits(0b001_001_001_001_001_001_001) };
		let sets = core::simd::num::SimdUint::cast::<u64>(sets);
		let sets = sets << core::simd::Simd::from_array([0, 10, 20, 30]);

		let mut result = Self::default();
		result.present = core::simd::num::SimdUint::reduce_or(sets);
		result
	}
}

fn tenpai(set: Tile37Set, totals: [u8; 4]) -> Tile37Set {
	let totals = core::simd::Simd::from_array(totals);
	let needs_tile = core::simd::Simd::splat(0b10110110110110_u16) >> core::simd::num::SimdUint::cast::<u16>(totals);
	let needs_tile = needs_tile & core::simd::Simd::splat(0b1);
	let needs_tile = core::simd::cmp::SimdPartialEq::simd_ne(needs_tile, core::simd::Simd::splat(0));

	let Tile34Set { present, .. } = set.into();
	let sets = core::simd::Simd::splat(present);
	let sets = sets >> core::simd::Simd::from_array([0, 9, 18]);
	let sets = sets & core::simd::Simd::splat(0b111111111);
	let set_z = present >> 27;

	// Add neighbors
	let sets = sets | (sets << core::simd::Simd::splat(1)) | (sets >> core::simd::Simd::splat(1));
	// Expand to hold separate red five
	let sets =
		(sets & core::simd::Simd::splat(0b000011111)) |
		((sets & core::simd::Simd::splat(0b111110000)) << core::simd::Simd::splat(1));
	let sets = sets.resize(set_z);
	let sets = sets << core::simd::Simd::from_array([0, 10, 20, 30]);
	let sets = core::simd::Select::select(needs_tile, sets, core::simd::Simd::splat(0));

	let mut result = Tile37Set::default();
	result.present = core::simd::num::SimdUint::reduce_or(sets);
	result
}
