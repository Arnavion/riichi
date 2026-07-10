use generic_array::{
	ArrayLength,
	GenericArray,
	typenum::{
		Diff,
		Sum,
		U0, U1,
	},
};

use crate::{
	Tile, Tile34Set, Tile37Set,
};

/// Similar to [`Tile37MultiSet`](crate::Tile37MultiSet) but stores tiles internally in a different layout
/// that is conducive to decomposing into melds.
#[derive(Debug, Eq, PartialEq)]
pub struct Tile37SuitedMultiSet<NT>(Tile37SuitedMultiSetInner, core::marker::PhantomData<NT>);

// Common implementation independent of `NT` to combat monomorphization bloat.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Tile37SuitedMultiSetInner {
	counts: [u32; 4],
	totals: [u8; 4],
}

impl<NT> Tile37SuitedMultiSet<NT> {
	pub fn new(ts: &GenericArray<Tile, NT>) -> Tile37SuitedMultiSet<NT> where NT: ArrayLength {
		let mut inner = Tile37SuitedMultiSetInner::default();
		for &t in ts {
			inner.push(t);
		}
		Self(inner, Default::default())
	}

	pub(crate) fn push(self, t: Tile) -> Tile37SuitedMultiSet<Sum<NT, U1>> where NT: core::ops::Add<U1> {
		let mut inner = self.0;
		inner.push(t);
		Tile37SuitedMultiSet(inner, Default::default())
	}

	pub(crate) fn remove(self, t: Tile) -> Option<Tile37SuitedMultiSet<Diff<NT, U1>>> where NT: core::ops::Sub<U1> {
		let mut inner = self.0;
		let removed = inner.remove(t);
		removed.then_some(Tile37SuitedMultiSet(inner, Default::default()))
	}

	pub(crate) unsafe fn remove_unchecked(self, t: Tile) -> Tile37SuitedMultiSet<Diff<NT, U1>> where NT: core::ops::Sub<U1> {
		let mut inner = self.0;
		unsafe { inner.remove_unchecked(t); }
		Tile37SuitedMultiSet(inner, Default::default())
	}

	pub(crate) fn tenpai(&self) -> Tile37Set {
		tenpai((*self).into(), self.0.totals)
	}
}

impl<NT> AsRef<Tile37SuitedMultiSetInner> for Tile37SuitedMultiSet<NT> {
	fn as_ref(&self) -> &Tile37SuitedMultiSetInner {
		&self.0
	}
}

impl<NT> Clone for Tile37SuitedMultiSet<NT> {
	fn clone(&self) -> Self {
		*self
	}
}

impl<NT> Copy for Tile37SuitedMultiSet<NT> {}

impl Default for Tile37SuitedMultiSet<U0> {
	fn default() -> Self {
		Self(Tile37SuitedMultiSetInner::default(), Default::default())
	}
}

impl<NT> TryFrom<Tile37SuitedMultiSetInner> for Tile37SuitedMultiSet<NT> where NT: generic_array::typenum::Unsigned {
	type Error = ();

	fn try_from(inner: Tile37SuitedMultiSetInner) -> Result<Self, Self::Error> {
		if (inner.totals[0] + inner.totals[1] + inner.totals[2] + inner.totals[3]) as usize == NT::USIZE {
			Ok(Self(inner, Default::default()))
		}
		else {
			Err(())
		}
	}
}

impl<NT> IntoIterator for Tile37SuitedMultiSet<NT> {
	type Item = <Self::IntoIter as Iterator>::Item;
	type IntoIter = Tile37SuitedMultiSetIntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl Tile37SuitedMultiSetInner {
	fn push(&mut self, t: Tile) {
		let (i, offset) = Self::offset_of(t);
		self.counts[i] += 0b1 << (offset * 3);
		self.totals[i] += 1;
	}

	fn remove(&mut self, t: Tile) -> bool {
		let (i, offset) = Self::offset_of(t);
		let count = self.counts[i] >> (offset * 3) & 0b111;
		if count == 0 { return false; }
		self.counts[i] -= 0b1 << (offset * 3);
		self.totals[i] -= 1;
		true
	}

	pub(crate) fn remove_all(&mut self, t: Tile) -> u8 {
		let (i, offset) = Self::offset_of(t);
		let count = (self.counts[i] >> (offset * 3) & 0b111) as u8;
		self.counts[i] &= !(0b111 << (offset * 3));
		self.totals[i] -= count;
		count
	}

	unsafe fn remove_unchecked(&mut self, t: Tile) {
		let (i, offset) = Self::offset_of(t);
		self.counts[i] -= 0b1 << (offset * 3);
		self.totals[i] -= 1;
	}

	pub(crate) fn is_empty(&self) -> bool {
		self.totals[0] == 0 && self.totals[1] == 0 && self.totals[2] == 0 && self.totals[3] == 0
	}

	fn offset_of(t: Tile) -> (usize, usize) {
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
}

impl<NT> From<Tile37SuitedMultiSet<NT>> for Tile37SuitedMultiSetInner {
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

#[derive(Clone, Debug)]
pub struct Tile37SuitedMultiSetIntoIter {
	counts: [u32; 4],
	offset_i: u8,
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
		let any_non_zero = self.counts[0] | self.counts[1] | self.counts[2] | self.counts[3] != 0;
		(usize::from(any_non_zero), None)
	}
}

impl core::iter::FusedIterator for Tile37SuitedMultiSetIntoIter {}

impl<NT> From<Tile37SuitedMultiSet<NT>> for Tile37Set {
	fn from(set: Tile37SuitedMultiSet<NT>) -> Self {
		fn to_set_numbers(count: u32) -> u32 {
			let set = count | (count >> 1) | (count >> 2);
			cfg_select! {
				all(target_arch = "x86_64", target_feature = "bmi2") =>
					unsafe { core::arch::x86_64::_pext_u32(set, 0b001_001_001_001_001_001_001_001_001_001) },

				_ => {{
					//            00j_00i_00h_00g_00f_00e_00d_00c_00b_00a

					//         -> 000_0ji_000_0hg_000_0fe_000_0dc_000_0ba
					let set =
						( set & 0b000_001_000_001_000_001_000_001_000_001) |
						((set & 0b001_000_001_000_001_000_001_000_001_000) >> 2);

					//         -> 000_0ji_000_000_00h_gfe_000_000_00d_cba
					let set =
						( set & 0b000_011_000_000_000_011_000_000_000_011) |
						((set & 0b000_000_000_011_000_000_000_011_000_000) >> 4);

					//         -> 000_0ji_000_000_ji0_000_000_0hg_fed_cba
					let set =
						( set & 0b000_011_000_000_000_000_000_000_001_111) |
						((set & 0b000_000_000_000_001_111_000_000_000_000) >> 8);

					//         -> 000_000_000_000_000_000_00j_ihg_fed_cba
					let set =
						( set & 0b000_000_000_000_000_000_000_011_111_111) |
						((set & 0b000_011_000_000_000_000_000_000_000_000) >> 16);

					set
				}},
			}
		}

		fn to_set_honors(count: u32) -> u32 {
			let set = count | (count >> 1) | (count >> 2);
			cfg_select! {
				all(target_arch = "x86_64", target_feature = "bmi2") =>
					unsafe { core::arch::x86_64::_pext_u32(set, 0b001_001_001_001_001_001_001) },

				_ => {{
					//            00g_00f_00e_00d_00c_00b_00a

					//         -> 00g_000_0fe_000_0dc_000_0ba
					let set =
						( set & 0b001_000_001_000_001_000_001) |
						((set & 0b000_001_000_001_000_001_000) >> 2);

					//         -> 000_000_gfe_000_000_00d_cba
					let set =
						( set & 0b000_000_011_000_000_000_011) |
						((set & 0b001_000_000_000_011_000_000) >> 4);

					//         -> 000_000_000_000_00g_fed_cba
					let set =
						( set & 0b000_000_000_000_000_001_111) |
						((set & 0b000_000_111_000_000_000_000) >> 8);

					set
				}},
			}
		}

		let set_m = to_set_numbers(set.0.counts[0]);
		let set_p = to_set_numbers(set.0.counts[1]);
		let set_s = to_set_numbers(set.0.counts[2]);
		let set_z = to_set_honors(set.0.counts[3]);
		let present =
			u64::from(set_m) |
			(u64::from(set_p) << 10) |
			(u64::from(set_s) << 20) |
			(u64::from(set_z) << 30);
		Self { present }
	}
}

fn tenpai(set: Tile37Set, totals: [u8; 4]) -> Tile37Set {
	fn needs_tile(total: u8) -> bool {
		0b10110110110110_u16.unbounded_shr(total.into()) & 0b1 == 0b1
	}

	const fn expand_set(set: u64) -> u64 {
		// Add neighbors
		let set = set | (set << 1) | (set >> 1);
		// Expand to hold separate red five
		let set =
			( set & 0b000011111) |
			((set & 0b111110000) << 1);
		set
	}

	let Tile34Set { present, .. } = set.into();
	let set_m = present & 0b111111111;
	let set_p = (present >> 9) & 0b111111111;
	let set_s = (present >> 18) & 0b111111111;
	let set_z = (present >> 27) & 0b1111111;
	let present =
		if needs_tile(totals[0]) { expand_set(set_m) } else { 0 } |
		if needs_tile(totals[1]) { expand_set(set_p) << 10 } else { 0 } |
		if needs_tile(totals[2]) { expand_set(set_s) << 20 } else { 0 } |
		if needs_tile(totals[3]) { set_z << 30 } else { 0 };
	Tile37Set { present }
}
