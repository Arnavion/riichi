use generic_array::{
	ArrayLength,
	GenericArray,
	sequence::{GenericSequence as _, Remove, Shorten},
	typenum::{
		Min, Minimum,
		Prod,
		Sum,
		U1, U2, U3, U4, U14,
	},
};

use crate::{
	ArrayVec, ArrayVecIntoIter,
	KouWait,
	NumberSuit, NumberTile, NumberTileClassified,
	ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ScorableHandRegularPair, ScorableHandRegularPairTag, ShunLowTileAndHasFiveRed, ShunWait,
	Tile, Tile27Set, Tile34MultiSet, Tile34Set, Tile37CountedMultiSet, Tile37MultiSet, Tile37Set, Tile37SetIntoIter, TsumoOrRon,
};

#[derive(Copy, Debug)]
struct Meld<M> {
	len: u8,
	ms: [core::mem::MaybeUninit<M>; 4],
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<M> Clone for Meld<M>
where
	M: Copy,
{
	fn clone(&self) -> Self {
		*self
	}
}

#[derive(Copy, Debug)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(
	clippy::eq_op,
	unused, // Constructed via `transmute`
)]
enum Honor {
	/// Ton
	E = t!(E) as u8 - t!(E) as u8,
	/// Nan
	S = t!(S) as u8 - t!(E) as u8,
	/// Shaa
	W = t!(W) as u8 - t!(E) as u8,
	/// Pei
	N = t!(N) as u8 - t!(E) as u8,
	/// Haku
	P = t!(Wh) as u8 - t!(E) as u8,
	/// Hatsu
	F = t!(G) as u8 - t!(E) as u8,
	/// Chun
	C = t!(R) as u8 - t!(E) as u8,
}

#[derive(Copy, Debug)]
#[derive_const(Clone)]
struct LookupHonors {
	pair: Option<Honor>,
	ankous: u8,
}

impl LookupHonors {
	fn new(key: u32) -> Option<Self> {
		let mut result = Self { pair: None, ankous: 0 };

		let ns = core::simd::Simd::<_, 7>::splat(key);
		#[expect(clippy::cast_possible_truncation)]
		let ns = ns >> core::simd::Simd::from_array(core::array::from_fn(|i| 3 * (i as u32)));
		let ns = ns & core::simd::Simd::splat(0b111);

		let pairs = core::simd::cmp::SimdPartialEq::simd_eq(ns, core::simd::Simd::splat(2));
		let ankous = core::simd::cmp::SimdPartialEq::simd_eq(ns, core::simd::Simd::splat(3));
		let any = core::simd::cmp::SimdPartialEq::simd_ne(ns, core::simd::Simd::splat(0));
		if pairs | ankous != any {
			return None;
		}

		result.pair = {
			let pairs = pairs.to_bitmask();
			if let Some(offset) = pairs.lowest_one() {
				if pairs != 0b1 << offset {
					return None;
				}
				#[expect(clippy::cast_possible_truncation)]
				let h = (offset as u8) << 1;
				Some(unsafe { core::mem::transmute::<u8, Honor>(h) })
			}
			else {
				None
			}
		};

		#[expect(clippy::cast_possible_truncation)]
		{
			result.ankous = ankous.to_bitmask() as u8;
		}

		Some(result)
	}

	/// # Safety
	///
	/// `melds` must have enough elements to write all of `self`'s melds.
	unsafe fn write_melds_to<'a>(self, mut melds: impl Iterator<Item = &'a mut core::mem::MaybeUninit<ScorableHandMeld>>) {
		let mut ankous = self.ankous;
		while let Some(offset) = ankous.lowest_one() {
			ankous &= !(0b1 << offset);
			#[expect(clippy::cast_possible_truncation)]
			let t = t!(E) as u8 + ((offset as u8) << 1);
			let t = unsafe { core::mem::transmute::<u8, Tile>(t) };
			let m = ScorableHandMeld::Ankou(t);
			let slot = melds.next();
			let slot = unsafe { slot.unwrap_unchecked() };
			slot.write(m);
		}
	}
}

#[derive(Copy, Debug)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(clippy::eq_op)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K1 = t!(1m) as u8 - t!(1m) as u8,
	/// Ankou 222 / Pair 22
	K2 = t!(2m) as u8 - t!(1m) as u8,
	/// Ankou 333 / Pair 33
	K3 = t!(3m) as u8 - t!(1m) as u8,
	/// Ankou 444 / Pair 44
	K4 = t!(4m) as u8 - t!(1m) as u8,
	/// Ankou 555 / Pair 55
	K5 = t!(5m) as u8 - t!(1m) as u8,
	/// Ankou 666 / Pair 66
	K6 = t!(6m) as u8 - t!(1m) as u8,
	/// Ankou 777 / Pair 77
	K7 = t!(7m) as u8 - t!(1m) as u8,
	/// Ankou 888 / Pair 88
	K8 = t!(8m) as u8 - t!(1m) as u8,
	/// Ankou 999 / Pair 99
	K9 = t!(9m) as u8 - t!(1m) as u8,

	/// Shun 123
	S1 = (t!(1m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 234
	S2 = (t!(2m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 345
	S3 = (t!(3m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 456
	S4 = (t!(4m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 567
	S5 = (t!(5m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 678
	S6 = (t!(6m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 789
	S7 = (t!(7m) as u8 - t!(1m) as u8) | (1 << 7),
}

impl NumberMeld {
	fn with_base(self, base: NumberTile) -> ScorableHandMeld {
		let number = self as u8;
		if number & (1 << 7) == 0 {
			// Ankou
			let t = base as u8 + number;
			let t = unsafe { core::mem::transmute::<u8, NumberTile>(t) };
			ScorableHandMeld::Ankou(t.into())
		}
		else {
			// Anjun
			let number = number & !(1 << 7);
			let t = base as u8 + number;
			let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(t) };
			ScorableHandMeld::Anjun(t)
		}
	}
}

impl Meld<NumberMeld> {
	/// # Safety
	///
	/// `melds` must have enough elements to write all of `self`'s melds.
	unsafe fn write_to<'a>(self, mut melds: impl Iterator<Item = &'a mut core::mem::MaybeUninit<ScorableHandMeld>>, base: NumberTile) {
		let len = usize::from(self.len);
		unsafe { core::hint::assert_unchecked(len <= self.ms.len()); }
		for m in &self.ms[..len] {
			let m = unsafe { m.assume_init() };
			let slot = melds.next();
			let slot = unsafe { slot.unwrap_unchecked() };
			slot.write(m.with_base(base));
		}
	}
}

#[allow(clippy::enum_glob_use)]
mod numbers {
	use {Some as O, None as X};

	use crate::Number;
	use super::{Meld, NumberMeld, NumberMeld::*};

	const M0: Meld<NumberMeld> = Meld { len: 0, ms: [const { core::mem::MaybeUninit::uninit() }; 4] };

	const fn m1(m1: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		Meld { len: 1, ms }
	}

	const fn m2(m1: NumberMeld, m2: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		Meld { len: 2, ms }
	}

	const fn m3(m1: NumberMeld, m2: NumberMeld, m3: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		ms[2].write(m3);
		Meld { len: 3, ms }
	}

	const fn m4(m1: NumberMeld, m2: NumberMeld, m3: NumberMeld, m4: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		ms[2].write(m3);
		ms[3].write(m4);
		Meld { len: 4, ms }
	}

	include!("numbers.generated.rs");

	pub(super) const EMPTY: &[(Option<NumberMeld>, Meld<NumberMeld>)] = &[(None, M0)];

	pub(super) fn is_valid((key, len): (u32, u8)) -> bool {
		if len == 0 {
			return true;
		}
		if len % 3 == 1 {
			return false;
		}

		// All elements of each slice have the same shape. Eg if the first element is `(Some(_), m2(..))`,
		// then the other elements will also be `(Some(_), m2(..))`. This means that if we find one combination of elements
		// that produces zero or more than two pairs, then every combination will also do that, so we can just terminate early.
		let mut has_pair = false;
		for decomposition in lookup(key) {
			let Some((pair, _)) = decomposition.first() else { return false; };
			if pair.is_some() && core::mem::replace(&mut has_pair, true) {
				return false;
			}
		}

		true
	}

	pub(super) fn lookup(key: u32) -> impl Iterator<Item = &'static [(Option<NumberMeld>, Meld<NumberMeld>)]> {
		const THREE_DIGITS: [u8; 512] = {
			let mut result = [0_u8; _];
			let mut i = 0;
			while i < result.len() {
				#[expect(clippy::cast_possible_truncation)]
				{
					result[i] = (i & 0b111) as u8 + 5 * ((i >> 3) & 0b111) as u8 + 5 * 5 * ((i >> 6) & 0b111) as u8;
				}
				i += 1;
			}
			result
		};

		#[expect(clippy::cast_possible_truncation)]
		let offsets = core::simd::Simd::<_, 9>::from_array(core::array::from_fn(|i| i as _));
		let shifts = offsets * core::simd::Simd::splat(3);

		let counts = core::simd::Simd::splat(key) >> shifts;
		let counts = counts & core::simd::Simd::splat(0b111);

		let present: core::simd::Mask<_, _> = core::simd::cmp::SimdPartialEq::simd_ne(counts, core::simd::Simd::splat(0));
		let is_start = present & !(present.shift_elements_right::<1>(false));
		#[expect(clippy::cast_possible_truncation)]
		let present = present.to_bitmask() as u32;

		let lengths = core::simd::num::SimdUint::trailing_ones(core::simd::Simd::splat(present) >> offsets);

		let masks = ((core::simd::Simd::splat(0b1) << (lengths * core::simd::Simd::splat(3))) - core::simd::Simd::splat(0b1)) << shifts;

		let contiguous_keys = core::simd::Simd::splat(key) & masks;
		let contiguous_keys = core::simd::Select::select(is_start, contiguous_keys, core::simd::Simd::splat(0));
		contiguous_keys.to_array().into_iter()
			.filter(|&key| key != 0)
			.map(|key| -> &'static [_] {
				let key =
					u32::from(THREE_DIGITS[(key & 0x1FF) as usize]) +
					5_u32.pow(3) * u32::from(THREE_DIGITS[((key >> 9) & 0x1FF) as usize]) +
					{
						let key = (key >> 18) as usize;
						unsafe { core::hint::assert_unchecked(key < THREE_DIGITS.len()); }
						5_u32.pow(6) * u32::from(THREE_DIGITS[key])
					};

				let key = key as usize;

				let value = {
					let layer2_i = LAYER1.get(key >> 5).copied().unwrap_or_default();
					let layer2_i = usize::from(layer2_i);
					unsafe { core::hint::assert_unchecked(layer2_i < LAYER2.len()); }
					let block = &LAYER2[layer2_i];
					block[key & 0b11111]
				};

				let (storage_start, len): (usize, usize) =
					if let Some(value) = value.checked_sub(0x8000) {
						let len = value >> 13;
						if len <= 2 {
							let storage_start = STORAGE_MULTIPLE_VALUES_START + usize::from(value & !0x6000);
							let len = len + 2;
							(storage_start, len.into())
						}
						else {
							return &[];
						}
					}
					else {
						(value.into(), 1)
					};
				let storage_end = storage_start + len;
				unsafe { core::hint::assert_unchecked(storage_end <= STORAGE.len()); }
				&STORAGE[storage_start..storage_end]
			})
	}

	pub(super) const fn key_add_number(key: u32, new_tile: Number) -> u32 {
		key + (0b1 << (3 * (new_tile.value() - 1)))
	}
}

pub(crate) struct Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	ji: Option<LookupHonors>,
	decomposition_ptr: GenericArray<*const (Option<NumberMeld>, Meld<NumberMeld>), Sum<NM, U1>>,
	decomposition_len: GenericArray<u8, Sum<NM, U1>>,
	decomposition_base: GenericArray<NumberTile, Sum<NM, U1>>,
	decomposition_i: GenericArray<u8, Sum<NM, U1>>,
	reds: [u8; 3],
}

impl<NM> Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength> + core::ops::Mul<U3, Output: core::ops::Add<U2>>,
{
	pub(crate) fn new(ts: &Tile37CountedMultiSet<Sum<Prod<NM, U3>, U2>>) -> Self {
		// Common implementation independent of `NM` to combat monomorphization bloat.
		fn inner(
			ts: &Tile37MultiSet,
			decomposition_ptr: &mut [*const (Option<NumberMeld>, Meld<NumberMeld>)],
			decomposition_len: &mut [u8],
			decomposition_base: &mut [NumberTile],
			reds: &mut [u8; 3],
		) -> Option<LookupHonors> {
			unsafe { core::hint::assert_unchecked(decomposition_ptr.len() == decomposition_len.len()); }
			unsafe { core::hint::assert_unchecked(decomposition_ptr.len() == decomposition_base.len()); }

			*reds = t![0m, 0p, 0s].map(|t| ts.get(t));

			let ts = Tile34MultiSet::from(ts.clone());
			let man = ts.man();
			let pin = ts.pin();
			let sou = ts.sou();
			let ji = ts.ji();

			let mut slots = decomposition_ptr.iter_mut().zip(decomposition_len).zip(decomposition_base).rev();

			// If any lookup failed, then the hand as a whole cannot be decomposed, so we can just terminate early.
			let ji = LookupHonors::new(ji.0)?;
			let mut has_pair = ji.pair.is_some();
			for ((key, len), base) in [(man, tn!(1m)), (pin, tn!(1p)), (sou, tn!(1s))] {
				if len % 3 == 1 {
					return None;
				}
				for decomposition in numbers::lookup(key) {
					// All elements of each slice have the same shape. Eg if the first element is `(Some(_), m2(..))`,
					// then the other elements will also be `(Some(_), m2(..))`. This means that if we find one combination of elements
					// that produces zero or more than two pairs, then every combination will also do that, so we can just terminate early.
					let (pair, _) = decomposition.first()?;
					if pair.is_some() && core::mem::replace(&mut has_pair, true) {
						return None;
					}
					// More decompositions than slots means this hand as a whole cannot have a valid decomposition.
					let ((slot_ptr, slot_len), slot_base) = slots.next()?;
					*slot_ptr = decomposition.as_ptr();
					#[expect(clippy::cast_possible_truncation)]
					{
						*slot_len = decomposition.len() as u8;
					}
					*slot_base = base;
				}
			}

			has_pair.then_some(ji)
		}

		let ts = ts.as_ref();
		let mut result = Self::default();
		result.ji = inner(ts, &mut result.decomposition_ptr, &mut result.decomposition_len, &mut result.decomposition_base, &mut result.reds);
		result
	}
}

impl<NM> Clone for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn clone(&self) -> Self {
		Self {
			ji: self.ji,
			decomposition_ptr: self.decomposition_ptr.clone(),
			decomposition_len: self.decomposition_len.clone(),
			decomposition_base: self.decomposition_base.clone(),
			decomposition_i: self.decomposition_i.clone(),
			reds: self.reds,
		}
	}
}

impl<NM> core::fmt::Debug for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Lookup")
			.field("ji", &self.ji)
			.field("decomposition_ptr", &self.decomposition_ptr)
			.field("decomposition_len", &self.decomposition_len)
			.field("decomposition_base", &self.decomposition_base)
			.field("decomposition_i", &self.decomposition_i)
			.field("reds", &self.reds)
			.finish()
	}
}

impl<NM> Default for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn default() -> Self {
		Self {
			ji: Default::default(),
			decomposition_ptr: GenericArray::repeat(numbers::EMPTY.as_ptr()),
			#[expect(clippy::cast_possible_truncation)]
			decomposition_len: GenericArray::repeat(numbers::EMPTY.len() as u8),
			decomposition_base: GenericArray::repeat(tn!(1m)),
			decomposition_i: Default::default(),
			reds: Default::default(),
		}
	}
}

impl<NM> Iterator for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength> + ArrayLength,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		// Common implementation independent of `NM` to combat monomorphization bloat.
		fn inner(
			ji: &mut Option<LookupHonors>,
			decomposition_ptr: &[*const (Option<NumberMeld>, Meld<NumberMeld>)],
			decomposition_i: &mut [u8],
			decomposition_base: &[NumberTile],
			decomposition_len: &[u8],
			melds: &mut [core::mem::MaybeUninit<ScorableHandMeld>],
		) -> Option<ScorableHandPair> {
			let ji_ = (*ji)?;

			// SAFETY: In order to have gotten here, we know that two of the given tiles correspond to a pair and the rest are in melds.
			// If there was not one pair, we would've returned a neutered iterator in `new()`.
			// If one or more of the suits did not form a valid decomposition, the corresponding slice would've been empty and we would've returned a neutered iterator in `new()`.
			//
			// So we will fill the `melds` slice exactly.
			let mut pair = ji_.pair.map(|h| {
				let t = t!(E) as u8 + h as u8;
				unsafe { core::mem::transmute::<u8, Tile>(t) }
			});

			let mut melds = melds.iter_mut();

			for ((&ptr, &i), &base) in decomposition_ptr.iter().zip(&*decomposition_i).zip(decomposition_base).rev() {
				let (decomposition_pair, decomposition_melds) = unsafe { &*(ptr.add(usize::from(i))) };

				unsafe { decomposition_melds.write_to(&mut melds, base); }
				pair = pair.or_else(|| decomposition_pair.map(|n| {
					let t = base as u8 + n as u8;
					unsafe { core::mem::transmute::<u8, Tile>(t) }
				}));
			}
			unsafe { ji_.write_melds_to(melds); }

			let pair = unsafe { pair.unwrap_unchecked() };
			let pair = ScorableHandPair(pair);

			cfg_select! {
				all(target_arch = "riscv64", target_feature = "v") => unsafe {
					let to_increment: isize;

					core::arch::asm!(
						"vsetvli zero, {len}, e8, m1, ta, ma",
						// let decomposition_i /* : v8:v8 */ = core::simd::Simd::from_array(self.decomposition_i);
						"vle8.v v8, ({decomposition_i})",
						// let decomposition_len /* : v9:v9 */ = core::simd::Simd::from_array(self.decomposition_len);
						"vle8.v v9, ({decomposition_len})",
						// let decomposition_i_plus_one /* : v10:v10 */ = decomposition_i + core::simd::Simd::splat(1);
						"vadd.vi v10, v8, 1",
						// let to_increment /* : v1:v1 */ = core::simd::cmp::SimdPartialOrd::simd_lt(decomposition_i_plus_one, decomposition_len);
						"vmsltu.vv v1, v10, v9",
						// if let Some(to_increment) = to_increment.first_set() {
						"vfirst.m {to_increment}, v1",
						"bltz {to_increment}, 1f",
						//     let to_increment = 0b1_u64 << to_increment;
						//     let to_reset /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment - 1);
						"vmsbf.m v0, v1",
						//     let decomposition_i /* : v8:v8 */ = core::simd::Select::select(to_reset, core::simd::Simd::splat(0), decomposition_i);
						"vmerge.vim v8, v8, 0, v0",
						//     let to_increment /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment);
						"vmsof.m v0, v1",
						//     let decomposition_i /* : v8:v8 */ = core::simd::Select::select(to_increment, decomposition_i_plus_one, decomposition_i);
						"vmerge.vvm v8, v8, v10, v0",
						//     decomposition_i.copy_to_slice(&mut self.decomposition_i);
						"vse8.v v8, ({decomposition_i})",
						// }
						"1:",

						len = in(reg) decomposition_i.len(),
						decomposition_i = in(reg) decomposition_i.as_mut_ptr(),
						decomposition_len = in(reg) decomposition_len.as_ptr(),
						to_increment = out(reg) to_increment,
						out("v0") _,
						out("v1") _,
						out("v8") _,
						out("v9") _,
						out("v10") _,
						options(nostack),
					);

					if to_increment < 0 {
						*ji = None;
					}
				},

				_ => {
					for (i, &len) in decomposition_i.iter_mut().zip(decomposition_len) {
						if *i + 1 < len {
							*i += 1;
							return Some(pair);
						}
						*i = 0;
					}

					*ji = None;
				},
			}

			Some(pair)
		}

		let mut melds = GenericArray::uninit();
		let pair = inner(&mut self.ji, &self.decomposition_ptr, &mut self.decomposition_i, &self.decomposition_base, &self.decomposition_len, &mut melds)?;
		let melds = unsafe { GenericArray::assume_init(melds) };
		Some((melds, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<NM> ExactSizeIterator for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{
	fn len(&self) -> usize {
		// This function is small enough that monomorphizing it for the unrolled fold is better.
		if self.ji.is_some() {
			self.decomposition_len.iter()
				.zip(&self.decomposition_i)
				.rfold(1, |acc, (&len, &i)| acc * usize::from(len) - usize::from(i))
		}
		else {
			0
		}
	}
}

impl<NM> core::iter::FusedIterator for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{}

unsafe impl<NM> Send for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{}

unsafe impl<NM> Sync for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{}

pub(crate) struct LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength>> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
{
	current: ArrayVecIntoIter<(GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair), Minimum<Sum<NM, U2>, U4>>,
	lookup: Lookup<Sum<NM, U1>>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<NM> LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength>> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
{
	pub(crate) const fn new(lookup: Lookup<Sum<NM, U1>>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		Self {
			current: Default::default(),
			lookup,
			new_tile,
			tsumo_or_ron,
		}
	}
}

impl<NM> Clone for LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength>> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
{
	fn clone(&self) -> Self {
		Self {
			current: self.current.clone(),
			lookup: self.lookup.clone(),
			new_tile: self.new_tile,
			tsumo_or_ron: self.tsumo_or_ron,
		}
	}
}

impl<NM> core::fmt::Debug for LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength>> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("LookupForNewTile")
			.field("current", &self.current)
			.field("lookup", &self.lookup)
			.field("new_tile", &self.new_tile)
			.field("tsumo_or_ron", &self.tsumo_or_ron)
			.finish()
	}
}

impl<NM> Default for LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength>> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
{
	fn default() -> Self {
		Self {
			current: Default::default(),
			lookup: Default::default(),
			new_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
		}
	}
}

impl<NM> Iterator for LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
	Lookup<Sum<NM, U1>>: Iterator<Item = (GenericArray<ScorableHandMeld, Sum<NM, U1>>, ScorableHandPair)>,
	GenericArray<ScorableHandMeld, Sum<NM, U1>>:
		Copy +
		Remove<ScorableHandMeld, Sum<NM, U1>, Output = GenericArray<ScorableHandMeld, NM>> +
		Shorten<ScorableHandMeld, Shorter = GenericArray<ScorableHandMeld, NM>>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current.next() else {
				let (ms, pair) = self.lookup.next()?;
				self.current = extract_fourth_meld(ms, pair, self.new_tile, self.tsumo_or_ron, self.lookup.reds);
				continue;
			};
			break Some((ms, md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_len = self.current.len();
		let (lookup_lo, lookup_hi) = self.lookup.size_hint();
		(current_len + lookup_lo, lookup_hi.map(|lookup_hi| current_len + lookup_hi * (NM::USIZE + 2)))
	}
}

impl<NM> core::iter::FusedIterator for LookupForNewTile<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength>> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
	Self: Iterator,
{}

pub fn lookup_tenpai<NT>(ts: Tile37CountedMultiSet<NT>) -> Tile37Set {
	fn inner(ts: &Tile37MultiSet) -> Tile37Set {
		const MAN: Tile34Set = t34set![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m];
		const PIN: Tile34Set = t34set![1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p];
		const SOU: Tile34Set = t34set![1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s];
		const JI: Tile34Set = t34set![1z, 2z, 3z, 4z, 5z, 6z, 7z];

		let ts34 = Tile34MultiSet::from(ts.clone());
		let man = ts34.man();
		let pin = ts34.pin();
		let sou = ts34.sou();
		let ji = ts34.ji();

		let lens = core::simd::Simd::from_array([man.1, pin.1, sou.1, ji.1]);
		let excess = lens % core::simd::Simd::splat(3);
		// Either one suit has 3n + 1 tiles, or two suits have 3n + 2 tiles for this hand to have a chance of being in tenpai.
		// Any other case is guaranteed to not be in tenpai.
		//
		// - If all suits have 3n tiles, any new tile would be unpaired, so such a hand cannot be in tenpai. Thus at least one suit must have 3n + 1 or 3n + 2 tiles.
		// - If any suit has 3n + 1 tiles, the new tile must be in that suit and the pair will be from that suit.
		//   This means that, for the final hand to be complete, there can only be one suit with 3n + 1 tiles and the other suits must have 3n tiles.
		// - If one suit has 3n + 2 tiles and all other suits have 3n tiles, the hand as a whole already has 3N + 2 tiles and thus cannot a tenpai hand.
		// - If two suits have 3n + 2 tiles and the other two suits have 3n tiles, the new tile can be in either of the two suits and will convert that suit to 3n tiles,
		//   while the other suit will produce the pair.
		// - If three or more suits have 3n + 2 tiles, the new tile will only convert one of them to 3n tiles, which means there will be two or more suits with 3n + 2 tiles,
		//   which cannot be a valid complete hand.
		//
		// Micro-optimization: `mask.to_bitmask().count_ones()` generates silly code that widens the mask bits to `0xFF` as an intermediate step
		// because of how `core::simd::Mask` is designed internally to wrap `iN` instead of `i1`.
		// Doing `reduce_sum(select(mask, splat(1), splat(0)))` generates the intended code that does popcount on the mask.
		let num_excess_1 =
			core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(
				core::simd::cmp::SimdPartialEq::simd_eq(excess, core::simd::Simd::splat(1)),
				core::simd::Simd::splat(1_u8),
				core::simd::Simd::splat(0_u8),
			));
		let num_excess_2 =
			core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(
				core::simd::cmp::SimdPartialEq::simd_eq(excess, core::simd::Simd::splat(2)),
				core::simd::Simd::splat(1_u8),
				core::simd::Simd::splat(0_u8),
			));
		if !((num_excess_1 == 1 && num_excess_2 == 0) || (num_excess_1 == 0 && num_excess_2 == 2)) {
			return Default::default();
		}
		let mut candidates = Tile34Set::default();
		candidates.present = core::simd::num::SimdUint::reduce_or(core::simd::Select::select(
			core::simd::cmp::SimdPartialOrd::simd_gt(excess, core::simd::Simd::splat(0)),
			core::simd::Simd::from_array([MAN.present, PIN.present, SOU.present, JI.present]),
			Tile34Set::default().simd_splat(),
		));

		let expected_valid_lookups = core::simd::cmp::SimdPartialEq::simd_eq(excess, core::simd::Simd::splat(0)).to_array();
		let Ok(man) = update_number_candidates(&mut candidates, man, expected_valid_lookups[0], &MAN) else { return Default::default(); };
		let Ok(pin) = update_number_candidates(&mut candidates, pin, expected_valid_lookups[1], &PIN) else { return Default::default(); };
		let Ok(sou) = update_number_candidates(&mut candidates, sou, expected_valid_lookups[2], &SOU) else { return Default::default(); };
		let Ok(ji_key) = update_honor_candidates(&mut candidates, ji.0, expected_valid_lookups[3], &JI) else { return Default::default(); };

		candidates &= ts34.tenpai();

		candidates.into_iter()
			.flat_map(|t| {
				fn is_valid(
					man: Option<(u32, u8)>,
					pin: Option<(u32, u8)>,
					sou: Option<(u32, u8)>,
					ji_key: Option<u32>,
					t: Tile,
				) -> bool {
					match NumberTile::try_from(t).ok().map(NumberTileClassified::from) {
						Some(NumberTileClassified { suit: NumberSuit::Man, number }) => {
							let (man_key, man_len) = unsafe { man.unwrap_unchecked() };
							let man_key = numbers::key_add_number(man_key, number);
							let man_len = man_len + 1;
							numbers::is_valid((man_key, man_len))
						},
						Some(NumberTileClassified { suit: NumberSuit::Pin, number }) => {
							let (pin_key, pin_len) = unsafe { pin.unwrap_unchecked() };
							let pin_key = numbers::key_add_number(pin_key, number);
							let pin_len = pin_len + 1;
							numbers::is_valid((pin_key, pin_len))
						},
						Some(NumberTileClassified { suit: NumberSuit::Sou, number }) => {
							let (sou_key, sou_len) = unsafe { sou.unwrap_unchecked() };
							let sou_key = numbers::key_add_number(sou_key, number);
							let sou_len = sou_len + 1;
							numbers::is_valid((sou_key, sou_len))
						},
						None => {
							let ji_key = unsafe { ji_key.unwrap_unchecked() };
							let ji_key = ji_key + (0b1 << (((t as u8 - t!(E) as u8) >> 1) * 3));
							LookupHonors::new(ji_key).is_some()
						},
					}
				}

				if let Some(t_red) = t.make_red() {
					let t_is_valid = ts.clone().insert(t);
					let t_red_is_valid = ts.clone().insert(t_red);
					let t_or_t_red_is_valid = (t_is_valid || t_red_is_valid) && is_valid(man, pin, sou, ji_key, t);
					(t_is_valid && t_or_t_red_is_valid).then_some(t).into_iter().chain((t_red_is_valid && t_or_t_red_is_valid).then_some(t_red))
				}
				else {
					let t_is_valid = ts.clone().insert(t) && is_valid(man, pin, sou, ji_key, t);
					t_is_valid.then_some(t).into_iter().chain(None)
				}
			})
			.collect()
	}

	fn update_number_candidates(
		candidates: &mut Tile34Set,
		(key, len): (u32, u8),
		expected_valid_lookup: bool,
		suit_set: &Tile34Set,
	) -> Result<Option<(u32, u8)>, ()> {
		if expected_valid_lookup {
			if numbers::is_valid((key, len)) {
				Ok(None)
			}
			else {
				Err(())
			}
		}
		else {
			let wait_only_in_this_suit = candidates.clone() & suit_set.clone() == *candidates;
			if !wait_only_in_this_suit && !numbers::is_valid((key, len)) {
				*candidates &= suit_set.clone();
				if candidates.is_empty() {
					return Err(());
				}
			}
			Ok(Some((key, len)))
		}
	}

	fn update_honor_candidates(
		candidates: &mut Tile34Set,
		key: u32,
		expected_valid_lookup: bool,
		suit_set: &Tile34Set,
	) -> Result<Option<u32>, ()> {
		if expected_valid_lookup {
			if LookupHonors::new(key).is_none() {
				Err(())
			}
			else {
				Ok(None)
			}
		}
		else {
			let wait_only_in_this_suit = candidates.clone() & suit_set.clone() == *candidates;
			if !wait_only_in_this_suit && LookupHonors::new(key).is_none() {
				*candidates &= suit_set.clone();
				if candidates.is_empty() {
					return Err(());
				}
			}
			Ok(Some(key))
		}
	}

	let ts = Tile37MultiSet::from(ts);
	inner(&ts)
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LookupForTenhou {
	current_a: ArrayVecIntoIter<(GenericArray<ScorableHandMeld, U3>, ScorableHandFourthMeld, ScorableHandRegularPair), U4>,
	current_b: Option<(GenericArray<ScorableHandMeld, U4>, ScorableHandPair, Tile37SetIntoIter)>,
	lookup: Lookup<U4>,
	tiles: Tile37Set,
}

impl LookupForTenhou {
	pub(crate) fn new(ts: Tile37CountedMultiSet<U14>) -> Self {
		let lookup = Lookup::new(&ts);
		let tiles = Tile37Set::from(Tile37MultiSet::from(ts));
		Self {
			current_a: Default::default(),
			current_b: None,
			lookup,
			tiles,
		}
	}
}

impl Iterator for LookupForTenhou {
	type Item = ([ScorableHandMeld; 3], ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current_a.next() else {
				let (ms, pair, new_tile) =
					if
						let Some((ms, pair, new_tiles)) = &mut self.current_b &&
						let Some(new_tile) = new_tiles.next()
					{
						(ms, pair, new_tile)
					}
					else {
						let (ms, pair) = self.lookup.next()?;
						let new_tiles = self.tiles.clone().into_iter();
						let (ms, pair, new_tiles) = self.current_b.insert((ms, pair, new_tiles));
						let new_tile = new_tiles.next();
						// SAFETY: `self.tiles` contains fourteen tiles so `new_tiles` contains at least ceil(14 / 4) elements.
						let new_tile = unsafe { new_tile.unwrap_unchecked() };
						(ms, pair, new_tile)
					};
				self.current_a = extract_fourth_meld(*ms, *pair, new_tile, TsumoOrRon::Tsumo, self.lookup.reds);
				continue;
			};
			break Some((ms.into(), md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_a_len = self.current_a.len();
		(current_a_len, None)
	}
}

impl core::iter::FusedIterator for LookupForTenhou {}

fn extract_fourth_meld<NM>(
	ms: GenericArray<ScorableHandMeld, Sum<NM,U1>>,
	pair: ScorableHandPair,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
	reds: [u8; 3],
) -> ArrayVecIntoIter<(GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair), Minimum<Sum<NM, U2>, U4>>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength> +
		core::ops::Add<U2, Output: Min<U4, Output: ArrayLength>>,
	Lookup<Sum<NM, U1>>: Iterator<Item = (GenericArray<ScorableHandMeld, Sum<NM, U1>>, ScorableHandPair)>,
	GenericArray<ScorableHandMeld, Sum<NM, U1>>:
		Copy +
		Remove<ScorableHandMeld, Sum<NM, U1>, Output = GenericArray<ScorableHandMeld, NM>> +
		Shorten<ScorableHandMeld, Shorter = GenericArray<ScorableHandMeld, NM>>,
{
	const ONES: Tile27Set = t27set![1m, 1p, 1s];
	const SEVENS: Tile27Set = t27set![7m, 7p, 7s];

	let winning_tile = new_tile;
	let new_tile = new_tile.remove_red();

	let mut current = ArrayVec::new();

	if pair.0 == new_tile {
		let (ms, md) = Shorten::pop_back(ms);
		let pair_tag = match tsumo_or_ron {
			TsumoOrRon::Tsumo => ScorableHandRegularPairTag::Antoi,
			TsumoOrRon::Ron => ScorableHandRegularPairTag::Mintoi,
		};
		let pair = ScorableHandRegularPair { tag: pair_tag, inner: pair };
		let result = current.push((ms, ScorableHandFourthMeld::tanki(md), pair));
		unsafe { result.unwrap_unchecked(); }
	}

	current.extend(ms.iter().enumerate().filter_map(|(i, &md)| {
		let md = match md {
			ScorableHandMeld::Ankou(tile) => {
				if tile != new_tile {
					return None;
				}
				ScorableHandFourthMeld::kou(tile, tsumo_or_ron, KouWait::Shanpon)
			},

			ScorableHandMeld::Anjun(tile) => {
				let (t1, t2, t3) = tile.shun();
				let wait =
					if Tile::from(t1) == new_tile {
						if SEVENS.contains(t1.into()) { ShunWait::Penchan } else { ShunWait::RyanmenLow }
					}
					else if Tile::from(t2) == new_tile {
						ShunWait::Kanchan
					}
					else if Tile::from(t3) == new_tile {
						if ONES.contains(t1.into()) { ShunWait::Penchan } else { ShunWait::RyanmenHigh }
					}
					else {
						return None;
					};
				ScorableHandFourthMeld::shun(tile, tsumo_or_ron, wait)
			},

			_ => unsafe { core::hint::unreachable_unchecked(); },
		};
		let (_, ms) = unsafe { Remove::remove_unchecked(ms, i) };
		let pair = ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Antoi, inner: pair };
		Some((ms, md, pair))
	}));

	if reds != [0; _] {
		for (ms, md, pair) in &mut *current {
			for (red, num_red) in t![0m, 0p, 0s].into_iter().zip(reds) {
				if num_red == 0 {
					continue;
				}

				let restored =
					if red == winning_tile {
						if md.is_tanki() {
							restore_red_to_kou(&mut pair.inner.0, red)
						}
						else {
							restore_red_to_fourth_meld(md, red, None)
						}
					}
					else {
						restore_red_to_kou(&mut pair.inner.0, red) ||
						restore_red_to_fourth_meld(md, red, Some(winning_tile)) ||
						ms.iter_mut().rev().any(|m| restore_red_to_meld(m, red))
					};
				unsafe { core::hint::assert_unchecked(restored); }
			}
		}
	}

	current.into_iter()
}

fn restore_red_to_meld(m: &mut ScorableHandMeld, red: Tile) -> bool {
	match m {
		ScorableHandMeld::Ankou(t) => restore_red_to_kou(t, red),
		ScorableHandMeld::Anjun(t) => restore_red_to_shun(t, red),
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn restore_red_to_fourth_meld(m: &mut ScorableHandFourthMeld, red: Tile, unless: Option<Tile>) -> bool {
	match m {
		ScorableHandFourthMeld::Ankou(t, _) |
		ScorableHandFourthMeld::Minkou(t, _) => restore_red_to_kou(t, red),
		ScorableHandFourthMeld::Anjun(t, _) |
		ScorableHandFourthMeld::Minjun(t, _) =>
			if Some(red.remove_red()) == unless {
				false
			}
			else {
				restore_red_to_shun(t, red)
			},
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn restore_red_to_kou(representative: &mut Tile, red: Tile) -> bool {
	if *representative == red.remove_red() {
		*representative = red;
		true
	}
	else {
		false
	}
}

fn restore_red_to_shun(representative: &mut ShunLowTileAndHasFiveRed, red: Tile) -> bool {
	if ((*representative as u8)..=(*representative as u8 + 5)).contains(&(red as u8)) {
		let t = (*representative as u8) | 0b1;
		*representative = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(t) };
		true
	}
	else {
		false
	}
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use generic_array::{
		sequence::{Lengthen, Shorten},
	};

	use crate::{CmpIgnoreRed as _, Number};
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		let mut result = ArrayVec::<_, U3>::new();
		m.for_each_tile(|t| result.push(t).unwrap());
		GenericArray::try_from(result).unwrap().into()
	}

	fn fourth_meld_to_tiles(m: ScorableHandFourthMeld) -> ArrayVec<([Tile; 4], Tile), U2> {
		let mut result = ArrayVec::new();

		match m {
			m @ (
				ScorableHandFourthMeld::Ankou(_, KouWait::Tanki) |
				ScorableHandFourthMeld::Anjun(_, ShunWait::Tanki)
			) => {
				let [t1, t2, t3] = meld_to_tiles(m.into());
				result.push(([t1, t2, t3, t!(1p)], t!(1p))).unwrap();
			},

			ScorableHandFourthMeld::Ankou(tile, KouWait::Shanpon) => {
				let t = tile.remove_red();
				result.push(([t, t, t!(1p), t!(1p)], tile)).unwrap();
				if t != tile {
					result.push(([t, tile, t!(1p), t!(1p)], t)).unwrap();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Kanchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t3, t!(1p), t!(1p)], t2)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Penchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = NumberTile::from(t1);
				if t1.number() == Number::One {
					result.push(([t1.into(), t2.into(), t!(1p), t!(1p)], t3.into())).unwrap();
				}
				else if t1.number() == Number::Seven {
					result.push(([t2.into(), t3.into(), t!(1p), t!(1p)], t1.into())).unwrap();
				}
				else {
					unreachable!();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenLow) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t2, t3, t!(1p), t!(1p)], t1)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenHigh) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t2, t!(1p), t!(1p)], t3)).unwrap();
			},

			_ => unreachable!(),
		}

		result
	}

	fn melds() -> [ScorableHandMeld; 20] {
		[
			make_scorable_hand!(@meld { ankou 1s 1s 1s }),
			make_scorable_hand!(@meld { anjun 1s 2s 3s }),
			make_scorable_hand!(@meld { ankou 2s 2s 2s }),
			make_scorable_hand!(@meld { anjun 2s 3s 4s }),
			make_scorable_hand!(@meld { ankou 3s 3s 3s }),
			make_scorable_hand!(@meld { anjun 3s 4s 5s }),
			make_scorable_hand!(@meld { anjun 3s 4s 0s }),
			make_scorable_hand!(@meld { ankou 4s 4s 4s }),
			make_scorable_hand!(@meld { anjun 4s 5s 6s }),
			make_scorable_hand!(@meld { anjun 4s 0s 6s }),
			make_scorable_hand!(@meld { ankou 5s 5s 5s }),
			make_scorable_hand!(@meld { anjun 5s 6s 7s }),
			make_scorable_hand!(@meld { ankou 5s 5s 0s }),
			make_scorable_hand!(@meld { anjun 0s 6s 7s }),
			make_scorable_hand!(@meld { ankou 6s 6s 6s }),
			make_scorable_hand!(@meld { anjun 6s 7s 8s }),
			make_scorable_hand!(@meld { ankou 7s 7s 7s }),
			make_scorable_hand!(@meld { anjun 7s 8s 9s }),
			make_scorable_hand!(@meld { ankou 8s 8s 8s }),
			make_scorable_hand!(@meld { ankou 9s 9s 9s }),
		]
	}

	fn melds_last() -> [ScorableHandFourthMeld; 40] {
		[
			make_scorable_hand!(@meldr4 { ankou 1s 1s 1s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s penchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s ryanmen_low }),
			make_scorable_hand!(@meldr4 { ankou 2s 2s 2s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 3s 3s 3s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 0s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 0s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 0s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 4s 4s 4s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 4s 0s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 0s 6s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 4s 0s 6s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 5s 5s 5s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 5s 5s 0s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 0s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 0s 6s 7s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 0s 6s 7s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 6s 6s 6s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 7s 7s 7s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s penchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 8s 8s 8s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 9s 9s 9s shanpon }),
		]
	}

	fn eq_ignore_red<NM>(
		(mut ms1, mut md1, p1): (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair),
		(mut ms2, mut md2, p2): (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair),
	) -> bool
	where
		NM: ArrayLength,
		GenericArray<ScorableHandMeld, NM>:
			Copy +
			IntoIterator<Item = ScorableHandMeld> +
			Lengthen<ScorableHandMeld, Longer: core::ops::DerefMut<Target = [ScorableHandMeld]>>,
	{
		fn count_reds_meld(count: &mut usize, m: ScorableHandMeld) {
			match m {
				ScorableHandMeld::Ankan(t!(0s)) |
				ScorableHandMeld::Minkan(t!(0s)) |
				ScorableHandMeld::Ankou(t!(0s)) |
				ScorableHandMeld::Minkou(t!(0s)) => *count += 1,
				ScorableHandMeld::Anjun(t) |
				ScorableHandMeld::Minjun(t) => match t {
					ShunLowTileAndHasFiveRed::Sou3Red |
					ShunLowTileAndHasFiveRed::Sou4Red |
					ShunLowTileAndHasFiveRed::Sou5Red => *count += 1,
					_ => (),
				},
				_ => (),
			}
		}

		fn count_reds_pair(count: &mut usize, p: ScorableHandRegularPair) {
			if p.inner.0 == t!(0s) {
				*count += 1;
			}
		}

		fn remove_red(m: &mut ScorableHandMeld) {
			match m {
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) => *t = t.remove_red(),
				ScorableHandMeld::Anjun(t) |
				ScorableHandMeld::Minjun(t) => *t = t.remove_red().into(),
			}
		}

		fn remove_red_fourth(m: &mut ScorableHandFourthMeld) {
			match m {
				ScorableHandFourthMeld::Ankan(t, _) |
				ScorableHandFourthMeld::Minkan(t, _) |
				ScorableHandFourthMeld::Ankou(t, _) |
				ScorableHandFourthMeld::Minkou(t, _) => *t = t.remove_red(),
				ScorableHandFourthMeld::Anjun(t, _) |
				ScorableHandFourthMeld::Minjun(t, _) => *t = t.remove_red().into(),
			}
		}

		let mut num_red1 = 0;
		for m in ms1 {
			count_reds_meld(&mut num_red1, m);
		}
		count_reds_meld(&mut num_red1, md1.into());
		count_reds_pair(&mut num_red1, p1);

		let mut num_red2 = 0;
		for m in ms2 {
			count_reds_meld(&mut num_red2, m);
		}
		count_reds_meld(&mut num_red2, md2.into());
		count_reds_pair(&mut num_red2, p2);

		for m in &mut ms1 {
			remove_red(m);
		}
		if let Some(mut md1_) = md1.to_tanki() {
			remove_red(&mut md1_);
			append_and_sort(&mut ms1, &mut md1_);
			md1 = ScorableHandFourthMeld::tanki(md1_);
		}
		else {
			ms1.sort_unstable();
			remove_red_fourth(&mut md1);
		}

		for m in &mut ms2 {
			remove_red(m);
		}
		if let Some(mut md2_) = md2.to_tanki() {
			remove_red(&mut md2_);
			append_and_sort(&mut ms2, &mut md2_);
			md2 = ScorableHandFourthMeld::tanki(md2_);
		}
		else {
			ms2.sort_unstable();
			remove_red_fourth(&mut md2);
		}

		ms1 == ms2 && md1 == md2 && p1.tag == p2.tag && p1.inner.0.eq_ignore_red(&p2.inner.0) && num_red1 == num_red2
	}

	fn append_and_sort<T, N>(arr: &mut GenericArray<T, N>, element: &mut T)
	where
		T: Copy + Ord,
		N: ArrayLength,
		GenericArray<T, N>:
			Copy +
			Lengthen<T, Longer:
				core::ops::DerefMut<Target = [T]> +
				Shorten<T, Shorter = GenericArray<T, N>>,
			>,
	{
		let mut arr_ = arr.append(*element);
		arr_.sort_unstable();
		let (arr_, last) = arr_.pop_back();
		*arr = arr_;
		*element = last;
	}

	#[test]
	fn to_meld() {
		for ma in melds_last() {
			for ([t1, t2, t3, t4], new_tile) in fourth_meld_to_tiles(ma) {
				let ts = [t1, t2, t3, t4].into();
				let expected = ([].into(), ma, ScorableHandRegularPair::antoi(t!(1p)));
				let actual: std::vec::Vec<_> =
					LookupForNewTile::new(
						Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
						new_tile,
						TsumoOrRon::Tsumo,
					).collect();
				assert_eq!(actual, [expected], "{ma} on {new_tile} did not meld into {expected:?}, only into {actual:?}");
			}
		}

		// 124 -> X
		assert!(Lookup::<U1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p].into()).unwrap()).next().is_none());
	}

	#[test]
	fn to_melds_2() {
		for ma in melds() {
			let ts @ [t1, t2, t3] = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			used.try_extend(ts).unwrap();

			for mb in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
				for ([t4, t5, t6, t7], new_tile) in fourth_meld_to_tiles(mb) {
					let mut used = used.clone();
					if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
						continue;
					}

					let expected =
						if let Some(mb) = mb.to_tanki() {
							let mut ms = [ma, mb];
							ms.sort_unstable();
							let [m3, m4] = ms;
							([m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
						}
						else {
							([ma].into(), mb, ScorableHandRegularPair::antoi(t!(1p)))
						};

					let ts = [t1, t2, t3, t4, t5, t6, t7].into();
					let actual: std::vec::Vec<_> =
						LookupForNewTile::new(
							Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
							new_tile,
							TsumoOrRon::Tsumo,
						).collect();

					assert!(
						actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
						"{ma} + {mb} on {new_tile} did not meld into {expected:?}, only into {actual:?}",
					);
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_3() {
		for (ma_i, ma) in melds().into_iter().enumerate() {
			let ts @ [t1, t2, t3] = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			used.try_extend(ts).unwrap();

			for &mb in &melds()[ma_i..] {
				let ts @ [t4, t5, t6] = meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend(ts).is_err() {
					continue;
				}

				for mc in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
					for ([t7, t8, t9, t10], new_tile) in fourth_meld_to_tiles(mc) {
						let mut used = used.clone();
						if used.try_extend([t7, t8, t9, t10, new_tile]).is_err() {
							continue;
						}

						let expected =
							if let Some(mc) = mc.to_tanki() {
								let mut ms = [ma, mb, mc];
								ms.sort_unstable();
								let [m2, m3, m4] = ms;
								([m2, m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
							}
							else {
								([ma, mb].into(), mc, ScorableHandRegularPair::antoi(t!(1p)))
							};

						let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into();
						let actual: std::vec::Vec<_> =
							LookupForNewTile::new(
								Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
								new_tile,
								TsumoOrRon::Tsumo,
							).collect();

						assert!(
							actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
							"{ma} + {mb} + {mc} on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
						);
					}
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_4() {
		for (ma_i, ma) in melds().into_iter().enumerate() {
			let ts @ [t1, t2, t3] = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			used.try_extend(ts).unwrap();

			for (mb_i, &mb) in melds()[ma_i..].iter().enumerate() {
				let ts @ [t4, t5, t6] = meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend(ts).is_err() {
					continue;
				}

				for &mc in &melds()[(ma_i + mb_i)..] {
					let ts @ [t7, t8, t9] = meld_to_tiles(mc);
					let mut used = used.clone();
					if used.try_extend(ts).is_err() {
						continue;
					}

					for md in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
						for ([t10, t11, t12, t13], new_tile) in fourth_meld_to_tiles(md) {
							let mut used = used.clone();
							if used.try_extend([t10, t11, t12, t13, new_tile]).is_err() {
								continue;
							}

							let expected =
								if let Some(md) = md.to_tanki() {
									let mut ms = [ma, mb, mc, md];
									ms.sort_unstable();
									let [m1, m2, m3, m4] = ms;
									([m1, m2, m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
								}
								else {
									([ma, mb, mc].into(), md, ScorableHandRegularPair::antoi(t!(1p)))
								};

							let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into();
							let actual: std::vec::Vec<_> =
								LookupForNewTile::new(
									Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
									new_tile,
									TsumoOrRon::Tsumo,
								).collect();

							assert!(
								actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
								"{ma} + {mb} + {mc} + {md} on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
							);
						}
					}
				}
			}
		}
	}
}
