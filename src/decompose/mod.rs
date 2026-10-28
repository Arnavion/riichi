use crate::{
	ArrayVec,
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

#[derive(Debug)]
pub(crate) struct Lookup<const NM: usize>
where
	[(); NM + 1]:,
{
	has_more: bool,
	// The first NM elements are melds, and the NM + 1'th element is the pair.
	// Honor melds are stored as `meld_ptr` == `null()` and `meld_base` == the honor tile.
	meld_ptr: [*const NumberMeld; NM + 1],
	meld_base: [Tile; NM + 1],
	// Maps each `meld_ptr` element to the index of its source decomposition parameters in `meld_source_len` and `meld_source_i`.
	meld_source: [u8; NM + 1],
	meld_source_len: [u8; NM + 1],
	meld_source_i: [u8; NM + 1],
	reds: [u8; 3],
}

impl<const NM: usize> Lookup<NM>
where
	[(); NM + 1]:,
{
	pub(crate) fn new(ts: &Tile37CountedMultiSet<{ NM * 3 + 2 }>) -> Self {
		// Common implementation independent of `NM` to combat monomorphization bloat.
		fn inner(
			ts: &Tile37MultiSet,
			meld_ptr: &mut [*const NumberMeld],
			meld_base: &mut [Tile],
			meld_source: &mut [u8],
			meld_source_len: &mut [u8],
			reds: &mut [u8; 3],
		) -> bool {
			unsafe { core::hint::assert_unchecked(meld_ptr.len() == meld_base.len()); }
			unsafe { core::hint::assert_unchecked(meld_ptr.len() == meld_source.len()); }
			unsafe { core::hint::assert_unchecked(meld_ptr.len() == meld_source_len.len()); }

			let Some((pair_ptr, meld_ptr)) = meld_ptr.split_last_mut() else { return false; };
			let Some((pair_base, meld_base)) = meld_base.split_last_mut() else { return false; };
			let Some((pair_source, meld_source)) = meld_source.split_last_mut() else { return false; };

			*reds = t![0m, 0p, 0s].map(|t| ts.get(t));

			let ts = Tile34MultiSet::from(ts.clone());
			let man = ts.man();
			let pin = ts.pin();
			let sou = ts.sou();
			let ji = ts.ji();

			let mut meld_source_slots = meld_source_len.iter_mut().enumerate().rev();
			let mut meld_slots = meld_ptr.iter_mut().zip(meld_base).zip(meld_source);

			// If any lookup failed, then the hand as a whole cannot be decomposed, so we can just terminate early.
			let Some(ji) = LookupHonors::new(ji.0) else { return false; };
			let mut has_pair =
				if let Some(h) = ji.pair {
					let pair_representative = t!(E) as u8 + h as u8;
					*pair_base = unsafe { core::mem::transmute::<u8, Tile>(pair_representative) };
					true
				}
				else {
					false
				};
			for ((key, len), base) in [(man, tn!(1m)), (pin, tn!(1p)), (sou, tn!(1s))] {
				if len % 3 == 1 {
					return false;
				}
				for decomposition in numbers::lookup(key) {
					let Some((pair, melds)) = decomposition.first() else { return false; };

					// More decompositions than meld source slots means this hand as a whole cannot have a valid decomposition.
					let Some((meld_source_i, slot_meld_source_len)) = meld_source_slots.next() else { return false; };

					#[expect(clippy::cast_possible_truncation)]
					{
						*slot_meld_source_len = decomposition.len() as u8;
					}

					if let Some(pair) = pair {
						// All elements of each slice have the same shape. Eg if the first element is `(Some(_), m2(..))`,
						// then the other elements will also be `(Some(_), m2(..))`. This means that if we find one combination of elements
						// that produces zero or more than two pairs, then every combination will also do that, so we can just terminate early.
						if core::mem::replace(&mut has_pair, true) {
							return false;
						}

						// This is equivalent to `*pair_ptr = pair;`, but miri complains that that pointer's provenance is limited to `pair`,
						// whereas we want to use the pointer to walk through all elements of `decomposition`.
						// So we need to retain the original provenance of `decomposition` by dealing only with pointers throughout.
						let offset = unsafe { core::ptr::from_ref(pair).byte_offset_from(decomposition.as_ptr()) };
						*pair_ptr = decomposition.as_ptr().wrapping_byte_offset(offset).cast();

						*pair_base = base.into();

						#[expect(clippy::cast_possible_truncation)]
						{
							*pair_source = meld_source_i as u8;
						}
					}

					let ms = unsafe { core::ptr::addr_of!((*decomposition.as_ptr()).1.ms) };
					let melds_len = usize::from(melds.len);
					unsafe { core::hint::assert_unchecked(melds_len <= melds.ms.len()); }
					for i in 0..melds_len {
						// More melds than meld slots means this hand cannot have a valid decomposition.
						let Some(((slot_meld_ptr, slot_meld_base), slot_meld_source)) = meld_slots.next() else { return false; };

						// This is equivalent to `*slot_meld_ptr = unsafe { (*ms)[i].assume_init_ref() };`, but miri complains that that pointer's provenance is limited to `ms[i]`,
						// whereas we want to use the pointer to walk through all elements of `decomposition`.
						// So we need to retain the original provenance of `decomposition` by dealing only with pointers throughout.
						*slot_meld_ptr = unsafe { (&raw const (*ms)[i]).cast::<NumberMeld>() };

						*slot_meld_base = base.into();

						#[expect(clippy::cast_possible_truncation)]
						{
							*slot_meld_source = meld_source_i as u8;
						}
					}
				}
			}

			let mut ji_ankous = ji.ankous;
			while let Some(offset) = ji_ankous.lowest_one() {
				ji_ankous &= !(0b1 << offset);

				// More melds than slots means this hand as a whole cannot have a valid decomposition.
				let Some(((_, slot_base), _)) = meld_slots.next() else { return false; };

				#[expect(clippy::cast_possible_truncation)]
				let base = t!(E) as u8 + ((offset as u8) << 1);
				*slot_base = unsafe { core::mem::transmute::<u8, Tile>(base) };
			}

			has_pair
		}

		let ts = ts.as_ref();
		let mut result = Self::default();
		result.has_more = inner(ts, &mut result.meld_ptr, &mut result.meld_base, &mut result.meld_source, &mut result.meld_source_len, &mut result.reds);
		result
	}
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<const NM: usize> Clone for Lookup<NM>
where
	[(); NM + 1]:,
{
	fn clone(&self) -> Self {
		Self {
			has_more: self.has_more,
			meld_ptr: self.meld_ptr,
			meld_base: self.meld_base,
			meld_source: self.meld_source,
			meld_source_len: self.meld_source_len,
			meld_source_i: self.meld_source_i,
			reds: self.reds,
		}
	}
}

const impl<const NM: usize> Default for Lookup<NM>
where
	[(); NM + 1]:,
{
	fn default() -> Self {
		Self {
			has_more: false,
			meld_ptr: [core::ptr::null(); _],
			meld_base: [t!(1m); _],
			meld_source: [0; _],
			meld_source_len: [1; _],
			meld_source_i: [0; _],
			reds: [0; _],
		}
	}
}

// `<Lookup<NM> as Iterator>::next` uses `core::simd::Simd<_, NM>`, but that type does not support zero length.
// So we need to make a separate bespoke impl for `Lookup<0>`.

impl Iterator for Lookup<0> {
	type Item = ([ScorableHandMeld; 0], ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		if !core::mem::replace(&mut self.has_more, false) {
			return None;
		}

		let pair_ptr = self.meld_ptr[0];
		let pair_representative = unsafe { pair_ptr.as_ref() };
		let pair_representative = pair_representative.copied().map_or_default(|m| m as u8) + (self.meld_base[0] as u8);
		let pair_representative = unsafe { core::mem::transmute::<u8, Tile>(pair_representative) };
		let pair = ScorableHandPair(pair_representative);
		Some(([], pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<const NM: usize> Iterator for Lookup<NM>
where
	[(); NM + 1]:,
	Assert<{ NM > 0 }>: IsTrue,
{
	type Item = ([ScorableHandMeld; NM], ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		if !self.has_more {
			return None;
		}

		let meld_ptr = core::simd::Simd::from_array(self.meld_ptr);
		// TODO(rustup): Use `SimdConstPtr::is_null()` when https://github.com/rust-lang/rust/issues/165043 is fixed.
		let is_number_meld = core::simd::cmp::SimdPartialEq::simd_ne(meld_ptr, core::simd::Simd::splat(core::ptr::null()));
		let meld_ptr = core::simd::ptr::SimdConstPtr::cast::<u8>(meld_ptr);
		let melds_and_pair = unsafe { core::simd::Simd::gather_select_ptr(meld_ptr, is_number_meld, core::simd::Simd::splat(0)) };

		let meld_base = unsafe { &*<*const [Tile; NM + 1]>::cast::<[u8; NM + 1]>(&raw const self.meld_base) };
		let tiles = core::simd::Simd::from_array(*meld_base) + (melds_and_pair & core::simd::Simd::splat(!(0b1 << 7)));

		let pair = {
			let pair_representative = unsafe { core::mem::transmute::<u8, Tile>(tiles[NM]) };
			ScorableHandPair(pair_representative)
		};

		let melds = {
			let melds = melds_and_pair.extract::<0, NM>();
			// 0b00______ => Ankou (2)
			// 0b10______ => Anjun (4)
			let ds = (melds >> core::simd::Simd::splat(6)) + core::simd::Simd::splat(2);
			let (lo, hi) = ds.interleave(tiles.extract::<0, NM>());
			let melds = [lo.to_array(), hi.to_array()];
			unsafe { core::mem::transmute_copy::<[[u8; NM]; 2], [ScorableHandMeld; NM]>(&melds) }
		};

		let meld_source_delta = cfg_select! {
			// TODO(rustup): Use `core::simd` once `Mask` stops sucking on RISC-V.
			all(target_arch = "riscv64", target_feature = "v") => unsafe {
				let to_increment: isize;
				let mut meld_source_delta = core::simd::Simd::<i8, { NM + 1 }>::splat(0);

				core::arch::asm!(
					"vsetivli zero, {len}, e8, m1, ta, ma",
					// let meld_source_i /* : v8:v8 */ = core::simd::Simd::from_array(self.meld_source_i);
					"vle8.v v8, ({meld_source_i})",
					// let meld_source_len /* : v9:v9 */ = core::simd::Simd::from_array(self.meld_source_len);
					"vle8.v v9, ({meld_source_len})",
					// let meld_source_i_plus_one /* : v10:v10 */ = meld_source_i + core::simd::Simd::splat(1);
					"vadd.vi v10, v8, 1",
					// let to_increment /* : v1:v1 */ = core::simd::cmp::SimdPartialOrd::simd_lt(meld_source_i_plus_one, meld_source_len);
					"vmsltu.vv v1, v10, v9",
					// if let Some(to_increment) = to_increment.first_set() {
					"vfirst.m {to_increment}, v1",
					"bltz {to_increment}, 1f",
					//     let to_increment = 0b1_u64 << to_increment;
					//     let to_reset /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment - 1);
					"vmsbf.m v0, v1",
					//     let meld_source_delta /* : v9:v9 */ = core::simd::Select::Select(to_reset, -core::simd::num::SimdUint::cast::<i8>(meld_source_i), core::simd::Simd::splat(0));
					"vrsub.vi v9, v8, 0",
					"vmv.v.i v10, 0",
					"vmerge.vvm v9, v10, v9, v0",
					//     let to_increment /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment);
					"vmsof.m v0, v1",
					//     let meld_source_delta /* : v9:v9 */ = core::simd::Select::select(to_increment, core::simd::Simd::splat(1), meld_source_delta);
					"vmerge.vim v9, v9, 1, v0",
					//     let meld_source_i /* : v8:v8 */ = core::num::SimdInt::cast::<u8>(core::simd::num::SimdUint::cast::<i8>(meld_source_i) + meld_source_delta);
					"vadd.vv v8, v8, v9",
					//     meld_source_i.copy_to_slice(&mut self.meld_source_i);
					"vse8.v v8, ({meld_source_i})",
					"vse8.v v9, ({meld_source_delta})",
					// }
					"1:",

					len = const NM + 1,
					meld_source_i = in(reg) self.meld_source_i.as_mut_ptr(),
					meld_source_len = in(reg) self.meld_source_len.as_ptr(),
					meld_source_delta = in(reg) meld_source_delta.as_mut_array().as_mut_ptr(),
					to_increment = out(reg) to_increment,
					out("v0") _,
					out("v1") _,
					out("v8") _,
					out("v9") _,
					out("v10") _,
					options(nostack),
				);

				if to_increment < 0 {
					self.has_more = false;
				}

				meld_source_delta
			},

			_ => {{
				let meld_source_i_previous = core::simd::Simd::from_array(self.meld_source_i);
				let meld_source_i_plus_one = meld_source_i_previous + core::simd::Simd::splat(1);
				let meld_source_len = core::simd::Simd::from_array(self.meld_source_len);
				let to_increment = core::simd::cmp::SimdPartialOrd::simd_lt(meld_source_i_plus_one, meld_source_len);
				if let Some(to_increment) = to_increment.first_set() {
					let to_increment = 0b1_u64 << to_increment;

					let to_reset = core::simd::Mask::<i8, _>::from_bitmask(to_increment - 1);
					let meld_source_i = core::simd::num::SimdUint::cast::<i8>(meld_source_i_previous);
					let meld_source_delta = core::simd::Select::select(to_reset, -meld_source_i, core::simd::Simd::splat(0));

					let to_increment = core::simd::Mask::<i8, _>::from_bitmask(to_increment);
					let meld_source_delta = core::simd::Select::select(to_increment, core::simd::Simd::splat(1), meld_source_delta);
					let meld_source_i = core::simd::num::SimdInt::cast::<u8>(meld_source_i + meld_source_delta);

					meld_source_i.copy_to_slice(&mut self.meld_source_i);
					meld_source_delta
				}
				else {
					self.has_more = false;
					core::simd::Simd::splat(0_i8)
				}
			}},
		};

		if self.has_more {
			let meld_source = core::simd::Simd::from_array(self.meld_source);
			let meld_source = core::simd::num::SimdUint::cast::<usize>(meld_source);

			let meld_ptr_offset = core::simd::Simd::gather_or_default(meld_source_delta.as_array(), meld_source);
			let meld_ptr_offset = core::simd::num::SimdInt::cast::<isize>(meld_ptr_offset);
			let stride = core::mem::size_of::<(Option<NumberMeld>, Meld<NumberMeld>)>().cast_signed();
			let meld_ptr_offset = meld_ptr_offset * core::simd::Simd::splat(stride);
			let meld_ptr_offset = core::simd::Select::select(is_number_meld, meld_ptr_offset, core::simd::Simd::splat(0));

			let meld_ptr = core::simd::ptr::SimdConstPtr::wrapping_offset(meld_ptr, meld_ptr_offset);
			let meld_ptr = core::simd::ptr::SimdConstPtr::cast::<NumberMeld>(meld_ptr);
			meld_ptr.copy_to_slice(&mut self.meld_ptr);
		}

		Some((melds, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<const NM: usize> ExactSizeIterator for Lookup<NM>
where
	[(); NM + 1]:,
	Self: Iterator,
{
	fn len(&self) -> usize {
		// This function is small enough that monomorphizing it for the unrolled fold is better.
		if self.has_more {
			self.meld_source_len.iter()
				.zip(&self.meld_source_i)
				.rfold(1, |acc, (&len, &i)| acc * usize::from(len) - usize::from(i))
		}
		else {
			0
		}
	}
}

impl<const NM: usize> core::iter::FusedIterator for Lookup<NM>
where
	[(); NM + 1]:,
	Self: Iterator,
{}

unsafe impl<const NM: usize> core::iter::TrustedLen for Lookup<NM>
where
	[(); NM + 1]:,
	Self: Iterator,
{}

unsafe impl<const NM: usize> Send for Lookup<NM>
where
	[(); NM + 1]:,
{}

unsafe impl<const NM: usize> Sync for Lookup<NM>
where
	[(); NM + 1]:,
{}

#[derive(Clone, Debug)]
pub(crate) struct LookupForNewTile<const NM: usize>
where
	[(); NM + 1]:,
	[(); (NM + 1) + 1]:,
	[(); (NM + 2).min(4)]:,
{
	current: core::array::IntoIter<([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair), { (NM + 2).min(4) }>,
	lookup: Lookup<{ NM + 1 }>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<const NM: usize> LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 1) + 1]:,
	[(); (NM + 2).min(4)]:,
{
	pub(crate) const fn new(lookup: Lookup<{ NM + 1 }>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		Self {
			// TODO(rustup): Use `Default::default()` when `core::array::IntoIter: const Default`.
			current: core::array::IntoIter::empty(),
			lookup,
			new_tile,
			tsumo_or_ron,
		}
	}
}

const impl<const NM: usize> Default for LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 1) + 1]:,
	[(); (NM + 2).min(4)]:,
{
	fn default() -> Self {
		Self {
			// TODO(rustup): Use `Default::default()` when `core::array::IntoIter: const Default`.
			current: core::array::IntoIter::empty(),
			lookup: Default::default(),
			new_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
		}
	}
}

impl<const NM: usize> Iterator for LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 1) + 1]:,
	[(); (NM + 2).min(4)]:,
	Assert<{ NM + 1 > 0 }>: IsTrue,
{
	type Item = ([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair);

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
		(current_len + lookup_lo, lookup_hi.map(|lookup_hi| current_len + lookup_hi * (NM + 2)))
	}
}

impl<const NM: usize> core::iter::FusedIterator for LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 1) + 1]:,
	[(); (NM + 2).min(4)]:,
	Self: Iterator,
{}

pub fn lookup_tenpai<const NT: usize>(ts: Tile37CountedMultiSet<NT>) -> Tile37Set {
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
		// Micro-optimization: `simd_eq().to_bitmask().count_ones()` generates silly code that widens the mask to `0xFF` as an intermediate step
		// because of how `core::simd::Mask` is designed internally to wrap `iN` instead of `i1`.
		// Doing `reduce_sum(select(simd_eq(), splat(1), splat(0)))` generates the intended code that does popcount on the mask.
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

#[derive(Clone, Debug)]
pub(crate) struct LookupForTenhou {
	current_a: core::array::IntoIter<([ScorableHandMeld; 3], ScorableHandFourthMeld, ScorableHandRegularPair), 4>,
	current_b: Option<([ScorableHandMeld; 4], ScorableHandPair, Tile37SetIntoIter)>,
	lookup: Lookup<4>,
	tiles: Tile37Set,
}

impl LookupForTenhou {
	pub(crate) fn new(ts: Tile37CountedMultiSet<14>) -> Self {
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

const impl Default for LookupForTenhou {
	fn default() -> Self {
		Self {
			// TODO(rustup): Use `Default::default()` when `core::array::IntoIter: const Default`.
			current_a: core::array::IntoIter::empty(),
			current_b: None,
			lookup: Default::default(),
			tiles: Default::default(),
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
				self.current_a = extract_fourth_meld::<3>(*ms, *pair, new_tile, TsumoOrRon::Tsumo, self.lookup.reds);
				continue;
			};
			break Some((ms, md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_a_len = self.current_a.len();
		(current_a_len, None)
	}
}

impl core::iter::FusedIterator for LookupForTenhou {}

struct Assert<const B: bool>;
trait IsTrue {}
impl IsTrue for Assert<true> {}

fn extract_fourth_meld<const NM: usize>(
	ms: [ScorableHandMeld; NM + 1],
	pair: ScorableHandPair,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
	reds: [u8; 3],
) -> core::array::IntoIter<([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair), { (NM + 2).min(4) }> {
	const ONES: Tile27Set = t27set![1m, 1p, 1s];
	const SEVENS: Tile27Set = t27set![7m, 7p, 7s];

	let winning_tile = new_tile;
	let new_tile = new_tile.remove_red();

	let mut current = ArrayVec::new();

	if pair.0 == new_tile {
		let md = ms[ms.len() - 1];
		let ms = unsafe { except(&ms, ms.len() - 1) };
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
		let ms = unsafe { except(&ms, i) };
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

/// # Safety
///
/// `ts_discard` must be within the bounds of `ts`.
unsafe fn except<T, const N: usize>(ts: &[T; N + 1], ts_discard: usize) -> [T; N]
where
	T: Clone,
{
	unsafe { core::hint::assert_unchecked(ts_discard <= N); }
	let mut result = [const { core::mem::MaybeUninit::uninit() }; N];
	result[..ts_discard].write_clone_of_slice(&ts[..ts_discard]);
	result[ts_discard..].write_clone_of_slice(&ts[(ts_discard + 1)..]);
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
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

	use crate::{append, CmpIgnoreRed as _, Number};
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		let mut result = ArrayVec::<_, 3>::new();
		m.for_each_tile(|t| result.push(t).unwrap());
		result.try_into().unwrap()
	}

	fn fourth_meld_to_tiles(m: ScorableHandFourthMeld) -> ArrayVec<([Tile; 4], Tile), 2> {
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

	fn eq_ignore_red<const NM: usize>(
		(mut ms1, mut md1, p1): ([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair),
		(mut ms2, mut md2, p2): ([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair),
	) -> bool
	where
		[(); NM + 1]:,
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

	fn append_and_sort<T, const N: usize>(arr: &mut [T; N], element: &mut T)
	where
		T: Copy + Ord,
		[(); N + 1]:,
	{
		let mut arr_ = append(*arr, *element);
		arr_.sort_unstable();
		arr.copy_from_slice(&arr_[..N]);
		*element = arr_[N];
	}

	#[test]
	fn to_meld() {
		for ma in melds_last() {
			for (ts, new_tile) in fourth_meld_to_tiles(ma) {
				let expected = ([], ma, ScorableHandRegularPair::antoi(t!(1p)));
				let actual: std::vec::Vec<_> =
					LookupForNewTile::new(
						Lookup::<1>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
						new_tile,
						TsumoOrRon::Tsumo,
					).collect();
				assert_eq!(actual, [expected], "{ma} on {new_tile} did not meld into {expected:?}, only into {actual:?}");
			}
		}

		// 124 -> X
		assert!(Lookup::<1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p]).unwrap()).next().is_none());
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
							([m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
						}
						else {
							([ma], mb, ScorableHandRegularPair::antoi(t!(1p)))
						};

					let ts = [t1, t2, t3, t4, t5, t6, t7];
					let actual: std::vec::Vec<_> =
						LookupForNewTile::new(
							Lookup::<2>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
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
								([m2, m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
							}
							else {
								([ma, mb], mc, ScorableHandRegularPair::antoi(t!(1p)))
							};

						let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10];
						let actual: std::vec::Vec<_> =
							LookupForNewTile::new(
								Lookup::<3>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
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
									([m1, m2, m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
								}
								else {
									([ma, mb, mc], md, ScorableHandRegularPair::antoi(t!(1p)))
								};

							let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13];
							let actual: std::vec::Vec<_> =
								LookupForNewTile::new(
									Lookup::<4>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
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
