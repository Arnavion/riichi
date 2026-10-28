use crate::{
	ADD1,
	KouWait,
	COMPLETE_HAND_TILES,
	IS_TENPAI_HAND_TILES,
	NON_ZERO, NumberTile,
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
	// Every third bit corresponds to an honor tile offset.
	//
	// Micro-optimization: Extracting and packing the bits into a u8 generates worse assembly.
	ankous: u32,
}

impl LookupHonors {
	fn new(key: u32) -> Option<Self> {
		let b0 = key & 0o1111111;
		let b1 = (key >> 1) & 0o1111111;
		let b2 = (key >> 2) & 0o1111111;

		let eq1 = !b1 & b0;
		let eq4 = b2;
		if eq1 | eq4 != 0 {
			return None;
		}

		let eq2 = b1 & !b0;
		let pair =
			if let Some(offset) = eq2.lowest_one() {
				if !eq2.is_power_of_two() {
					return None;
				}

				#[expect(clippy::cast_possible_truncation)]
				let h = ((offset / 3) as u8) << 1;
				Some(unsafe { core::mem::transmute::<u8, Honor>(h) })
			}
			else {
				None
			};

		let ankous = b1 & b0;

		Some(Self { pair, ankous })
	}

	fn waits(key: u32) -> u32 {
		let b0 = key & 0o1111111;
		let b1 = (key >> 1) & 0o1111111;
		let b2 = (key >> 2) & 0o1111111;
		let eq1 = !b1 & b0;
		let eq2 = b1 & !b0;
		let eq4 = b2;

		// If there is even a single tile with count 4, then the hand is not in tenpai so there are no waits.
		// Otherwise, the wait is either a tile with count 1 (that could become a pair) or a tile with count 2 (that could become a kou).
		let waits =
			if eq4 != 0 {
				return 0;
			}
			else if eq2.count_ones() <= 2 && eq1 == 0 {
				eq2
			}
			else if eq1.is_power_of_two() && eq2 == 0 {
				eq1
			}
			else {
				return 0;
			};

		waits.extract_bits(0o1111111)
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

/// The offset from the base tile for honor melds / pair. This is `0`, because the base tile for honor melds / pair is the actual honor tile.
/// See the comment on the `Lookup::meld_ptr` field.
static HONOR_MELD: NumberMeld = NumberMeld::K1;

mod numbers;

#[derive(Debug)]
pub(crate) struct Lookup<const NM: usize> {
	has_more: bool,
	// The first NM elements are melds, and the NM + 1'th element is the pair.
	// Honor melds / pair are stored as `meld_ptr` == `&HONOR_MELD` (which has value 0) and `meld_base` == the honor tile.
	// This way, `meld_ptr` holds offsets from `meld_base` to the real meld / pair representative tile regardless of whether it's a number or honor meld / pair.
	meld_ptr: [*const NumberMeld; core::gca!(ADD1::<NM>)],
	meld_base: [Tile; core::gca!(ADD1::<NM>)],
	// Maps each `meld_ptr` element to the index of its source decomposition parameters in `meld_source_len` and `meld_source_i`.
	meld_source: [u8; core::gca!(ADD1::<NM>)],
	meld_source_len: [u8; core::gca!(ADD1::<NM>)],
	meld_source_i: [u8; core::gca!(ADD1::<NM>)],
	reds: [u8; 3],
}

impl<const NM: usize> Lookup<NM> {
	pub(crate) fn new(ts: &Tile37CountedMultiSet<core::gca!(COMPLETE_HAND_TILES::<NM>)>) -> Self {
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
				for (start, decomposition) in numbers::lookup(key) {
					let Some((pair, melds)) = decomposition.first() else { return false; };

					let base = base as u8 + (start << 1);
					let base = unsafe { core::mem::transmute::<u8, NumberTile>(base) };

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
				let base = t!(E) as u8 + (((offset / 3) as u8) << 1);
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
const impl<const NM: usize> Clone for Lookup<NM> {
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

const impl<const NM: usize> Default for Lookup<NM> {
	fn default() -> Self {
		Self {
			has_more: false,
			meld_ptr: [&raw const HONOR_MELD; _],
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

		let pair_representative = unsafe { *self.meld_ptr[0] };
		let pair_representative = (pair_representative as u8) + (self.meld_base[0] as u8);
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
	Assert<core::gca!(NON_ZERO::<NM>)>: IsTrue,
{
	type Item = ([ScorableHandMeld; NM], ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		if !self.has_more {
			return None;
		}

		let meld_ptr = core::simd::Simd::from_array(self.meld_ptr);
		let meld_ptr = core::simd::ptr::SimdConstPtr::cast::<u8>(meld_ptr);
		let melds_and_pair = unsafe { core::simd::Simd::gather_ptr(meld_ptr) };

		let meld_base = unsafe { &*<*const [Tile; core::gca!(ADD1::<NM>)]>::cast::<[u8; core::gca!(ADD1::<NM>)]>(&raw const self.meld_base) };
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

		let meld_ptr_offset = cfg_select! {
			// TODO(rustup): Use `core::simd` once `Mask` stops sucking on RISC-V.
			all(target_arch = "riscv64", target_feature = "v") => unsafe {
				let to_increment: isize;
				let mut meld_ptr_offset = core::simd::Simd::<i8, core::gca!(ADD1::<NM>)>::splat(0);
				let meld_ptr_offset_raw: u64;

				core::arch::asm!(
					"vsetivli zero, {nm_plus_one}, e8, m1, ta, ma",
					// let meld_source_i_previous /* : v8:v8 */ = core::simd::Simd::from_array(self.meld_source_i);
					"vle8.v v8, ({meld_source_i})",
					// let meld_source_len /* : v9:v9 */ = core::simd::Simd::from_array(self.meld_source_len);
					"vle8.v v9, ({meld_source_len})",
					// let meld_source_i_plus_one /* : v10:v10 */ = meld_source_i_previous + core::simd::Simd::splat(1);
					"vadd.vi v10, v8, 1",
					// let to_increment /* : v1:v1 */ = core::simd::cmp::SimdPartialOrd::simd_lt(meld_source_i_plus_one, meld_source_len);
					"vmsltu.vv v1, v10, v9",
					// if let Some(to_increment) = to_increment.first_set() {
					"vfirst.m {to_increment}, v1",
					"bltz {to_increment}, 1f",
					//     let to_increment = 0b1_u64 << to_increment;
					//     let to_reset /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment - 1);
					"vmsbf.m v0, v1",
					//     let meld_source_i = core::simd::num::SimdUint::cast::<i8>(meld_source_i_previous);
					//     let meld_ptr_offset /* : v9:v9 */ = core::simd::Select::Select(to_reset, -core::simd::num::SimdUint::cast::<i8>(meld_source_i), core::simd::Simd::splat(0));
					"vrsub.vi v9, v8, 0",
					"vmv.v.i v10, 0",
					"vmerge.vvm v9, v10, v9, v0",
					//     let to_increment /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment);
					"vmsof.m v0, v1",
					//     let meld_ptr_offset /* : v9:v9 */ = core::simd::Select::select(to_increment, core::simd::Simd::splat(1), meld_ptr_offset);
					"vmerge.vim v9, v9, 1, v0",
					//     let meld_source_i /* : v8:v8 */ = core::num::SimdInt::cast::<u8>(core::simd::num::SimdUint::cast::<i8>(meld_source_i) + meld_ptr_offset);
					"vadd.vv v8, v8, v9",
					//     self.meld_source_i = meld_source_i.to_array();
					"vse8.v v8, ({meld_source_i})",
					//     let meld_source /* : v10:v10 */ = core::simd::Simd::from_array(self.meld_source);
					"vle8.v v10, ({meld_source})",
					//     let meld_ptr_offset = core::simd::num::SimdInt::cast::<u8>(meld_ptr_offset);
					//     let meld_ptr_offset /* :v8:v8 */ = meld_ptr_offset.swizzle_dyn(meld_source);
					"vrgather.vv v8, v9, v10",
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vmv.x.s {meld_ptr_offset_raw}, v8",
					// }
					"1:",

					nm_plus_one = const NM + 1,
					meld_source_i = in(reg) self.meld_source_i.as_mut_ptr(),
					meld_source_len = in(reg) self.meld_source_len.as_ptr(),
					to_increment = out(reg) to_increment,
					meld_source = in(reg) self.meld_source.as_ptr(),
					meld_ptr_offset_raw = lateout(reg) meld_ptr_offset_raw,
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

				let meld_ptr_offset_raw = &meld_ptr_offset_raw.to_le_bytes().map(u8::cast_signed)[..meld_ptr_offset.len()];
				meld_ptr_offset.as_mut_array().copy_from_slice(meld_ptr_offset_raw);
				meld_ptr_offset
			},

			_ => {{
				let meld_source_i_previous = core::simd::Simd::from_array(self.meld_source_i);
				let meld_source_i_plus_one = meld_source_i_previous + core::simd::Simd::splat(1);
				let meld_source_len = core::simd::Simd::from_array(self.meld_source_len);
				let to_increment = core::simd::cmp::SimdPartialOrd::simd_lt(meld_source_i_plus_one, meld_source_len);
				if let Some(to_increment) = to_increment.first_set() {
					#[expect(clippy::cast_possible_truncation)]
					let id = core::simd::Simd::from_array(core::array::from_fn(|i| i as i8));

					#[expect(clippy::cast_possible_truncation)]
					let to_increment = core::simd::Simd::splat(to_increment as i8);

					let to_reset = core::simd::cmp::SimdPartialOrd::simd_lt(id, to_increment);
					let meld_source_i = core::simd::num::SimdUint::cast::<i8>(meld_source_i_previous);
					let meld_ptr_offset = core::simd::Select::select(to_reset, -meld_source_i, core::simd::Simd::splat(0));

					let to_increment = core::simd::cmp::SimdPartialEq::simd_eq(id, to_increment);
					let meld_ptr_offset = core::simd::Select::select(to_increment, core::simd::Simd::splat(1), meld_ptr_offset);
					let meld_source_i = core::simd::num::SimdInt::cast::<u8>(meld_source_i + meld_ptr_offset);

					self.meld_source_i = meld_source_i.to_array();

					let meld_source = core::simd::Simd::from_array(self.meld_source);
					let meld_ptr_offset = core::simd::num::SimdInt::cast::<u8>(meld_ptr_offset);
					let meld_ptr_offset = meld_ptr_offset.swizzle_dyn(meld_source);
					core::simd::num::SimdUint::cast::<i8>(meld_ptr_offset)
				}
				else {
					self.has_more = false;
					core::simd::Simd::splat(0_i8)
				}
			}},
		};

		if self.has_more {
			let meld_ptr_offset = core::simd::num::SimdInt::cast::<isize>(meld_ptr_offset);
			let stride = core::mem::size_of::<(Option<NumberMeld>, Meld<NumberMeld>)>().cast_signed();
			let meld_ptr_offset = meld_ptr_offset * core::simd::Simd::splat(stride);

			let meld_ptr = core::simd::ptr::SimdConstPtr::wrapping_offset(meld_ptr, meld_ptr_offset);
			let meld_ptr = core::simd::ptr::SimdConstPtr::cast::<NumberMeld>(meld_ptr);
			self.meld_ptr = meld_ptr.to_array();
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
	Self: Iterator,
{}

unsafe impl<const NM: usize> core::iter::TrustedLen for Lookup<NM>
where
	Self: Iterator,
{}

unsafe impl<const NM: usize> Send for Lookup<NM> {}

unsafe impl<const NM: usize> Sync for Lookup<NM> {}

#[derive(Clone, Debug)]
pub(crate) struct LookupForNewTile<const NM: usize> {
	current: FourthMelds<NM>,
	lookup: Lookup<core::gca!(ADD1::<NM>)>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<const NM: usize> LookupForNewTile<NM> {
	pub(crate) const fn new(lookup: Lookup<core::gca!(ADD1::<NM>)>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		Self {
			current: Default::default(),
			lookup,
			new_tile,
			tsumo_or_ron,
		}
	}
}

const impl<const NM: usize> Default for LookupForNewTile<NM> {
	fn default() -> Self {
		Self {
			current: Default::default(),
			lookup: Default::default(),
			new_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
		}
	}
}

impl<const NM: usize> Iterator for LookupForNewTile<NM>
where
	Assert<core::gca!(NON_ZERO::<core::gca!(ADD1::<NM>)>)>: IsTrue,
{
	type Item = ([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current.next() else {
				let (ms, pair) = self.lookup.next()?;
				self.current = FourthMelds::new(ms, pair, self.new_tile, self.tsumo_or_ron, self.lookup.reds);
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
	Self: Iterator,
{}

pub fn lookup_tenpai<const NT: usize>(ts: Tile37CountedMultiSet<NT>) -> Tile37Set
where
	Assert<core::gca!(IS_TENPAI_HAND_TILES::<NT>)>: IsTrue,
{
	fn inner(ts: &Tile37MultiSet) -> Tile37Set {
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
		// - If one suit has 3n + 1 tiles, then the other three suits must have 3n tiles for the sum to be 3n + 1.
		//   In this case, the new tile must be in that suit and the pair will be from that suit.
		// - If two suits have 3n + 2 tiles then the other two suits must have 3n tiles for the sum to be 3n + 1.
		//   In this case, the new tile can be in either of the two suits and will convert that suit to 3n tiles, while the other suit will produce the pair.
		//
		// | 3n + 0 | 3n + 1 | 3n + 2 | May be in tenpai | Number of suits with | Suits looking
		// |        |        |        |                  |  more than 3n tiles  | for new tiles
		// +========+========+========+==================+======================+===============
		// |    3   |    1   |    0   | Valid            | 1                    | 3n + 1
		// |    2   |    0   |    2   | Valid            | 2                    | 3n + 2
		// |    1   |    2   |    1   | Invalid          | 3                    |
		// |    0   |    4   |    0   | Invalid          | 4                    |
		// |    0   |    1   |    3   | Invalid          | 4                    |
		// +--------+--------+--------+------------------+----------------------+---------------
		// |    4   |    0   |    0   | Impossible       |                      |
		// |    3   |    0   |    1   | Impossible       |                      |
		// |    2   |    2   |    0   | Impossible       |                      |
		// |    2   |    1   |    1   | Impossible       |                      |
		// |    1   |    3   |    0   | Impossible       |                      |
		// |    1   |    1   |    2   | Impossible       |                      |
		// |    1   |    0   |    3   | Impossible       |                      |
		// |    0   |    3   |    1   | Impossible       |                      |
		// |    0   |    2   |    2   | Impossible       |                      |
		// |    0   |    0   |    4   | Impossible       |                      |
		//
		// Thus the "Invalid" cases can be simplified into "more than two suits have more than 3n tiles".
		//
		// Micro-optimization: `mask.to_bitmask()` generates silly code that widens the mask bits to `0xFF` as an intermediate step
		// because of how `core::simd::Mask` is designed internally to wrap `iN` instead of `i1`.
		// Doing `reduce_or(select(mask, [1, 2, 4, 8], splat(0)))` generates better code than that.
		let has_excess = core::simd::cmp::SimdPartialOrd::simd_gt(excess, core::simd::Simd::splat(0));
		#[expect(clippy::cast_possible_truncation)]
		let has_excess =
			core::simd::num::SimdUint::reduce_or(core::simd::Select::select(
				has_excess,
				core::simd::Simd::splat(0b1_u8) << core::simd::Simd::from_array(core::array::from_fn(|i| i as _)),
				core::simd::Simd::splat(0),
			));
		let num_suits_with_excess = has_excess.count_ones();
		if num_suits_with_excess > 2 {
			return Default::default();
		}

		// If a suit has 3n tiles, it must already be valid, otherwise the hand as a whole is invalid.
		// This is an early check before building up the `SuitState`s for suits with excess.
		if has_excess & 0b0001 == 0b0000 && !numbers::is_valid(man) {
			return Default::default();
		}
		if has_excess & 0b0010 == 0b0000 && !numbers::is_valid(pin) {
			return Default::default();
		}
		if has_excess & 0b0100 == 0b0000 && !numbers::is_valid(sou) {
			return Default::default();
		}
		let ji_state =
			if has_excess & 0b1000 == 0b0000 {
				let ji_state = LookupHonors::new(ji.0);
				if ji_state.is_none() {
					return Default::default();
				}
				ji_state
			}
			else {
				LookupHonors::new(ji.0)
			};
		// Micro-optimization: `SuitState::default()` is created for suits that don't have excess, and returns an invalid `SuitState`
		// that cannot become valid with any tile. But it's not actually used anyway, since the code below only calls `.waits()` if the suit had excess.
		// The `::default()` is just there to make the `if-else` arms have the same type.
		// The alternative would be to return `None` / `Some(SuitState::new(...))` but that generates worse assembly.
		let man_state =
			if has_excess & 0b0001 == 0b0000 {
				Default::default()
			}
			else {
				numbers::SuitState::new(man)
			};
		let pin_state =
			if has_excess & 0b0010 == 0b0000 {
				Default::default()
			}
			else {
				numbers::SuitState::new(pin)
			};
		let sou_state =
			if has_excess & 0b0100 == 0b0000 {
				Default::default()
			}
			else {
				numbers::SuitState::new(sou)
			};

		// All suits valid => wait is in any suit with excess
		// One invalid suit => wait is in that suit
		// More than one invalid suit => not in tenpai
		let invalid =
			(
				u8::from(!man_state.is_valid()) |
				(u8::from(!pin_state.is_valid()) << 1) |
				(u8::from(!sou_state.is_valid()) << 2) |
				(u8::from(has_excess & 0b1000 != 0b0000 && ji_state.is_none()) << 3)
			) & has_excess;
		let may_wait_in =
			if invalid == 0 {
				has_excess
			}
			else if invalid.is_power_of_two() {
				invalid
			}
			else {
				return Default::default();
			};

		let mut valid = 0_u64;
		if may_wait_in & 0b0001 != 0b0000 {
			valid |= u64::from(man_state.waits());
		}
		if may_wait_in & 0b0010 != 0b0000 {
			valid |= u64::from(pin_state.waits()) << 9;
		}
		if may_wait_in & 0b0100 != 0b0000 {
			valid |= u64::from(sou_state.waits()) << 18;
		}
		if may_wait_in & 0b1000 != 0b0000 {
			valid |= u64::from(LookupHonors::waits(ji.0)) << 27;
		}

		let mut result = Tile34Set::default();
		result.present = valid;

		let mut result = result.stretch_red_fives();

		// `LookupHonors::waits` and `SuitState::waits` exclude tiles that already have four copies in `ts`,
		// but this does not account for fives, for which the presence of three regular fives means a fourth five must be excluded,
		// and the presence of a red five means a second red five must be excluded. So we handle fives manually.
		let fives_invalid = {
			// counts[12+:2] == 0b11 => regular fives can't be inserted => result[10 * suit + 4] = 0b1
			// counts[15] == 0b1 => red fives can't be inserted => result[10 * suit + 5] = 0b1
			// result[10 * suit + 4+:2] = (counts[12] & counts[13]) | (counts[15] << 1);
			let counts = ts.to_suits_simd().extract::<0, 3>();
			let counts = counts >> u32::from(Tile::offset(t!(5m)) * 3);
			let result = (counts & (counts >> 1) & core::simd::Simd::splat(0b1)) | ((counts >> 2) & core::simd::Simd::splat(0b10));
			let result = result << core::simd::Simd::from_array([Tile::offset(t!(1m)), Tile::offset(t!(1p)) + 1, Tile::offset(t!(1s)) + 2].map(u32::from));
			u64::from(core::simd::num::SimdUint::reduce_or(result) << Tile::offset(t!(5m)))
		};
		result.present &= !fives_invalid;

		result
	}

	let ts = Tile37MultiSet::from(ts);
	inner(&ts)
}

#[derive(Clone, Debug)]
#[derive_const(Default)]
pub(crate) struct LookupForTenhou {
	current_a: FourthMelds<3>,
	current_b: Option<([ScorableHandMeld; 4], ScorableHandPair, Tile37SetIntoIter)>,
	lookup: Lookup<4>,
	tiles: Tile37Set,
}

impl LookupForTenhou {
	pub(crate) fn new(ts: &Tile37CountedMultiSet<14>) -> Self {
		let lookup = Lookup::new(ts);
		let tiles = Tile37Set::from(ts.as_ref());
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
				self.current_a = FourthMelds::new(*ms, *pair, new_tile, TsumoOrRon::Tsumo, self.lookup.reds);
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

pub(crate) struct Assert<const B: bool>;
pub(crate) trait IsTrue {}
impl IsTrue for Assert<true> {}

#[derive(Debug)]
struct FourthMelds<const NM: usize> {
	ms: [ScorableHandMeld; core::gca!(ADD1::<NM>)],
	pair: ScorableHandPair,
	// Bit `0` is set if the pair contains the winning tile. Bit `i + 1` is set if `ms[i]` contains the winning tile.
	has_winning_tile: u8,
	winning_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
	reds: [u8; 3],
}

impl<const NM: usize> FourthMelds<NM> {
	fn new(
		ms: [ScorableHandMeld; core::gca!(ADD1::<NM>)],
		pair: ScorableHandPair,
		winning_tile: Tile,
		tsumo_or_ron: TsumoOrRon,
		reds: [u8; 3],
	) -> Self {
		let new_tile = winning_tile.remove_red();

		let has_winning_tile =
			ms.iter()
			.enumerate()
			.fold(u8::from(pair.0 as u8 == new_tile as u8), |acc, (i, &m)| {
				let [d, t] = m.parts();
				// Micro-optimization:
				//
				// This is equivalent to:
				//
				//     let present = match m {
				//         ScorableHandMeld::Ankou(t) => t == new_tile,
				//         ScorableHandMeld::Anjun(t1) => { let (t2, t3) = t1.shun_rest(); [Tile::from(t1), Tile::from(t2), Tile::from(t3)].contains(&new_tile),
				//         _ => unsafe { core::hint::unreachable_unchecked(); },
				//     };
				//
				// ... but that generates branches and does extra work in `shun_rest` for producing a red five.
				//
				// `ms` comes from lookup which is guaranteed to only have ankous and anjuns, and guaranteed to not have `FiveRed`s in either of those.
				// So we can do better with arithmetic on the discriminant and tile. Given `diff = new_tile.wrapping_sub(t)`:
				// - Ankou (0b010): expect t == new_tile => diff == 0
				// - Anjun (0b100): expect [t, t + 2, t + 4].contains(&new_tile) => diff <= 4
				let diff = (new_tile as u8).wrapping_sub(t);
				let max_diff = d & 0b100;
				let present = diff <= max_diff;
				acc | (u8::from(present) << (i + 1))
			});

		Self {
			ms,
			pair,
			has_winning_tile,
			winning_tile,
			tsumo_or_ron,
			reds,
		}
	}
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<const NM: usize> Clone for FourthMelds<NM> {
	fn clone(&self) -> Self {
		Self {
			ms: self.ms,
			pair: self.pair,
			has_winning_tile: self.has_winning_tile,
			winning_tile: self.winning_tile,
			tsumo_or_ron: self.tsumo_or_ron,
			reds: self.reds,
		}
	}
}

const impl<const NM: usize> Default for FourthMelds<NM> {
	fn default() -> Self {
		Self {
			ms: [ScorableHandMeld::Ankou(t!(1m)); _],
			pair: ScorableHandPair(t!(1m)),
			has_winning_tile: 0,
			winning_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
			reds: [0; _],
		}
	}
}

impl<const NM: usize> Iterator for FourthMelds<NM> {
	type Item = ([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		const ONES: Tile27Set = t27set![1m, 1p, 1s];
		const SEVENS: Tile27Set = t27set![7m, 7p, 7s];

		let i = self.has_winning_tile.lowest_one()?;
		self.has_winning_tile &= !(0b1 << i);

		let new_tile = self.winning_tile.remove_red();

		let (mut ms, mut md, mut pair) =
			if let Some(i) = i.checked_sub(1) {
				let i = i as usize;
				unsafe { core::hint::assert_unchecked(i < self.ms.len()); }
				let md = match self.ms[i] {
					ScorableHandMeld::Ankou(t) => ScorableHandFourthMeld::kou(t, self.tsumo_or_ron, KouWait::Shanpon),
					ScorableHandMeld::Anjun(t) => {
						let (t1, t2, t3) = t.shun();
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
								unsafe { core::hint::unreachable_unchecked(); }
							};
						ScorableHandFourthMeld::shun(t, self.tsumo_or_ron, wait)
					},

					_ => unsafe { core::hint::unreachable_unchecked(); },
				};
				let ms = unsafe { except(&self.ms, i) };
				let pair = ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Antoi, inner: self.pair };
				(ms, md, pair)
			}
			else {
				let md = self.ms[self.ms.len() - 1];
				let ms = unsafe { except(&self.ms, self.ms.len() - 1) };
				let pair_tag = match self.tsumo_or_ron {
					TsumoOrRon::Tsumo => ScorableHandRegularPairTag::Antoi,
					TsumoOrRon::Ron => ScorableHandRegularPairTag::Mintoi,
				};
				let pair = ScorableHandRegularPair { tag: pair_tag, inner: self.pair };
				(ms, ScorableHandFourthMeld::tanki(md), pair)
			};

		if self.reds != [0; _] {
			for (red, num_red) in t![0m, 0p, 0s].into_iter().zip(self.reds) {
				if num_red == 0 {
					continue;
				}

				let restored =
					if red == self.winning_tile {
						if md.is_tanki() {
							restore_red_to_kou(&mut pair.inner.0, red)
						}
						else {
							restore_red_to_fourth_meld(&mut md, red, None)
						}
					}
					else {
						restore_red_to_kou(&mut pair.inner.0, red) ||
						restore_red_to_fourth_meld(&mut md, red, Some(self.winning_tile)) ||
						ms.iter_mut().rev().any(|m| restore_red_to_meld(m, red))
					};
				debug_assert!(restored);
			}
		}

		Some((ms, md, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<const NM: usize> ExactSizeIterator for FourthMelds<NM> {
	fn len(&self) -> usize {
		self.has_winning_tile.count_ones() as usize
	}
}

impl<const NM: usize> core::iter::FusedIterator for FourthMelds<NM> {}

unsafe impl<const NM: usize> core::iter::TrustedLen for FourthMelds<NM> {}

/// # Safety
///
/// `ts_discard` must be within the bounds of `ts`.
unsafe fn except<T, const N: usize>(ts: &[T; core::gca!(ADD1::<N>)], ts_discard: usize) -> [T; N]
where
	T: Copy,
{
	// Micro-optimization: This is equivalent to:
	//
	//     unsafe { core::hint::assert_unchecked(ts_discard <= N); }
	//     let mut result = [const { core::mem::MaybeUninit::uninit() }; N];
	//     result[..ts_discard].write_copy_of_slice(&ts[..ts_discard]);
	//     result[ts_discard..].write_copy_of_slice(&ts[(ts_discard + 1)..]);
	//
	// ... but that generates calls to `memcpy`, whereas this version generates branchless conditional moves.
	core::array::from_fn(|i| if i < ts_discard { ts[i] } else { ts[i + 1] })
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

	use crate::{append, ArrayVec, CmpIgnoreRed as _, Number};
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		let mut result = ArrayVec::<_, 3>::new();
		m.for_each_tile(|t| result.push(t).unwrap());
		result.try_into().unwrap()
	}

	fn fourth_meld_and_pair_to_tiles(m: ScorableHandFourthMeld, ScorableHandPair(p_t): ScorableHandPair) -> ArrayVec<([Tile; 4], Tile), 2> {
		let mut result = ArrayVec::new();

		match m {
			m @ (
				ScorableHandFourthMeld::Ankou(_, KouWait::Tanki) |
				ScorableHandFourthMeld::Anjun(_, ShunWait::Tanki)
			) => {
				let [t1, t2, t3] = meld_to_tiles(m.into());
				result.push(([t1, t2, t3, p_t], p_t)).unwrap();
			},

			ScorableHandFourthMeld::Ankou(tile, KouWait::Shanpon) => {
				let t = tile.remove_red();
				result.push(([t, t, p_t, p_t], tile)).unwrap();
				if t != tile {
					result.push(([t, tile, p_t, p_t], t)).unwrap();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Kanchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t3, p_t, p_t], t2)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Penchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = NumberTile::from(t1);
				if t1.number() == Number::One {
					result.push(([t1.into(), t2.into(), p_t, p_t], t3.into())).unwrap();
				}
				else if t1.number() == Number::Seven {
					result.push(([t2.into(), t3.into(), p_t, p_t], t1.into())).unwrap();
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
				result.push(([t2, t3, p_t, p_t], t1)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenHigh) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t2, p_t, p_t], t3)).unwrap();
			},

			_ => unreachable!(),
		}

		result
	}

	fn pairs() -> [ScorableHandPair; 3] {
		t![1p, 1s, 9s].map(ScorableHandPair)
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
	) -> bool {
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
	{
		let mut arr_ = append(*arr, *element);
		arr_.sort_unstable();
		arr.copy_from_slice(&arr_[..N]);
		*element = arr_[N];
	}

	#[test]
	fn to_meld() {
		for p in pairs() {
			for ma in melds_last() {
				for (ts @ [t1, t2, t3, t4], new_tile) in fourth_meld_and_pair_to_tiles(ma, p) {
					let mut used = Tile37MultiSet::default();
					if used.try_extend([t1, t2, t3, t4, new_tile]).is_err() {
						continue;
					}

					let expected = ([], ma, ScorableHandRegularPair::antoi(p.0));

					let actual: std::vec::Vec<_> =
						LookupForNewTile::new(
							Lookup::<1>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
							new_tile,
							TsumoOrRon::Tsumo,
						).collect();

					assert!(
						actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
						"({ma}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
					);
				}
			}
		}

		// 124 -> X
		assert!(Lookup::<1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p]).unwrap()).next().is_none());
	}

	#[test]
	fn to_melds_2() {
		for p in pairs() {
			for ma in melds() {
				let ts @ [t1, t2, t3] = meld_to_tiles(ma);
				let mut used = Tile37MultiSet::default();
				used.try_extend(ts).unwrap();

				for mb in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
					for ([t4, t5, t6, t7], new_tile) in fourth_meld_and_pair_to_tiles(mb, p) {
						let mut used = used.clone();
						if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
							continue;
						}

						let expected =
							if let Some(mb) = mb.to_tanki() {
								let mut ms = [ma, mb];
								ms.sort_unstable();
								let [m3, m4] = ms;
								([m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
							}
							else {
								([ma], mb, ScorableHandRegularPair::antoi(p.0))
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
							"({ma}, {mb}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
						);
					}
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_3() {
		for p in pairs() {
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
						for ([t7, t8, t9, t10], new_tile) in fourth_meld_and_pair_to_tiles(mc, p) {
							let mut used = used.clone();
							if used.try_extend([t7, t8, t9, t10, new_tile]).is_err() {
								continue;
							}

							let expected =
								if let Some(mc) = mc.to_tanki() {
									let mut ms = [ma, mb, mc];
									ms.sort_unstable();
									let [m2, m3, m4] = ms;
									([m2, m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
								}
								else {
									([ma, mb], mc, ScorableHandRegularPair::antoi(p.0))
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
								"({ma}, {mb}, {mc}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
							);
						}
					}
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_4() {
		for p in pairs() {
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
							for ([t10, t11, t12, t13], new_tile) in fourth_meld_and_pair_to_tiles(md, p) {
								let mut used = used.clone();
								if used.try_extend([t10, t11, t12, t13, new_tile]).is_err() {
									continue;
								}

								let expected =
									if let Some(md) = md.to_tanki() {
										let mut ms = [ma, mb, mc, md];
										ms.sort_unstable();
										let [m1, m2, m3, m4] = ms;
										([m1, m2, m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
									}
									else {
										([ma, mb, mc], md, ScorableHandRegularPair::antoi(p.0))
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
									"({ma}, {mb}, {mc}, {md}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
								);
							}
						}
					}
				}
			}
		}
	}
}
