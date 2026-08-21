use generic_array::{
	ArrayLength,
	GenericArray,
	sequence::{GenericSequence as _, Remove, Shorten},
	typenum::{
		Prod,
		Sum,
		U1, U2, U3, U4, U14,
	},
};

use crate::{
	KouWait,
	NumberTile,
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

#[allow(clippy::enum_glob_use)]
mod numbers {
	use {Some as O, None as X};

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

	pub(super) fn is_valid((counts, len): (u32, u8)) -> bool {
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
		for (_, value) in lookup_values(counts) {
			let Some(has_pair_) = value_shape(value) else { return false; };
			if has_pair_ && core::mem::replace(&mut has_pair, true) {
				return false;
			}
		}

		true
	}

	/// Splits the given counts into one or more contiguous runs of tiles, and returns the decompositions of each run.
	///
	/// Each yielded tuple contains the offset of the start of the run (`0` for 1, `1` for 2, etc) as the first element and the decomposition of the run as the second element.
	/// The decompositions are relative to the start of the run.
	///
	/// For example, if counts is `0o3000` corresponding to 444, this has one contiguous run and the offset of the start is 3.
	/// Thus the iterator yields one element `(3, &[...])`.
	pub(super) fn lookup(counts: u32) -> impl Iterator<Item = (u8, &'static [(Option<NumberMeld>, Meld<NumberMeld>)])> {
		lookup_values(counts).map(|(start, value)| {
			let decompositions =
				if value < 0x8000 {
					let storage_start = usize::from(value & 0x0FFF);
					let len = usize::from((value >> 13) & 0b11) + 1;
					let storage_end = storage_start + len;
					unsafe { core::hint::assert_unchecked(storage_end <= STORAGE.len()); }
					&STORAGE[storage_start..storage_end]
				}
				else {
					&[]
				};
			(start, decompositions)
		})
	}

	/// Splits the given counts into one or more contiguous runs of tiles, and returns the parameters of the decompositions of each run.
	///
	/// Each yielded tuple contains the offset of the start of the run (`0` for 1, `1` for 2, etc) as the first element and the LUT value as the second element.
	///
	/// For example, if counts is `0o3000` corresponding to 444, this has one contiguous run and the offset of the start is 3.
	/// Thus the iterator yields one element `(3, ...)`.
	fn lookup_values(counts: u32) -> impl Iterator<Item = (u8, u16)> {
		let (digits, present) = digits_and_present(counts);
		runs(digits, present).map(|(shift, value)| {
			#[expect(clippy::cast_possible_truncation)]
			let start = (shift >> 1) as u8;
			(start, value)
		})
	}

	/// Splits the given counts into one or more contiguous runs of tiles, and returns the parameters of the decompositions of each run.
	///
	/// Each yielded tuple contains two times the offset of the start of the run (`0` for 1, `2` for 2, etc) as the first element and the LUT value as the second element.
	///
	/// For example, if counts is `0o3000` corresponding to 444, this has one contiguous run and the offset of the start is 3.
	/// Thus the iterator yields one element `(6, ...)`.
	fn runs(digits: u32, present: u32) -> impl Iterator<Item = (u32, u16)> {
		let mut is_start = run_starts(present);

		core::iter::from_fn(move || {
			if is_start == 0 {
				return None;
			}

			let shift = is_start.trailing_zeros();
			is_start &= !(0b1 << shift);

			let (index, _) = run_index(digits, present, shift);
			let value = lookup_value(index);

			Some((shift, value))
		})
	}

	/// Returns 2-bit flags for each digit: `0b01` if this digit is the first present digit of one or more present digits, otherwise `0b00`.
	const fn run_starts(present: u32) -> u32 {
		present & !(present << 2) & 0b01_01_01_01_01_01_01_01_01
	}

	/// Converts the given suit tile counts into the concatenation of all base-4 lookup digits and the concatenation of all 2-bit present flags.
	fn digits_and_present(counts: u32) -> (u32, u32) {
		// Convert each count to `count + 3` which forms one digit of the base-4 lookup index.
		// This does `+ 3` instead of `- 1` because the latter could propagate a borrow into adjacent counts,
		// whereas the former will not since a count is at most 4 and 4 + 3 = 7 still fits in the original 3 bits.
		//
		// The lower 2 bits of each digit form the digit of the lookup index. The upper bit (bit 2) indicates whether the count
		// was originally zero or not. If it was zero, the upper bit will be `0` (and the lower two bits will be `11`, which is nonsensical),
		// otherwise it will be `1`. This can be used for presence and run detection.
		let counts = counts + 0o333_333_333;

		let present = counts & 0o444_444_444;

		// Micro-optimization: We want to do an `extract_bits` on `counts` and another on `present`, but we can save instructions by combining them into one value,
		// running `extract_bits` on that, and then separating out the results.
		//
		// Micro-optimization: The combination could use a shift of 28 instead of 32, because `counts` only has 30 bits and the lower two bits of `present` are 0.
		// However shifting by 32 means RISC-V can use `add.uw` to do the combination instead of separate `slli 30; or`.
		let digits_and_present = (u64::from(present) << 32) | u64::from(counts);
		let digits_and_present = digits_and_present.extract_bits((0o333_333_333 << 33) | 0o333_333_333);
		// Concatenation of all digits. Also set bit 18, the bit right after the 9th digit, so that if a run starts at the 9th digit,
		// then it too has has a length marker.
		#[expect(clippy::cast_possible_truncation)]
		let digits = (digits_and_present as u32) & 0b11_11_11_11_11_11_11_11_11 | 0b1_00_00_00_00_00_00_00_00_00;
		// Concatenation of all 2-bit present flags.
		#[expect(clippy::cast_possible_truncation)]
		let present = (digits_and_present >> (2 * 9)) as u32;
		// Stretch each `present` flag into a 2-bit value, `0b00` / `0b11` for absent / present digits.
		let present = present | (present >> 1);

		(digits, present)
	}

	fn run_index(digits: u32, present: u32, shift: u32) -> (usize, u32) {
		let present = present >> shift;
		// Extract the digits of the run, plus one more bit for the length marker.
		// This extra bit is the lower bit of the next digit. The next digit is either an absent digit `0b11`,
		// or the current digit is the last (ninth) digit in which case the next bit was set to be `1` above.
		// In either case, the extra bit is `1`, which is exactly what the length marker needs to be.
		let run_mask = present ^ (present + 1);
		let index = (digits >> shift) & run_mask;
		let index = index as usize;
		unsafe { core::hint::assert_unchecked(index < (0b1 << 19)); }
		(index, run_mask)
	}

	fn lookup_value(index: usize) -> u16 {
		let layer2_i = usize::from(LAYER1[index >> 5]);
		unsafe { core::hint::assert_unchecked(layer2_i < LAYER2.len()); }
		let block = &LAYER2[layer2_i];
		block[index & 0b11111]
	}

	/// Returns `None` if the given LUT value has zero decompositions, otherwise `Some(has_pair)`.
	fn value_shape(value: u16) -> Option<bool> {
		// Values in the range `0x8000..` mean there are zero decompositions. Otherwise bit 12 is set if the decompositions have a pair.
		(value < 0x8000).then_some(value & 0x1000 != 0)
	}

	/// Precomputed lookup state of a particular number suit.
	#[derive(Copy)]
	#[derive_const(Clone)]
	pub(super) struct SuitState {
		digits: u32,
		present: u32,
		/// Bit `start * 2` is set if the run starting at `start` has no decompositions.
		bad: u32,
		/// Bit `start * 2` is set if the run starting at `start` has decompositions containing a pair.
		pairs: u32,
	}

	impl SuitState {
		pub(super) fn new(counts: u32) -> Self {
			let (digits, present) = digits_and_present(counts);

			let mut bad = 0;
			let mut pairs = 0;

			for (shift, value) in runs(digits, present) {
				let (run_bad, run_pairs) = run_bits(shift, value);
				bad |= run_bad;
				pairs |= run_pairs;
			}

			Self { digits, present, bad, pairs }
		}

		/// Returns `true` if all runs have one or more decompositions and there are 0 or 1 pairs.
		pub(super) fn is_valid(self) -> bool {
			self.bad == 0 && (self.pairs & self.pairs.wrapping_sub(1)) == 0
		}

		/// Returns `true` if adding the new tile specified by the given offset (`0` for 1, `1` for 2, etc) to this suit gives a valid `SuitState`.
		pub(super) fn is_valid_with(self, offset: u32) -> bool {
			let shift = offset * 2;

			if ((self.present & self.digits) >> shift) & 0b11 == 0b11 {
				// Suit already contains four copies of the new tile.
				return false;
			}

			// Add the given number to the suit. If it was previously absent, its digit was `0b11` (representing count = 0)
			// and must change to `0b00` (representing count = 1).
			let absent = !(self.present >> shift) & 0b1;
			let present = self.present | (0b11 << shift);
			let digits = self.digits + (0b1 << shift) - (absent << (shift + 2));

			let is_start = run_starts(present);
			// The run containing the new tile is the run with the largest start that is also <= the new tile.
			let is_start_le_new_tile = is_start & ((0b10 << shift) - 1);
			let shift = is_start_le_new_tile.highest_one();
			let shift = unsafe { shift.unwrap_unchecked() };

			let (index, run_mask) = run_index(digits, present, shift);

			let value = lookup_value(index);

			let (run_bad, run_pairs) = run_bits(shift, value);
			let run_mask = (run_mask >> 1) << shift;
			let bad = (self.bad & !run_mask) | run_bad;
			let pairs = (self.pairs & !run_mask) | run_pairs;
			let suit_state = Self { digits, present, bad, pairs };
			suit_state.is_valid()
		}
	}

	fn run_bits(shift: u32, value: u16) -> (u32, u32) {
		match value_shape(value) {
			Some(has_pair) => (0, u32::from(has_pair) << shift),
			None => (0b1 << shift, 0),
		}
	}
}

pub(crate) struct Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	has_more: bool,
	// The first NM elements are melds, and the NM + 1'th element is the pair.
	// Honor melds / pair are stored as `meld_ptr` == `&HONOR_MELD` (which has value 0) and `meld_base` == the honor tile.
	// This way, `meld_ptr` holds offsets from `meld_base` to the real meld / pair representative tile regardless of whether it's a number or honor meld / pair.
	meld_ptr: GenericArray<*const NumberMeld, Sum<NM, U1>>,
	meld_base: GenericArray<Tile, Sum<NM, U1>>,
	// Maps each `meld_ptr` element to the index of its source decomposition parameters in `meld_source_len` and `meld_source_i`.
	meld_source: GenericArray<u8, Sum<NM, U1>>,
	meld_source_len: GenericArray<u8, Sum<NM, U1>>,
	meld_source_i: GenericArray<u8, Sum<NM, U1>>,
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

impl<NM> Clone for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn clone(&self) -> Self {
		Self {
			has_more: self.has_more,
			meld_ptr: self.meld_ptr.clone(),
			meld_base: self.meld_base.clone(),
			meld_source: self.meld_source.clone(),
			meld_source_len: self.meld_source_len.clone(),
			meld_source_i: self.meld_source_i.clone(),
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
			.field("has_more", &self.has_more)
			.field("meld_ptr", &self.meld_ptr)
			.field("meld_base", &self.meld_base)
			.field("meld_source", &self.meld_source)
			.field("meld_source_len", &self.meld_source_len)
			.field("meld_source_i", &self.meld_source_i)
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
			has_more: false,
			meld_ptr: GenericArray::repeat(&raw const HONOR_MELD),
			meld_base: GenericArray::repeat(t!(1m)),
			meld_source: GenericArray::repeat(0),
			meld_source_len: GenericArray::repeat(1),
			meld_source_i: GenericArray::repeat(0),
			reds: [0; _],
		}
	}
}

impl<NM> Iterator for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength> + ArrayLength,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		fn inner<const NM_: usize, const NM_PLUS_ONE: usize>(
			self_has_more: &mut bool,
			self_meld_ptr: &mut [*const NumberMeld; NM_PLUS_ONE],
			self_meld_base: &[Tile; NM_PLUS_ONE],
			self_meld_source: &[u8; NM_PLUS_ONE],
			self_meld_source_len: &[u8; NM_PLUS_ONE],
			self_meld_source_i: &mut [u8; NM_PLUS_ONE],
		) -> ([ScorableHandMeld; NM_], ScorableHandPair) {
			const { assert!(NM_PLUS_ONE == NM_ + 1); }

			let meld_ptr = core::simd::Simd::from_array(*self_meld_ptr);
			let meld_ptr = core::simd::ptr::SimdConstPtr::cast::<u8>(meld_ptr);
			let melds_and_pair = unsafe { core::simd::Simd::gather_ptr(meld_ptr) };

			let meld_base = unsafe { &*<*const [Tile; NM_PLUS_ONE]>::cast::<[u8; NM_PLUS_ONE]>(self_meld_base) };
			let tiles = core::simd::Simd::from_array(*meld_base) + (melds_and_pair & core::simd::Simd::splat(!(0b1 << 7)));

			let pair = {
				let pair_representative = unsafe { core::mem::transmute::<u8, Tile>(tiles[NM_]) };
				ScorableHandPair(pair_representative)
			};

			let melds = {
				// 0b00______ => Ankou (2)
				// 0b10______ => Anjun (4)
				let melds = melds_and_pair.extract::<0, NM_>();
				let ds = (melds >> core::simd::Simd::splat(6)) + core::simd::Simd::splat(2);
				let (lo, hi) = ds.interleave(tiles.extract::<0, NM_>());
				let melds = [lo.to_array(), hi.to_array()];
				unsafe { core::mem::transmute_copy::<[[u8; NM_]; 2], [ScorableHandMeld; NM_]>(&melds) }
			};

			let meld_ptr_offset = cfg_select! {
				// TODO(rustup): Use `core::simd` once `Mask` stops sucking on RISC-V.
				all(target_arch = "riscv64", target_feature = "v") => unsafe {
					let to_increment: isize;
					let mut meld_ptr_offset = core::simd::Simd::<i8, NM_PLUS_ONE>::splat(0);
					let meld_ptr_offset_raw: u64;

					core::arch::asm!(
						"vsetivli zero, {nm_plus_one}, e8, m1, ta, ma",
						// let meld_source_i_previous /* : v8:v8 */ = core::simd::Simd::from_array(*self_meld_source_i);
						"vle8.v v8, ({meld_source_i})",
						// let meld_source_len /* : v9:v9 */ = core::simd::Simd::from_array(*self_meld_source_len);
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
						//     *self_meld_source_i = meld_source_i.to_array();
						"vse8.v v8, ({meld_source_i})",
						//     let meld_source /* : v10:v10 */ = core::simd::Simd::from_array(*self_meld_source);
						"vle8.v v10, ({meld_source})",
						//     let meld_ptr_offset = core::simd::num::SimdInt::cast::<u8>(meld_ptr_offset);
						//     let meld_ptr_offset /* :v8:v8 */ = meld_ptr_offset.swizzle_dyn(meld_source);
						"vrgather.vv v8, v9, v10",
						"vsetivli zero, 1, e64, m1, ta, ma",
						"vmv.x.s {meld_ptr_offset_raw}, v8",
						// }
						"1:",

						nm_plus_one = const NM_ + 1,
						meld_source_i = in(reg) self_meld_source_i.as_mut_ptr(),
						meld_source_len = in(reg) self_meld_source_len.as_ptr(),
						to_increment = out(reg) to_increment,
						meld_source = in(reg) self_meld_source.as_ptr(),
						meld_ptr_offset_raw = lateout(reg) meld_ptr_offset_raw,
						out("v0") _,
						out("v1") _,
						out("v8") _,
						out("v9") _,
						out("v10") _,
						options(nostack),
					);

					if to_increment < 0 {
						*self_has_more = false;
					}

					let meld_ptr_offset_raw = &meld_ptr_offset_raw.to_le_bytes().map(u8::cast_signed)[..meld_ptr_offset.len()];
					meld_ptr_offset.as_mut_array().copy_from_slice(meld_ptr_offset_raw);
					meld_ptr_offset
				},

				_ => {{
					let meld_source_i_previous = core::simd::Simd::from_array(*self_meld_source_i);
					let meld_source_i_plus_one = meld_source_i_previous + core::simd::Simd::splat(1);
					let meld_source_len = core::simd::Simd::from_array(*self_meld_source_len);
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

						*self_meld_source_i = meld_source_i.to_array();

						let meld_source = core::simd::Simd::from_array(*self_meld_source);
						let meld_ptr_offset = core::simd::num::SimdInt::cast::<u8>(meld_ptr_offset);
						let meld_ptr_offset = meld_ptr_offset.swizzle_dyn(meld_source);
						core::simd::num::SimdUint::cast::<i8>(meld_ptr_offset)
					}
					else {
						*self_has_more = false;
						core::simd::Simd::splat(0_i8)
					}
				}},
			};

			if *self_has_more {
				let meld_ptr_offset = core::simd::num::SimdInt::cast::<isize>(meld_ptr_offset);
				let stride = core::mem::size_of::<(Option<NumberMeld>, Meld<NumberMeld>)>().cast_signed();
				let meld_ptr_offset = meld_ptr_offset * core::simd::Simd::splat(stride);

				let meld_ptr = core::simd::ptr::SimdConstPtr::wrapping_offset(meld_ptr, meld_ptr_offset);
				let meld_ptr = core::simd::ptr::SimdConstPtr::cast::<NumberMeld>(meld_ptr);
				*self_meld_ptr = meld_ptr.to_array();
			}

			(melds, pair)
		}

		if !self.has_more {
			return None;
		}

		// To work around being unable to create `Simd<_, NM::USIZE>` etc, we monomorphize the impl for `NM = 1..=4`
		// (`NM_PLUS_ONE = 2..=5`) and dispatch to the right one. The correct `match` arm is chosen at compile time
		// and the rest are dropped, so this becomes static dispatch with no overhead.

		macro_rules! static_dispatch_inner {
			($(( $nm:literal $nm_plus_one:literal ))*) => {{
				const { assert!((1..=4).contains(&NM::USIZE)); }
				match NM::USIZE {
					$(
						$nm => {
							let self_meld_ptr = unsafe { &mut *<*mut GenericArray<*const NumberMeld, Sum<NM, U1>>>::cast::<[*const NumberMeld; $nm_plus_one]>(&mut self.meld_ptr) };
							let self_meld_base = unsafe { &*<*const GenericArray<Tile, Sum<NM, U1>>>::cast::<[Tile; $nm_plus_one]>(&self.meld_base) };
							let self_meld_source = unsafe { &*<*const GenericArray<u8, Sum<NM, U1>>>::cast::<[u8; $nm_plus_one]>(&self.meld_source) };
							let self_meld_source_len = unsafe { &*<*const GenericArray<u8, Sum<NM, U1>>>::cast::<[u8; $nm_plus_one]>(&self.meld_source_len) };
							let self_meld_source_i = unsafe { &mut *<*mut GenericArray<u8, Sum<NM, U1>>>::cast::<[u8; $nm_plus_one]>(&mut self.meld_source_i) };
							let (melds, pair) = inner::<$nm, $nm_plus_one>(
								&mut self.has_more,
								self_meld_ptr,
								self_meld_base,
								self_meld_source,
								self_meld_source_len,
								self_meld_source_i,
							);
							let melds = unsafe { core::mem::transmute_copy::<[ScorableHandMeld; $nm], GenericArray<ScorableHandMeld, NM>>(&melds) };
							(melds, pair)
						},
					)*
					_ => unreachable!(),
				}
			}};
		}

		Some(static_dispatch_inner!((1 2) (2 3) (3 4) (4 5)))
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
{
	current: FourthMelds<NM>,
	lookup: Lookup<Sum<NM, U1>>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<NM> LookupForNewTile<NM>
where
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
{
	pub(crate) fn new(lookup: Lookup<Sum<NM, U1>>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
	FourthMelds<NM>: Iterator<Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair)>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair);

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
		(current_len + lookup_lo, lookup_hi.map(|lookup_hi| current_len + lookup_hi * (NM::USIZE + 2)))
	}
}

impl<NM> core::iter::FusedIterator for LookupForNewTile<NM>
where
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
		for (expected_valid_lookup, suit) in expected_valid_lookups.into_iter().zip([man, pin, sou]) {
			if expected_valid_lookup && !numbers::is_valid(suit) {
				return Default::default();
			}
		}
		if expected_valid_lookups[3] && LookupHonors::new(ji.0).is_none() {
			return Default::default();
		}

		let Ok(man) = update_number_candidates(&mut candidates, man, expected_valid_lookups[0], &MAN) else { return Default::default(); };
		let Ok(pin) = update_number_candidates(&mut candidates, pin, expected_valid_lookups[1], &PIN) else { return Default::default(); };
		let Ok(sou) = update_number_candidates(&mut candidates, sou, expected_valid_lookups[2], &SOU) else { return Default::default(); };
		let Ok(ji_key) = update_honor_candidates(&mut candidates, ji.0, expected_valid_lookups[3], &JI) else { return Default::default(); };

		candidates &= ts34.tenpai();

		let mut valid = 0_u64;
		for (i, suit_state) in [man, pin, sou].into_iter().enumerate() {
			let Some(suit_state) = suit_state else { continue; };
			valid |= filter_offsets((candidates.present >> (i * 9)) & 0o777, |offset| suit_state.is_valid_with(offset)) << (i * 9);
		}
		if let Some(ji_key) = ji_key {
			valid |= filter_offsets(candidates.present >> 27, |offset| LookupHonors::new(ji_key + (0b1 << (offset * 3))).is_some()) << 27;
		}

		let mut result = Tile34Set::default();
		result.present = valid;
		result.stretch_red_fives() & Tile37Set::insertable(ts)
	}

	fn update_number_candidates(
		candidates: &mut Tile34Set,
		(counts, len): (u32, u8),
		expected_valid_lookup: bool,
		suit_set: &Tile34Set,
	) -> Result<Option<numbers::SuitState>, ()> {
		if expected_valid_lookup {
			Ok(None)
		}
		else {
			let suit_state = numbers::SuitState::new(counts);
			let wait_only_in_this_suit = candidates.clone() & suit_set.clone() == *candidates;
			if !wait_only_in_this_suit && (len % 3 == 1 || !suit_state.is_valid()) {
				*candidates &= suit_set.clone();
				if candidates.is_empty() {
					return Err(());
				}
			}
			Ok(Some(suit_state))
		}
	}

	fn update_honor_candidates(
		candidates: &mut Tile34Set,
		key: u32,
		expected_valid_lookup: bool,
		suit_set: &Tile34Set,
	) -> Result<Option<u32>, ()> {
		if expected_valid_lookup {
			Ok(None)
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

	fn filter_offsets(mut offsets: u64, mut f: impl FnMut(u32) -> bool) -> u64 {
		let mut result = 0;
		while let Some(offset) = offsets.lowest_one() {
			offsets &= !(0b1 << offset);
			result |= u64::from(f(offset)) << offset;
		}
		result
	}

	let ts = Tile37MultiSet::from(ts);
	inner(&ts)
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LookupForTenhou {
	current_a: FourthMelds<U3>,
	current_b: Option<(GenericArray<ScorableHandMeld, U4>, ScorableHandPair, Tile37SetIntoIter)>,
	lookup: Lookup<U4>,
	tiles: Tile37Set,
}

impl LookupForTenhou {
	pub(crate) fn new(ts: &Tile37CountedMultiSet<U14>) -> Self {
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
			break Some((ms.into(), md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_a_len = self.current_a.len();
		(current_a_len, None)
	}
}

impl core::iter::FusedIterator for LookupForTenhou {}

struct FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	ms: GenericArray<ScorableHandMeld, Sum<NM, U1>>,
	pair: ScorableHandPair,
	// Bit `0` is set if the pair contains the winning tile. Bit `i + 1` is set if `ms[i]` contains the winning tile.
	has_winning_tile: u8,
	winning_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
	reds: [u8; 3],
}

impl<NM> FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn new(
		ms: GenericArray<ScorableHandMeld, Sum<NM, U1>>,
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

impl<NM> Clone for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn clone(&self) -> Self {
		Self {
			ms: self.ms.clone(),
			pair: self.pair,
			has_winning_tile: self.has_winning_tile,
			winning_tile: self.winning_tile,
			tsumo_or_ron: self.tsumo_or_ron,
			reds: self.reds,
		}
	}
}

impl<NM> core::fmt::Debug for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("FourthMelds")
			.field("ms", &self.ms)
			.field("pair", &self.pair)
			.field("has_winning_tile", &self.has_winning_tile)
			.field("winning_tile", &self.winning_tile)
			.field("tsumo_or_ron", &self.tsumo_or_ron)
			.field("reds", &self.reds)
			.finish()
	}
}

impl<NM> Default for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn default() -> Self {
		Self {
			ms: GenericArray::repeat(ScorableHandMeld::Ankou(t!(1m))),
			pair: ScorableHandPair(t!(1m)),
			has_winning_tile: 0,
			winning_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
			reds: [0; _],
		}
	}
}

impl<NM> Iterator for FourthMelds<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<ScorableHandMeld, Sum<NM, U1>>:
		Copy +
		Remove<ScorableHandMeld, Sum<NM, U1>, Output = GenericArray<ScorableHandMeld, NM>> +
		Shorten<ScorableHandMeld, Shorter = GenericArray<ScorableHandMeld, NM>>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair);

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
				let (_, ms) = unsafe { Remove::remove_unchecked(self.ms, i) };
				let pair = ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Antoi, inner: self.pair };
				(ms, md, pair)
			}
			else {
				let (ms, md) = Shorten::pop_back(self.ms);
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

impl<NM> ExactSizeIterator for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{
	fn len(&self) -> usize {
		self.has_winning_tile.count_ones() as usize
	}
}

impl<NM> core::iter::FusedIterator for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{}

unsafe impl<NM> core::iter::TrustedLen for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{}

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

	use crate::{ArrayVec, CmpIgnoreRed as _, Number};
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		let mut result = ArrayVec::<_, U3>::new();
		m.for_each_tile(|t| result.push(t).unwrap());
		GenericArray::try_from(result).unwrap().into()
	}

	fn fourth_meld_and_pair_to_tiles(m: ScorableHandFourthMeld, ScorableHandPair(p_t): ScorableHandPair) -> ArrayVec<([Tile; 4], Tile), U2> {
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
		for p in pairs() {
			for ma in melds_last() {
				for (ts @ [t1, t2, t3, t4], new_tile) in fourth_meld_and_pair_to_tiles(ma, p) {
					let mut used = Tile37MultiSet::default();
					if used.try_extend([t1, t2, t3, t4, new_tile]).is_err() {
						continue;
					}

					let expected = ([].into(), ma, ScorableHandRegularPair::antoi(p.0));
					let actual: std::vec::Vec<_> =
						LookupForNewTile::new(
							Lookup::new(&Tile37CountedMultiSet::new((&ts).into()).unwrap().insert(new_tile).unwrap()),
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
		assert!(Lookup::<U1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p].into()).unwrap()).next().is_none());
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
								([m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
							}
							else {
								([ma].into(), mb, ScorableHandRegularPair::antoi(p.0))
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
									([m2, m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
								}
								else {
									([ma, mb].into(), mc, ScorableHandRegularPair::antoi(p.0))
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
										([m1, m2, m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
									}
									else {
										([ma, mb, mc].into(), md, ScorableHandRegularPair::antoi(p.0))
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
