#![allow(clippy::enum_glob_use)]

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

pub(super) const EMPTY: &[(Option<NumberMeld>, Meld<NumberMeld>)] = &[(None, M0)];

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

/// Precomputed lookup state of a particular number suit.
#[derive(Clone, Copy, Default)]
pub(super) struct SuitState {
	digits: u32,
	present: u32,
	/// Bit `offset * 2` is set if `offset` is the first offset or if the previous offset is absent,
	/// ie a new run would start at `offset` if it were present.
	potential_starts: u32,
	/// `true` if all runs have one or more decompositions and there are 0 or 1 pairs.
	is_valid: bool,
	/// Bit `offset` is set if adding a new tile at `offset` (`0` for 1, `1` for 2, etc) could possibly give a valid `SuitState`.
	///
	/// Bits that are not set here correspond to offsets which are guaranteed to not give a valid `SuitState`.
	may_make_valid: u32,
	/// Bit `offset` is set if adding a new tile at `offset` (`0` for 1, `1` for 2, etc) touches every run with a pair.
	///
	/// If the merged run containing the new tile has a pair, then the corresponding bit must have been set here for the merged run to be valid.
	touches_all_pairs: u32,
}

impl SuitState {
	pub(super) fn new((counts, len): (u32, u8)) -> Self {
		let (digits, present) = digits_and_present(counts);

		let potential_starts = ((!present << 2) | 0b1) & 0b01_01_01_01_01_01_01_01_01;

		// Runs are decomposed individually, and adding a new tile merges all the runs it touches while leaving the others unchanged.
		// So for the result to be valid, the new tile must touch at least one run (otherwise it's an isolated single tile and cannot have a valid decomposition),
		// and it must touch every bad run (so that they have a chance to become valid runs). Furthermore, if the suit has 3n + 1 tiles,
		// then adding the new tile makes that 3n + 2, which means the new tile must leave at most one run with a pair untouched.
		// Otherwise if the suit has 3n + 2 tiles, then adding the new tile makes that 3n + 3, which means the new tile must touch every run with a pair.

		let mut num_bad = 0_usize;
		let mut num_pairs = 0_usize;
		let mut touches_any = 0_u32;
		let mut touches_all_bad = u32::MAX;
		let mut touches_all_pairs = u32::MAX;
		let mut touches_all_but_one_pair = u32::MAX;

		for (start_shift, value, run_mask) in runs(digits, present) {
			let (run_is_bad, run_has_pair) = match value_shape(value) {
				Some(run_has_pair) => (false, run_has_pair),
				None => (true, false),
			};

			num_bad += usize::from(run_is_bad);
			num_pairs += usize::from(run_has_pair);

			// `run_mask` has two bits per tile and one extra leading bit.
			let run = ((0b1 << (run_mask.count_ones() / 2)) - 1) << (start_shift / 2);
			let touches = (run | (run << 1) | (run >> 1)) & 0o777;
			touches_any |= touches;
			if run_is_bad {
				touches_all_bad &= touches;
			}
			// An offset that does not touch this run leaves at most one pair untouched only if it touched all previous pairs.
			if run_has_pair {
				touches_all_but_one_pair = (touches_all_but_one_pair & touches) | touches_all_pairs;
				touches_all_pairs &= touches;
			}
		}

		let is_valid = num_bad == 0 && num_pairs <= 1;

		let touches_required_pairs = if len % 3 == 2 { touches_all_pairs } else { touches_all_but_one_pair };
		let may_make_valid = touches_any & touches_all_bad & touches_required_pairs;

		Self {
			digits,
			present,
			potential_starts,
			is_valid,
			may_make_valid,
			touches_all_pairs,
		}
	}

	/// Returns `true` if all runs have one or more decompositions and there are 0 or 1 pairs.
	pub(super) fn is_valid(self) -> bool {
		self.is_valid
	}

	/// Returns the set of offsets (bit `0` for 1, `1` for 2, etc) for which adding a new tile corresponding to that offset
	/// gives a valid `SuitState`.
	pub(super) fn waits(self) -> u32 {
		let offsets = self.may_make_valid;

		let eq4 = self.present & self.digits;
		let eq4 = eq4 & (eq4 >> 1);

		// Bit `offset` is set if the merged run containing the new tile has no decompositions, or if the suit already contains four copies of that tile.
		let mut bad = 0;

		// Bit `offset` is set if the merged run containing the new tile has decompositions containing a pair.
		let mut has_pair = 0;

		let mut remaining = offsets;
		while let Some(offset) = remaining.lowest_one() {
			remaining &= !(0b1 << offset);

			let shift = offset * 2;

			// Add the new tile to the suit.
			//
			// If it was previously absent, then its digit was `0b11`, and adding one to it overflows into the next digit,
			// so we need to subtract one from the next digit.
			//
			// If four copies of it were present, then its digit was `0b11`, and adding one to it overflows into the next digit,
			// even if we subtract one from the next digit. The resulting digits are garbage. But this case will be ignored anyway because of `eq4` below.
			let absent = !(self.present >> shift) & 0b1;
			let present = self.present | (0b11 << shift);
			let digits = self.digits + (0b1 << shift) - (absent << (shift + 2));

			// The run containing the new tile is the run with the largest `potential_start` that is also <= the new tile.
			let is_start_le_new_tile = self.potential_starts & ((0b10 << shift) - 1);
			let start_shift = is_start_le_new_tile.highest_one();
			let start_shift = unsafe { start_shift.unwrap_unchecked() };

			let (index, _) = run_index(digits, present, start_shift);

			let value = lookup_value(index);

			bad |= ((u32::from(value) >> 15) | ((eq4 >> shift) & 0b1)) << offset;
			has_pair |= ((u32::from(value) >> 12) & 0b1) << offset;
		}

		offsets & !bad & (!has_pair | self.touches_all_pairs)
	}
}

/// Splits the given counts into one or more contiguous runs of tiles, and returns the parameters of the decompositions of each run.
///
/// Each yielded tuple contains the offset of the start of the run (`0` for 1, `1` for 2, etc) as the first element and the LUT value as the second element.
///
/// For example, if counts is `0o3000` corresponding to 444, this has one contiguous run and the offset of the start is 3.
/// Thus the iterator yields one element `(3, ...)`.
fn lookup_values(counts: u32) -> impl Iterator<Item = (u8, u16)> {
	let (digits, present) = digits_and_present(counts);
	runs(digits, present).map(|(start_shift, value, _)| {
		#[expect(clippy::cast_possible_truncation)]
		let start = (start_shift >> 1) as u8;
		(start, value)
	})
}

/// Returns `None` if the given LUT value has zero decompositions, otherwise `Some(has_pair)`.
fn value_shape(value: u16) -> Option<bool> {
	// Values in the range `0x8000..` mean there are zero decompositions. Otherwise bit 12 is set if the decompositions have a pair.
	(value < 0x8000).then_some(value & 0x1000 != 0)
}

/// Splits the given counts into one or more contiguous runs of tiles, and returns the parameters of the decompositions of each run.
///
/// Each yielded tuple contains two times the offset of the start of the run (`0` for 1, `2` for 2, etc) as the first element, the LUT value as the second element
/// and the run mask returned by `run_index` as the third element.
///
/// For example, if counts is `0o3000` corresponding to 444, this has one contiguous run and the offset of the start is 3.
/// Thus the iterator yields one element `(6, ..., ...)`.
fn runs(digits: u32, present: u32) -> impl Iterator<Item = (u32, u16, u32)> {
	let mut is_start = present & !(present << 2) & 0b01_01_01_01_01_01_01_01_01;

	core::iter::from_fn(move || {
		if is_start == 0 {
			return None;
		}

		let start_shift = is_start.trailing_zeros();
		is_start &= !(0b1 << start_shift);

		let (index, run_mask) = run_index(digits, present, start_shift);
		let value = lookup_value(index);

		Some((start_shift, value, run_mask))
	})
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
	let digits_and_present = cfg_select! {
		all(target_arch = "x86_64", target_feature = "bmi2") =>
			unsafe { core::arch::x86_64::_pext_u64(digits_and_present, (0o333_333_333 << 33) | 0o333_333_333) },

		_ => {{
			const fn step(x: u64, mask: u64, shift: u8) -> u64 {
				let mask = mask | (mask << 33);
				(x & !mask) | ((x & mask) >> shift)
			}

			//                                                  0ii_0hh_0gg_0ff_0ee_0dd_0cc_0bb_0aa
			let digits_and_present = digits_and_present & ((0o333_333_333 << 33) | 0o333_333_333);
			//                                               -> 0ii_00h_hgg_00f_fee_00d_dcc_00b_baa
			let digits_and_present = step(digits_and_present, 0b000_011_000_011_000_011_000_011_000, 1);
			//                                               -> 0ii_000_0hh_ggf_fee_000_0dd_ccb_baa
			let digits_and_present = step(digits_and_present, 0b000_001_111_000_000_001_111_000_000, 2);
			//                                               -> 0ii_000_000_00h_hgg_ffe_edd_ccb_baa
			let digits_and_present = step(digits_and_present, 0b000_000_011_111_111_000_000_000_000, 4);
			//                                               -> 000_000_000_iih_hgg_ffe_edd_ccb_baa
			let digits_and_present = step(digits_and_present, 0b011_000_000_000_000_000_000_000_000, 8);
			let present = digits_and_present >> 33;
			let digits = digits_and_present & 0b11_11_11_11_11_11_11_11_11;
			(present << (2 * 9)) | digits
		}},
	};
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

fn run_index(digits: u32, present: u32, start_shift: u32) -> (usize, u32) {
	let present = present >> start_shift;
	// Extract the digits of the run, plus one more bit for the length marker.
	// This extra bit is the lower bit of the next digit. The next digit is either an absent digit `0b11`,
	// or the current digit is the last (ninth) digit in which case the next bit was set to be `1` above.
	// In either case, the extra bit is `1`, which is exactly what the length marker needs to be.
	let run_mask = present ^ (present + 1);
	let index = (digits >> start_shift) & run_mask;
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
