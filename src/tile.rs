use generic_array::ArrayLength;

use crate::{
	ArrayVec,
	GameType,
	HandMeldType,
	Tile27Set, Tile34MultiSet, Tile34Set,
};

// Tile values are chosen such that:
// - Tile order is the same as the value order.
// - `N5` and `N0` have different values but can be compared equal by masking out the difference. This is used so that pairs and kous containing akadora can be handled
//   just as easily as those not containing akadora, and so that melds / hands that differ only in the position of akadora can be considered equal.
// - `N0` is ordered between `N4` and `N6` just like `N5` is.
// - Operations like `NumberTile::suit`, `NumberTile::shun_rest`, etc can be performed using arithmetic instead of requiring LUTs.
// - The tile representative of shuntsus (`ShunTile`) and kantsus / koutsus / toitsus (`KanKouToiTile`) can be converted
//   into the corresponding base tile with simple masking.
//
// Taken together, this means that `N0` must set one bit that no other tile sets,
// and that this bit must be less significant than the other bits so that `N4`'s value can be less than it and `N6`'s value can be greater than it.
// Thus every tile except `N0` has a value that is a multiple of 4, and `N0` tiles have the same value as the corresponding `N5` tile
// but with the LSB set.
//
// Since `KanKouToiTile` supports representing more than one red five, we specifically reserve two lower bits of `Tile` for the number of red fives,
// which means every non-red `Tile` is a multiple of 4.

const START: u8 = 0x00;

/// A tile.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Tile {
	M1 = START,
	M2 = Self::M1 as u8 + 0x04,
	M3 = Self::M2 as u8 + 0x04,
	M4 = Self::M3 as u8 + 0x04,
	M5 = Self::M4 as u8 + 0x04,
	M0 = Self::M5 as u8 + 0x01,
	M6 = Self::M5 as u8 + 0x04,
	M7 = Self::M6 as u8 + 0x04,
	M8 = Self::M7 as u8 + 0x04,
	M9 = Self::M8 as u8 + 0x04,
	P1 = Self::M9 as u8 + 0x04,
	P2 = Self::P1 as u8 + 0x04,
	P3 = Self::P2 as u8 + 0x04,
	P4 = Self::P3 as u8 + 0x04,
	P5 = Self::P4 as u8 + 0x04,
	P0 = Self::P5 as u8 + 0x01,
	P6 = Self::P5 as u8 + 0x04,
	P7 = Self::P6 as u8 + 0x04,
	P8 = Self::P7 as u8 + 0x04,
	P9 = Self::P8 as u8 + 0x04,
	S1 = Self::P9 as u8 + 0x04,
	S2 = Self::S1 as u8 + 0x04,
	S3 = Self::S2 as u8 + 0x04,
	S4 = Self::S3 as u8 + 0x04,
	S5 = Self::S4 as u8 + 0x04,
	S0 = Self::S5 as u8 + 0x01,
	S6 = Self::S5 as u8 + 0x04,
	S7 = Self::S6 as u8 + 0x04,
	S8 = Self::S7 as u8 + 0x04,
	S9 = Self::S8 as u8 + 0x04,
	Z1 = Self::S9 as u8 + 0x04,
	Z2 = Self::Z1 as u8 + 0x04,
	Z3 = Self::Z2 as u8 + 0x04,
	Z4 = Self::Z3 as u8 + 0x04,
	Z5 = Self::Z4 as u8 + 0x04,
	Z6 = Self::Z5 as u8 + 0x04,
	Z7 = Self::Z6 as u8 + 0x04,
}

/// A number tile.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum NumberTile {
	M1 = Tile::M1 as u8,
	M2 = Tile::M2 as u8,
	M3 = Tile::M3 as u8,
	M4 = Tile::M4 as u8,
	M5 = Tile::M5 as u8,
	M0 = Tile::M0 as u8,
	M6 = Tile::M6 as u8,
	M7 = Tile::M7 as u8,
	M8 = Tile::M8 as u8,
	M9 = Tile::M9 as u8,
	P1 = Tile::P1 as u8,
	P2 = Tile::P2 as u8,
	P3 = Tile::P3 as u8,
	P4 = Tile::P4 as u8,
	P5 = Tile::P5 as u8,
	P0 = Tile::P0 as u8,
	P6 = Tile::P6 as u8,
	P7 = Tile::P7 as u8,
	P8 = Tile::P8 as u8,
	P9 = Tile::P9 as u8,
	S1 = Tile::S1 as u8,
	S2 = Tile::S2 as u8,
	S3 = Tile::S3 as u8,
	S4 = Tile::S4 as u8,
	S5 = Tile::S5 as u8,
	S0 = Tile::S0 as u8,
	S6 = Tile::S6 as u8,
	S7 = Tile::S7 as u8,
	S8 = Tile::S8 as u8,
	S9 = Tile::S9 as u8,
}

/// The tile that makes up a kantsu / koutsu / toitsu, plus the lower two bits encode the number of `N0`s in the group.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum KanKouToiTile {
	M1 = Tile::M1 as u8,
	M2 = Tile::M2 as u8,
	M3 = Tile::M3 as u8,
	M4 = Tile::M4 as u8,
	M5 = Tile::M5 as u8,
	M0 = Tile::M0 as u8,
	M00 = Self::M0 as u8 + 0x01,
	M000 = Self::M00 as u8 + 0x01,
	M6 = Tile::M6 as u8,
	M7 = Tile::M7 as u8,
	M8 = Tile::M8 as u8,
	M9 = Tile::M9 as u8,
	P1 = Tile::P1 as u8,
	P2 = Tile::P2 as u8,
	P3 = Tile::P3 as u8,
	P4 = Tile::P4 as u8,
	P5 = Tile::P5 as u8,
	P0 = Tile::P0 as u8,
	P00 = Self::P0 as u8 + 0x01,
	P000 = Self::P00 as u8 + 0x01,
	P6 = Tile::P6 as u8,
	P7 = Tile::P7 as u8,
	P8 = Tile::P8 as u8,
	P9 = Tile::P9 as u8,
	S1 = Tile::S1 as u8,
	S2 = Tile::S2 as u8,
	S3 = Tile::S3 as u8,
	S4 = Tile::S4 as u8,
	S5 = Tile::S5 as u8,
	S0 = Tile::S0 as u8,
	S00 = Self::S0 as u8 + 0x01,
	S000 = Self::S00 as u8 + 0x01,
	S6 = Tile::S6 as u8,
	S7 = Tile::S7 as u8,
	S8 = Tile::S8 as u8,
	S9 = Tile::S9 as u8,
	Z1 = Tile::Z1 as u8,
	Z2 = Tile::Z2 as u8,
	Z3 = Tile::Z3 as u8,
	Z4 = Tile::Z4 as u8,
	Z5 = Tile::Z5 as u8,
	Z6 = Tile::Z6 as u8,
	Z7 = Tile::Z7 as u8,
}

/// A number tile that is the lowest tile of a shun.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ShunLowTile {
	M1 = Tile::M1 as u8,
	M2 = Tile::M2 as u8,
	M3 = Tile::M3 as u8,
	M4 = Tile::M4 as u8,
	M5 = Tile::M5 as u8,
	M0 = Tile::M0 as u8,
	M6 = Tile::M6 as u8,
	M7 = Tile::M7 as u8,
	P1 = Tile::P1 as u8,
	P2 = Tile::P2 as u8,
	P3 = Tile::P3 as u8,
	P4 = Tile::P4 as u8,
	P5 = Tile::P5 as u8,
	P0 = Tile::P0 as u8,
	P6 = Tile::P6 as u8,
	P7 = Tile::P7 as u8,
	S1 = Tile::S1 as u8,
	S2 = Tile::S2 as u8,
	S3 = Tile::S3 as u8,
	S4 = Tile::S4 as u8,
	S5 = Tile::S5 as u8,
	S0 = Tile::S0 as u8,
	S6 = Tile::S6 as u8,
	S7 = Tile::S7 as u8,
}

/// A number tile that is the lowest tile of a shun, plus a bit that is set if the shun contains a `N0`.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ShunTile {
	M123 = Tile::M1 as u8,
	M234 = Tile::M2 as u8,
	M345 = Tile::M3 as u8,
	M340 = Tile::M3 as u8 + 0x01,
	M456 = Tile::M4 as u8,
	M406 = Tile::M4 as u8 + 0x01,
	M567 = Tile::M5 as u8,
	M067 = Tile::M0 as u8,
	M678 = Tile::M6 as u8,
	M789 = Tile::M7 as u8,
	P123 = Tile::P1 as u8,
	P234 = Tile::P2 as u8,
	P345 = Tile::P3 as u8,
	P340 = Tile::P3 as u8 + 0x01,
	P456 = Tile::P4 as u8,
	P406 = Tile::P4 as u8 + 0x01,
	P567 = Tile::P5 as u8,
	P067 = Tile::P0 as u8,
	P678 = Tile::P6 as u8,
	P789 = Tile::P7 as u8,
	S123 = Tile::S1 as u8,
	S234 = Tile::S2 as u8,
	S345 = Tile::S3 as u8,
	S340 = Tile::S3 as u8 + 0x01,
	S456 = Tile::S4 as u8,
	S406 = Tile::S4 as u8 + 0x01,
	S567 = Tile::S5 as u8,
	S067 = Tile::S0 as u8,
	S678 = Tile::S6 as u8,
	S789 = Tile::S7 as u8,
}

/// A wind tile.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum WindTile {
	Z1 = Tile::Z1 as u8,
	Z2 = Tile::Z2 as u8,
	Z3 = Tile::Z3 as u8,
	Z4 = Tile::Z4 as u8,
}

/// A dragon tile.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum DragonTile {
	Z5 = Tile::Z5 as u8,
	Z6 = Tile::Z6 as u8,
	Z7 = Tile::Z7 as u8,
}

/// A number tile broken down into its suit and number.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct NumberTileClassified {
	pub suit: NumberSuit,
	pub number: Number,
}

/// The suit of a number tile.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum NumberSuit {
	M = 0,
	P = 1,
	S = 2,
}

/// The value of a number tile.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Number {
	N1 = START,
	N2 = Self::N1 as u8 + 0x04,
	N3 = Self::N2 as u8 + 0x04,
	N4 = Self::N3 as u8 + 0x04,
	N5 = Self::N4 as u8 + 0x04,
	N0 = Self::N5 as u8 + 0x01,
	N6 = Self::N5 as u8 + 0x04,
	N7 = Self::N6 as u8 + 0x04,
	N8 = Self::N7 as u8 + 0x04,
	N9 = Self::N8 as u8 + 0x04,
}

/// The value of a [`ShunLowTile`].
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ShunLowNumber {
	N1 = Number::N1 as u8,
	N2 = Number::N2 as u8,
	N3 = Number::N3 as u8,
	N4 = Number::N4 as u8,
	N5 = Number::N5 as u8,
	N0 = Number::N0 as u8,
	N6 = Number::N6 as u8,
	N7 = Number::N7 as u8,
}

/// A trait for comparing tiles based on treating `N5` and `N0` tiles as equal.
pub const trait CmpIgnoreRed {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering;

	fn eq_ignore_red(&self, other: &Self) -> bool {
		matches!(self.cmp_ignore_red(other), core::cmp::Ordering::Equal)
	}

	fn ne_ignore_red(&self, other: &Self) -> bool {
		!self.eq_ignore_red(other)
	}
}

impl Tile {
	/// Returns one of each type of `Tile` in a game of the given type.
	pub const fn each(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::Yonma => &t![
				1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
				E, S, W, N,
				Wh, G, R,
			],

			GameType::Sanma => &t![
				1m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
				E, S, W, N,
				Wh, G, R,
			],
		}
	}

	/// Parses a sequence of `Tile`s and an optional meld type from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
	/// See `extended-mpsz.md` in the root of this repo.
	///
	/// Note that this library does not retain information about which tile was called or which player it was called from.
	/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
	/// but the order of the tiles and the position of the marker within the meld
	/// (which identify the tile that was called and who it was called from) are ignored.
	///
	/// If `end` is set to `Some`, parsing stops when that byte is encountered, and the remaining string is returned.
	/// If `end` is set to `None`, the whole string is parsed, and an empty string is returned.
	///
	/// # Errors
	///
	/// Returns an error if the string does not have valid syntax.
	#[expect(clippy::result_unit_err)]
	pub fn parse_run_until<N>(s: &[u8], end: Option<u8>) -> Result<(ArrayVec<Self, N>, Option<HandMeldType>, &[u8]), ()>
	where
		N: ArrayLength,
	{
		#[derive(Copy, Debug)]
		#[derive_const(Clone)]
		enum Op {
			// An error variant is defined here because the alternative is `OPS: [Option<Op>; 256]` which ends up encoding `None::<Op>` as `0b03`.
			// It's nicer to encode the error case as `0b00` since most of the table will be filled with that.
			InvalidByte,
			AddToCurrentRun(Tile),
			SetCurrentRunSuit(Tile),
			SetMeldType(HandMeldType),
		}

		// Micro-optimization: `let op = match b { ... };` generates a jump table where the op code is inlined into the jump targets, making the function much larger.
		// Making an ops array this way forces the compiler to generate a LUT, which is preferable.
		const OPS: [Op; 256] = {
			let mut result = [Op::InvalidByte; _];

			result[b'1' as usize] = Op::AddToCurrentRun(t!(1m));
			result[b'2' as usize] = Op::AddToCurrentRun(t!(2m));
			result[b'3' as usize] = Op::AddToCurrentRun(t!(3m));
			result[b'4' as usize] = Op::AddToCurrentRun(t!(4m));
			result[b'5' as usize] = Op::AddToCurrentRun(t!(5m));
			result[b'0' as usize] = Op::AddToCurrentRun(t!(0m));
			result[b'6' as usize] = Op::AddToCurrentRun(t!(6m));
			result[b'7' as usize] = Op::AddToCurrentRun(t!(7m));
			result[b'8' as usize] = Op::AddToCurrentRun(t!(8m));
			result[b'9' as usize] = Op::AddToCurrentRun(t!(9m));

			result[b'm' as usize] = Op::SetCurrentRunSuit(t!(1m));
			result[b'p' as usize] = Op::SetCurrentRunSuit(t!(1p));
			result[b's' as usize] = Op::SetCurrentRunSuit(t!(1s));
			result[b'z' as usize] = Op::SetCurrentRunSuit(t!(1z));

			result[b'+' as usize] = Op::SetMeldType(HandMeldType::Ankan);
			result[b'=' as usize] = Op::SetMeldType(HandMeldType::Shouminkan);
			result[b'-' as usize] = Op::SetMeldType(HandMeldType::MinjunMinkouDaiminkan);

			result
		};

		let mut result = ArrayVec::new();
		let mut result_type = None;

		let mut current_run_start = 0_usize;
		let mut current_run_is_valid_z = true;

		let mut bs = s.iter();
		for &b in &mut bs {
			if Some(b) == end {
				break;
			}

			match OPS[usize::from(b)] {
				Op::InvalidByte => return Err(()),

				Op::AddToCurrentRun(t) => {
					result.push(t).map_err(|_| ())?;
					current_run_is_valid_z &= t <= t!(7m) && t != t!(0m);
				},

				Op::SetCurrentRunSuit(suit_base) => {
					unsafe { core::hint::assert_unchecked(current_run_start <= result.len()); }
					let current_run = &mut result[current_run_start..];
					if current_run.is_empty() || (suit_base == t!(1z) && !current_run_is_valid_z) {
						return Err(());
					}
					let diff = suit_base as u8 - t!(1m) as u8;
					if diff > 0 {
						for t in current_run {
							let t_new = *t as u8 + diff;
							// SAFETY: The explicit values given to the `Tile` and `Number` variants make it so that adding `t!(1x) - t!(1m)` is a valid way
							// to convert `t!(nm)` to `t!(nx)`.
							*t = unsafe { core::mem::transmute::<u8, Tile>(t_new) };
						}
					}
					current_run_start = result.len();
					current_run_is_valid_z = true;
				},

				Op::SetMeldType(ty) => if result_type.replace(ty).is_some() {
					return Err(());
				},
			}
		}

		if current_run_start != result.len() {
			return Err(());
		}

		Ok((result, result_type, bs.as_slice()))
	}

	/// Returns the tile that would be a dora tile if this tile was revealed in the dead wall.
	///
	/// For the sake of efficiency, this function does not care if `2m..=8m` are passed in for `GameType::Sanma`, and returns the yonma result in that case.
	///
	/// # Example
	///
	/// ```rust
	/// # #![deny(unused)]
	/// #
	/// # use riichi::{GameType, t};
	/// #
	/// assert_eq!(t!(2m).indicates_dora(GameType::Yonma), t!(3m));
	/// assert_eq!(t!(1m).indicates_dora(GameType::Sanma), t!(9m));
	/// ```
	pub const fn indicates_dora(self, game_type: GameType) -> Self {
		// Micro-optimization: This generates branchless code and avoids the need for a LUT.
		//
		// Tested exhaustively in the `tile_indicates_dora` test.

		const NUMBER_TILE_WRAPS: Tile34Set = t34set![9m, 9p, 9s];

		let sub_number_wrap = if NUMBER_TILE_WRAPS.contains(self) { t!(1p) as u8 - t!(1m) as u8 } else { 0 };
		let sub_wind_wrap = if self == t!(N) { t!(Wh) as u8 - t!(E) as u8 } else { 0 };
		let sub_dragon_wrap = if self == t!(R) { t!(R) as u8 + 4 - t!(Wh) as u8 } else { 0 };
		let add_1m_sanma = if self == t!(1m) && matches!(game_type, GameType::Sanma) { t!(9m) as u8 - t!(2m) as u8 } else { 0 };

		let result = self.remove_red() as u8 + 4 - sub_number_wrap - sub_wind_wrap - sub_dragon_wrap + add_1m_sanma;

		// SAFETY: Lines up with the explicit values given to the `Tile` variants,
		// and tested exhaustively in the `tile_indicates_dora` test.
		unsafe { core::mem::transmute::<u8, Self>(result) }
	}

	pub const fn to_str(self) -> &'static str {
		// Micro-optimization: `match self { ... }` causes each string to be stored as a separate constant
		// that then needs to be looked up from a LUT. The same happens for the length of each string.
		// Making a single string and indexing it manually avoids that first load, and calculating the length using arithmetic avoids the second.
		const STRINGS: &str = "1m??2m??3m??4m??5m0m6m??7m??8m??9m??1p??2p??3p??4p??5p0p6p??7p??8p??9p??1s??2s??3s??4s??5s0s6s??7s??8s??9s??E???S???W???N???Wh??G???R???";

		let start = self as usize - t!(1m) as usize;
		let start = start + (start & 0b1);
		let len = 1 + usize::from(self <= t!(9s) || self == t!(Wh));
		let end = start + len;
		&STRINGS[start..end]
	}

	pub(crate) const fn is_red(self) -> bool {
		(self as u8) & 0b1 == 0b1
	}

	#[must_use]
	pub(crate) const fn remove_red(self) -> Self {
		let result = (self as u8) & !0b1;
		unsafe { core::mem::transmute::<u8, Self>(result) }
	}

	#[must_use]
	pub(crate) const fn make_red(self) -> Option<Self> {
		// Micro-optimization: It is clearer to check for membership in a `Tile37Set`, but that has a complex offset calculation.
		// We can do better with `Tile34Set` plus a simple additional check that `self` isn't already red.
		const FIVES: Tile34Set = t34set![5m, 5p, 5s];

		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if (!(self as u8)) & u8::from(FIVES.contains(self)) == 0b1 {
			let result = (self as u8) | 0b1;
			let result = unsafe { core::mem::transmute::<u8, Self>(result) };
			Some(result)
		}
		else {
			None
		}
	}

	pub(crate) const fn offset(t: Self) -> u8 {
		(t as u8 - t!(1m) as u8) >> 2
	}

	pub(crate) fn offsets<const N: usize>(ts: core::simd::Simd<u8, N>) -> core::simd::Simd<u8, N> {
		(ts - core::simd::Simd::splat(t!(1m) as u8)) >> 2
	}

	pub(crate) fn mask<T>(offset: u8) -> T
	where
		T: From<u8> + core::ops::Shl<u8, Output = T>,
	{
		let one = T::from(0b1_u8);
		one << offset
	}

	pub(crate) fn masks<T, const N: usize>(offsets: core::simd::Simd<u8, N>) -> core::simd::Simd<T, N>
	where
		T: core::simd::SimdCast + core::simd::SimdElement,
		core::simd::Simd<T, N>: core::ops::Shl<Output = core::simd::Simd<T, N>>,
	{
		let ones = core::simd::num::SimdUint::cast::<T>(core::simd::Simd::splat(0b1_u8));
		let offsets = core::simd::num::SimdUint::cast::<T>(offsets);
		ones << offsets
	}

	pub(crate) fn suits_mask(tiles_mask: u64) -> u8 {
		const SUIT_MASKS: core::simd::Simd<u64, 5> = core::simd::Simd::from_array([
			0b0000000_000000000_000000000_111111111,
			0b0000000_000000000_111111111_000000000,
			0b0000000_111111111_000000000_000000000,
			0b0001111_000000000_000000000_000000000,
			0b1110000_000000000_000000000_000000000,
		]);

		let tiles_mask = core::simd::Simd::splat(tiles_mask);
		let suit_mask = tiles_mask & SUIT_MASKS;
		let suit_mask = core::simd::cmp::SimdPartialEq::simd_ne(suit_mask, core::simd::Simd::splat(0));
		#[expect(clippy::cast_possible_truncation)]
		let result = suit_mask.to_bitmask() as u8;
		unsafe { core::hint::assert_unchecked(result <= 0b11111); }
		result
	}
}

const impl CmpIgnoreRed for Tile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 2).cmp(&((*other as u8) >> 2))
	}

	fn eq_ignore_red(&self, other: &Self) -> bool {
		(*self as u8 ^ *other as u8) >> 2 == 0
	}
}

impl core::fmt::Debug for Tile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for Tile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str(self.to_str())
	}
}

const impl From<NumberTile> for Tile {
	fn from(t: NumberTile) -> Self {
		*t.as_ref()
	}
}

const impl From<ShunLowTile> for Tile {
	fn from(t: ShunLowTile) -> Self {
		*t.as_ref()
	}
}

const impl From<WindTile> for Tile {
	fn from(t: WindTile) -> Self {
		*t.as_ref()
	}
}

const impl From<DragonTile> for Tile {
	fn from(t: DragonTile) -> Self {
		*t.as_ref()
	}
}

impl core::str::FromStr for Tile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		// Micro-optimization: A simple `match s { "1m" => t!(1m), ... }` generates a jump table for each of the `s.len() == 1` and `s.len() == 2` cases.
		// Doing it this way generates branches for the suit and one small jump table for the yakuhai cases at the end.

		Ok(match s.as_bytes() {
			b"Wh" => t!(Wh),

			&[number, suit] => {
				let number = match number {
					b'0' => Number::N0,
					b'1'..=b'9' => unsafe { core::mem::transmute::<u8, Number>(((number - b'1') << 2) + Number::N1 as u8) },
					_ => return Err(()),
				};
				let suit = match suit {
					b'm' => NumberSuit::M,
					b'p' => NumberSuit::P,
					b's' => NumberSuit::S,
					b'z' => {
						let tile = t!(E) as u8 + (number as u8 - Number::N1 as u8);
						return (tile <= t!(R) as u8 && tile & 0b1 == 0).then(|| unsafe { core::mem::transmute::<u8, Self>(tile) }).ok_or(());
					},
					_ => return Err(()),
				};
				NumberTile::from(NumberTileClassified { suit, number }).into()
			},

			b"E" => t!(E),
			b"S" => t!(S),
			b"W" => t!(W),
			b"N" => t!(N),

			b"G" => t!(G),
			b"R" => t!(R),

			_ => return Err(()),
		})
	}
}

impl NumberTile {
	/// Returns one of each type of `NumberTile` in a game of the given type.
	pub const fn each(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::Yonma => &tn![
				1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
			],

			GameType::Sanma => &tn![
				1m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
			],
		}
	}

	pub const fn number(self) -> Number {
		let n = (self as u8 - t!(1m) as u8) % (t!(1p) as u8 - t!(1m) as u8) + Number::N1 as u8;
		// SAFETY: Lines up with the explicit values given to the `NumberTile` and `Number` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute::<u8, Number>(n) }
	}

	pub const fn suit(self) -> NumberSuit {
		let suit = (self as u8 - t!(1m) as u8) / (t!(1p) as u8 - t!(1m) as u8);
		// SAFETY: Lines up with the explicit values given to the `NumberTile` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute::<u8, NumberSuit>(suit) }
	}
}

const impl AsRef<Tile> for NumberTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `NumberTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

const impl CmpIgnoreRed for NumberTile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 2).cmp(&((*other as u8) >> 2))
	}

	fn eq_ignore_red(&self, other: &Self) -> bool {
		(*self as u8 ^ *other as u8) >> 2 == 0
	}
}

impl core::fmt::Debug for NumberTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for NumberTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		AsRef::<Tile>::as_ref(self).fmt(f)
	}
}

const impl From<NumberTileClassified> for NumberTile {
	fn from(t: NumberTileClassified) -> Self {
		let NumberTileClassified { suit, number } = t;
		// Micro-optimization: Using a `match` for every combination is safer but generates branches based on `suit`
		// that add constant 0x24 or 0x48 instead of the multiplication by 0x24 (via `lea` / `sh*add`), so we do it manually.
		let t = (suit as u8) * (tn!(1p) as u8 - tn!(1m) as u8) + (number as u8 - Number::N1 as u8) + tn!(1m) as u8;
		// SAFETY: Lines up with the explicit values given to the `Number` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute::<u8, Self>(t) }
	}
}

const impl From<ShunLowTile> for NumberTile {
	fn from(t: ShunLowTile) -> Self {
		*AsRef::as_ref(&t)
	}
}

impl core::str::FromStr for NumberTile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let t: Tile = s.parse()?;
		t.try_into()
	}
}

const impl TryFrom<Tile> for NumberTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		if (t!(1m)..=t!(9s)).contains(&t) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `NumberTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from` test.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl KanKouToiTile {
	/// Construct a `KanKouToiTile` using the given base tile and the number of red fives in this group.
	///
	/// Returns `Some` if the `num_red_fives` value makes sense with the `tile` value, ie it is >0 only if `tile` is a `N5`, `None` otherwise.
	pub const fn new(tile: Tile, num_red_fives: u8) -> Option<Self> {
		let tile = tile.remove_red();
		if num_red_fives <= 3 && (num_red_fives == 0 || tile.make_red().is_some()) {
			let result = (tile as u8) | num_red_fives;
			let result = unsafe { core::mem::transmute::<u8, Self>(result) };
			Some(result)
		}
		else {
			None
		}
	}

	/// Construct a kantsu representative using the given four tiles.
	///
	/// Returns `Some` if the tiles form a valid kantsu, `None` otherwise.
	pub const fn kan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if is_kan(t1, t2, t3, t4) {
			let num_red_fives =
				(t1 as u8 & 0b1) +
				(t2 as u8 & 0b1) +
				(t3 as u8 & 0b1) +
				(t4 as u8 & 0b1);
			Self::new(t1, num_red_fives)
		}
		else {
			None
		}
	}

	/// Construct a koutsu representative using the given four tiles.
	///
	/// Returns `Some` if the tiles form a valid koutsu, `None` otherwise.
	pub const fn kou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if is_kou(t1, t2, t3) {
			let num_red_fives =
				(t1 as u8 & 0b1) +
				(t2 as u8 & 0b1) +
				(t3 as u8 & 0b1);
			Self::new(t1, num_red_fives)
		}
		else {
			None
		}
	}

	/// Construct a toitsu representative using the given four tiles.
	///
	/// Returns `Some` if the tiles form a valid toitsu, `None` otherwise.
	pub const fn toi(t1: Tile, t2: Tile) -> Option<Self> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if t1.eq_ignore_red(&t2) {
			let num_red_fives =
				(t1 as u8 & 0b1) +
				(t2 as u8 & 0b1);
			Self::new(t1, num_red_fives)
		}
		else {
			None
		}
	}

	/// Returns the base (non-red) tile corresponding to this group representative.
	pub const fn tile(self) -> Tile {
		let result = (self as u8) & !0b11;
		unsafe { core::mem::transmute::<u8, Tile>(result) }
	}

	/// Returns the number of red fives in this group.
	pub const fn num_red_fives(self) -> u8 {
		self as u8 & 0b11
	}

	/// Returns the tiles comprising this group.
	///
	/// The representative only stores the number of red fives, not the number of tiles in the group, so the caller provides that latter number here via `N`.
	/// So `.num_red_fives()` of those tiles will be red fives and the rest will be regular fives. Regular fives are placed before red fives in the array.
	///
	/// For example, if the representative has `.tile() == t!(5m) && .num_red_fives() == 1`, and the caller calls `.tiles::<4>()`,
	/// the returned array will be `t![5m, 5m, 5m, 0m]`.
	///
	/// If `N < .num_red_fives()`, there is clearly a mismatch, but this function has the defined behavior of returning all red tiles in this case.
	pub fn tiles<const N: usize>(self) -> [Tile; N] {
		let tile = self.tile();
		let mut result = [tile; N];
		let num_red_fives = usize::from(self.num_red_fives());
		if num_red_fives > 0 {
			let tile_red = tile.make_red();
			let tile_red = unsafe { tile_red.unwrap_unchecked() };
			let result = &mut result[N.saturating_sub(num_red_fives)..];
			// Micro-optimization: rustc generates a call to `memset` but we can do better with scalable vectors on RVV.
			cfg_select! {
				all(target_arch = "riscv64", target_feature = "v") => unsafe {
					let result = core::slice::from_raw_parts_mut(<*mut Tile>::cast::<u8>(result.as_mut_ptr()), result.len());
					core::arch::asm!(
						"vsetvli zero, {result_len}, e8, m1, ta, ma",
						"vmv.v.x v8, {tile_red}",
						"vse8.v v8, ({result_ptr})",

						result_len = in(reg) result.len(),
						tile_red = in(reg) tile_red as u8,
						result_ptr = in(reg) result.as_mut_ptr(),
						out("v8") _,
						options(nostack),
					);
				},

				_ => result.fill(tile_red),
			};
		}
		result
	}

	/// Adds a red five to this representative.
	///
	/// # Safety
	///
	/// Requires that `self` is a `N5` or `N0` tile and that the current number of red fives is less than 3.
	pub(crate) const unsafe fn add_red(&mut self) {
		let this = unsafe { &mut *<*mut Self>::cast::<u8>(self) };
		debug_assert!(*this & 0b11 <= 0b10);
		*this += 1;
	}

	#[cfg(test)]
	pub(crate) const fn remove_all_red(&mut self) {
		let this = unsafe { &mut *<*mut Self>::cast::<u8>(self) };
		*this &= !0b11;
	}

	pub(crate) const fn dora_match(self, n: u8, doras: &Tile34MultiSet) -> u8 {
		doras.get(self.tile()) * n + self.num_red_fives()
	}

	pub(crate) fn fmt(self, n: usize, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let t = self.tile();
		let num_red_fives = usize::from(self.num_red_fives());
		let num_regular = n.saturating_sub(num_red_fives);

		if num_regular > 0 {
			let s = t.to_str();
			for _ in 0..num_regular {
				f.write_str(s)?;
				f.write_str(" ")?;
			}
		}
		if num_red_fives > 0 {
			let t = t.make_red();
			let t = unsafe { t.unwrap_unchecked() };
			let s = t.to_str();
			for _ in 0..num_red_fives {
				f.write_str(s)?;
				f.write_str(" ")?;
			}
		}

		Ok(())
	}
}

const impl CmpIgnoreRed for KanKouToiTile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 2).cmp(&((*other as u8) >> 2))
	}

	fn eq_ignore_red(&self, other: &Self) -> bool {
		(*self as u8 ^ *other as u8) >> 2 == 0
	}
}

impl ShunLowTile {
	pub const fn number(self) -> ShunLowNumber {
		let number = NumberTile::from(self).number();
		let number = number as u8;
		unsafe { core::mem::transmute::<u8, ShunLowNumber>(number) }
	}

	pub(crate) const fn shun_rest(self) -> (NumberTile, NumberTile) {
		let this = self as u8 & !0b1;
		let next = this + 4;
		let next = unsafe { core::mem::transmute::<u8, NumberTile>(next) };
		let next_next = this + 8;
		let next_next = unsafe { core::mem::transmute::<u8, NumberTile>(next_next) };
		(next, next_next)
	}
}

const impl AsRef<Tile> for ShunLowTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `ShunLowTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

const impl AsRef<NumberTile> for ShunLowTile {
	fn as_ref(&self) -> &NumberTile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `ShunLowTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

const impl CmpIgnoreRed for ShunLowTile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 2).cmp(&((*other as u8) >> 2))
	}

	fn eq_ignore_red(&self, other: &Self) -> bool {
		(*self as u8 ^ *other as u8) >> 2 == 0
	}
}

impl core::fmt::Debug for ShunLowTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ShunLowTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		AsRef::<Tile>::as_ref(self).fmt(f)
	}
}

const impl TryFrom<NumberTile> for ShunLowTile {
	type Error = ();

	fn try_from(t: NumberTile) -> Result<Self, Self::Error> {
		Tile::from(t).try_into()
	}
}

const impl TryFrom<Tile> for ShunLowTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		// Tested exhaustively in the `shun_rest` test.

		const VALID: Tile34Set = t34set![
			1m, 2m, 3m, 4m, 5m, 6m, 7m,
			1p, 2p, 3p, 4p, 5p, 6p, 7p,
			1s, 2s, 3s, 4s, 5s, 6s, 7s,
		];

		if VALID.contains(t) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `NumberTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from` test.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl ShunTile {
	/// Construct a `ShunTile` using the given three tiles.
	///
	/// Returns `Some` if the three tiles form a valid shun, `None` otherwise.
	pub const fn new(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if is_shun(t1, t2, t3) {
			let has_five_red = (t1 as u8 & 0b1) | (t2 as u8 & 0b1) | (t3 as u8 & 0b1);
			let result = t1 as u8 | has_five_red;
			Some(unsafe { core::mem::transmute::<u8, Self>(result) })
		}
		else {
			None
		}
	}

	pub(crate) const fn is_red(self) -> bool {
		(self as u8) & 0b1 == 0b1
	}

	#[must_use]
	pub(crate) const fn remove_red(self) -> ShunLowTile {
		let result = (self as u8) & !0b1;
		unsafe { core::mem::transmute::<u8, ShunLowTile>(result) }
	}

	pub(crate) const fn shun(self) -> (ShunLowTile, NumberTile, NumberTile) {
		// SAFETY: Lines up with the explicit values given to the `ShunLowTile` and `NumberTile` variants,
		// and tested exhaustively in the `shun` test.

		let is_red = self as u8 & 0b1 != 0;

		let this = self.remove_red();
		let (next, next_next) = this.shun_rest();

		let this = this as u8 | u8::from(is_red && Tile27Set::FIVES.contains(this.into()));
		let this = unsafe { core::mem::transmute::<u8, ShunLowTile>(this) };

		let next = next as u8 | u8::from(is_red && Tile27Set::FIVES.contains(next));
		let next = unsafe { core::mem::transmute::<u8, NumberTile>(next) };

		let next_next = next_next as u8 | u8::from(is_red && Tile27Set::FIVES.contains(next_next));
		let next_next = unsafe { core::mem::transmute::<u8, NumberTile>(next_next) };

		(this, next, next_next)
	}

	pub(crate) fn dora_match(self, doras: &Tile34MultiSet) -> u8 {
		let (t1, t2, t3) = self.shun();
		[t1.into(), t2.into(), t3.into()].into_iter()
			.map(|t| doras.get(t) + u8::from(t.is_red()))
			.sum::<u8>()
	}
}

impl core::fmt::Display for ShunTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		// Micro-optimization: `f.write_str(match self { ... })` causes each string to be stored as a separate constant
		// that then needs to be looked up from a LUT. The same happens for the length of each string.
		// Making a single string and indexing it manually avoids that first load, and calculating the length using arithmetic avoids the second.
		const STRINGS: &str = "\
			1m 2m 3m 4m 5m 6m 7m 8m 9m \
			1p 2p 3p 4p 5p 6p 7p 8p 9p \
			1s 2s 3s 4s 5s 6s 7s 8s 9s \
			1m 2m 3m 4m 0m 6m 7m 8m 9m \
			1p 2p 3p 4p 0p 6p 7p 8p 9p \
			1s 2s 3s 4s 0s 6s 7s 8s 9s \
		";

		let offset = *self as usize - Self::M123 as usize;
		let start = (offset >> 2) * 3 + (offset & 0b1) * 81;
		let end = start + 9;
		f.write_str(&STRINGS[start..end])
	}
}

const impl From<ShunLowTile> for ShunTile {
	fn from(t: ShunLowTile) -> Self {
		unsafe { core::mem::transmute::<ShunLowTile, Self>(t) }
	}
}

impl WindTile {
	/// # Safety
	///
	/// This takes `u8` so that `ShunTile` values can be passed in as-is instead of needing to `.remove_red()` them into a valid `Tile` first.
	///
	/// However if `t` is in the range of `(t!(E) as u8)..=(t!(N) as u8)` then `t` must have a value corresponding to a `WindTile`.
	pub(crate) const unsafe fn try_from_raw(t: u8) -> Result<Self, ()> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if ((t!(E) as u8)..=(t!(N) as u8)).contains(&t) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `WindTile` variants,
			// and tested exhaustively in the `wind_tile_as_ref_and_from` test.
			let t = unsafe { core::mem::transmute::<u8, Self>(t) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

const impl AsRef<Tile> for WindTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `WindTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `wind_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

impl core::fmt::Debug for WindTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for WindTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		AsRef::<Tile>::as_ref(self).fmt(f)
	}
}

impl core::str::FromStr for WindTile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let t: Tile = s.parse()?;
		t.try_into()
	}
}

const impl TryFrom<Tile> for WindTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		// SAFETY: Since `t` is a `Tile` it is guaranteed to meet the safety requirement of `try_from_raw`.
		unsafe { Self::try_from_raw(t as u8) }
	}
}

impl DragonTile {
	/// # Safety
	///
	/// This takes `u8` so that `ShunTile` values can be passed in as-is instead of needing to `.remove_red()` them into a valid `Tile` first.
	///
	/// However if `t` is in the range of `(t!(Wh) as u8)..=(t!(R) as u8)` then `t` must have a value corresponding to a `DragonTile`.
	pub(crate) const unsafe fn try_from_raw(t: u8) -> Result<Self, ()> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if ((t!(Wh) as u8)..=(t!(R) as u8)).contains(&t) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `DragonTile` variants,
			// and tested exhaustively in the `dragon_tile_as_ref_and_from` test.
			let t = unsafe { core::mem::transmute::<u8, Self>(t) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

const impl AsRef<Tile> for DragonTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `DragonTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `dragon_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

impl core::fmt::Debug for DragonTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for DragonTile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		AsRef::<Tile>::as_ref(self).fmt(f)
	}
}

impl core::str::FromStr for DragonTile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let t: Tile = s.parse()?;
		t.try_into()
	}
}

const impl TryFrom<Tile> for DragonTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		// SAFETY: Since `t` is a `Tile` it is guaranteed to meet the safety requirement of `try_from_raw`.
		unsafe { Self::try_from_raw(t as u8) }
	}
}

impl core::fmt::Display for NumberTileClassified {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "{}{}", self.number, self.suit)
	}
}

const impl From<NumberTile> for NumberTileClassified {
	fn from(t: NumberTile) -> Self {
		Self { suit: t.suit(), number: t.number() }
	}
}

impl core::fmt::Debug for NumberSuit {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for NumberSuit {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		// Micro-optimization: `f.write_str(match self { ... })` causes each string to be stored as a separate constant
		// that then needs to be looked up from a LUT. Making a single string and indexing it manually avoids that load.
		let offset = usize::from(*self as u8);
		f.write_str(&"mps"[offset..=offset])
	}
}

impl Number {
	pub const fn value(self) -> u8 {
		((self as u8 - Self::N1 as u8) >> 2) + 1
	}
}

const impl CmpIgnoreRed for Number {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 2).cmp(&((*other as u8) >> 2))
	}

	fn eq_ignore_red(&self, other: &Self) -> bool {
		(*self as u8 ^ *other as u8) >> 2 == 0
	}
}

impl core::fmt::Debug for Number {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for Number {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		// Micro-optimization: `f.write_str(match self { ... })` causes each string to be stored as a separate constant
		// that then needs to be looked up from a LUT. Making a single string and indexing it manually avoids that load.
		let offset = usize::from(*self as u8 - Self::N1 as u8);
		f.write_str(&"1???2???3???4???50??6???7???8???9???"[offset..=offset])
	}
}

const impl From<ShunLowNumber> for Number {
	fn from(n: ShunLowNumber) -> Self {
		unsafe { core::mem::transmute::<u8, Self>(n as u8) }
	}
}

const fn eq_ignore_red<const N: usize>(a: &[u8; N], b: &[u8; N]) -> bool {
	// TODO(rustup): This uses an indexed `while` loop instead of `a.iter().zip(b).fold(...)` so that it can be `const fn`.
	let mut eq = 0;
	let mut i = 0;
	while i < a.len() {
		eq |= a[i] ^ b[i];
		i += 1;
	}
	eq >> 2 == 0
}

const fn is_kan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> bool {
	eq_ignore_red(&[t1 as u8, t2 as u8, t3 as u8], &[t2 as u8, t3 as u8, t4 as u8])
}

const fn is_kou(t1: Tile, t2: Tile, t3: Tile) -> bool {
	eq_ignore_red(&[t1 as u8, t2 as u8], &[t2 as u8, t3 as u8])
}

const fn is_shun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> bool {
	let (t2_expected, t3_expected) = t1.shun_rest();
	eq_ignore_red(&[t2_expected as u8, t3_expected as u8], &[t2 as u8, t3 as u8])
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use crate::Tile37MultiSet;
	use super::*;

	#[test]
	fn tile_indicates_dora() {
		for (input, expected_yonma, expected_sanma) in [
			(t!(1m), t!(2m), Some(t!(9m))),
			(t!(2m), t!(3m), None),
			(t!(3m), t!(4m), None),
			(t!(4m), t!(5m), None),
			(t!(5m), t!(6m), None),
			(t!(0m), t!(6m), None),
			(t!(6m), t!(7m), None),
			(t!(7m), t!(8m), None),
			(t!(8m), t!(9m), None),
			(t!(9m), t!(1m), Some(t!(1m))),
			(t!(1p), t!(2p), Some(t!(2p))),
			(t!(2p), t!(3p), Some(t!(3p))),
			(t!(3p), t!(4p), Some(t!(4p))),
			(t!(4p), t!(5p), Some(t!(5p))),
			(t!(5p), t!(6p), Some(t!(6p))),
			(t!(0p), t!(6p), Some(t!(6p))),
			(t!(6p), t!(7p), Some(t!(7p))),
			(t!(7p), t!(8p), Some(t!(8p))),
			(t!(8p), t!(9p), Some(t!(9p))),
			(t!(9p), t!(1p), Some(t!(1p))),
			(t!(1s), t!(2s), Some(t!(2s))),
			(t!(2s), t!(3s), Some(t!(3s))),
			(t!(3s), t!(4s), Some(t!(4s))),
			(t!(4s), t!(5s), Some(t!(5s))),
			(t!(5s), t!(6s), Some(t!(6s))),
			(t!(0s), t!(6s), Some(t!(6s))),
			(t!(6s), t!(7s), Some(t!(7s))),
			(t!(7s), t!(8s), Some(t!(8s))),
			(t!(8s), t!(9s), Some(t!(9s))),
			(t!(9s), t!(1s), Some(t!(1s))),
			(t!(E), t!(S), Some(t!(S))),
			(t!(S), t!(W), Some(t!(W))),
			(t!(W), t!(N), Some(t!(N))),
			(t!(N), t!(E), Some(t!(E))),
			(t!(Wh), t!(G), Some(t!(G))),
			(t!(G), t!(R), Some(t!(R))),
			(t!(R), t!(Wh), Some(t!(Wh))),
		] {
			let actual = input.indicates_dora(GameType::Yonma);
			assert_eq!(actual, expected_yonma);

			let actual = input.indicates_dora(GameType::Sanma);
			assert_eq!(actual, expected_sanma.unwrap_or(expected_yonma));
		}
	}

	const TILE_EACH_YONMA_WITH_RED_FIVE: [Tile; 37] = t![
		1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m,
		1p, 2p, 3p, 4p, 5p, 0p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 0s, 6s, 7s, 8s, 9s,
		E, S, W, N,
		Wh, G, R,
	];

	#[test]
	fn tile_red() {
		for t in TILE_EACH_YONMA_WITH_RED_FIVE {
			assert_eq!(t.is_red(), matches!(t, t!(0m | 0p | 0s)));

			assert_eq!(t.remove_red(), match t {
				t!(0m) => t!(5m),
				t!(0p) => t!(5p),
				t!(0s) => t!(5s),
				t => t,
			});

			assert_eq!(t.make_red(), match t {
				t!(5m) => Some(t!(0m)),
				t!(5p) => Some(t!(0p)),
				t!(5s) => Some(t!(0s)),
				_ => None,
			});
		}
	}

	#[test]
	fn tile_ord() {
		for a in TILE_EACH_YONMA_WITH_RED_FIVE {
			for b in TILE_EACH_YONMA_WITH_RED_FIVE {
				let expected = (a as u8).cmp(&(b as u8));
				let expected_ignore_red = match (a, b) {
					(t!(5m | 0m), t!(5m | 0m)) |
					(t!(5p | 0p), t!(5p | 0p)) |
					(t!(5s | 0s), t!(5s | 0s)) => core::cmp::Ordering::Equal,
					_ => expected,
				};
				let actual = a.cmp(&b);
				assert_eq!(actual, expected);
				let actual = a.partial_cmp(&b).unwrap();
				assert_eq!(actual, expected);
				let actual = a.cmp_ignore_red(&b);
				assert_eq!(actual, expected_ignore_red);
			}
		}
	}

	#[test]
	fn number_tile_as_ref_and_from_and_try_from() {
		for (input, expected) in [
			(tn!(1m), t!(1m)),
			(tn!(2m), t!(2m)),
			(tn!(3m), t!(3m)),
			(tn!(4m), t!(4m)),
			(tn!(5m), t!(5m)),
			(tn!(0m), t!(0m)),
			(tn!(6m), t!(6m)),
			(tn!(7m), t!(7m)),
			(tn!(8m), t!(8m)),
			(tn!(9m), t!(9m)),
			(tn!(1p), t!(1p)),
			(tn!(2p), t!(2p)),
			(tn!(3p), t!(3p)),
			(tn!(4p), t!(4p)),
			(tn!(5p), t!(5p)),
			(tn!(0p), t!(0p)),
			(tn!(6p), t!(6p)),
			(tn!(7p), t!(7p)),
			(tn!(8p), t!(8p)),
			(tn!(9p), t!(9p)),
			(tn!(1s), t!(1s)),
			(tn!(2s), t!(2s)),
			(tn!(3s), t!(3s)),
			(tn!(4s), t!(4s)),
			(tn!(5s), t!(5s)),
			(tn!(0s), t!(0s)),
			(tn!(6s), t!(6s)),
			(tn!(7s), t!(7s)),
			(tn!(8s), t!(8s)),
			(tn!(9s), t!(9s)),
		] {
			let actual: &Tile = input.as_ref();
			assert_eq!(*actual, expected);
			let actual = Tile::from(input);
			assert_eq!(actual, expected);
			let actual = NumberTile::try_from(expected).unwrap();
			assert_eq!(actual, input);
			() = WindTile::try_from(expected).unwrap_err();
			() = DragonTile::try_from(expected).unwrap_err();
		}
	}

	#[test]
	fn number_tile_convert_classified() {
		for (ntc, nt) in [
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N1 }, tn!(1m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N2 }, tn!(2m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N3 }, tn!(3m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N4 }, tn!(4m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N5 }, tn!(5m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N0 }, tn!(0m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N6 }, tn!(6m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N7 }, tn!(7m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N8 }, tn!(8m)),
			(NumberTileClassified { suit: NumberSuit::M, number: Number::N9 }, tn!(9m)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N1 }, tn!(1p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N2 }, tn!(2p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N3 }, tn!(3p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N4 }, tn!(4p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N5 }, tn!(5p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N0 }, tn!(0p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N6 }, tn!(6p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N7 }, tn!(7p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N8 }, tn!(8p)),
			(NumberTileClassified { suit: NumberSuit::P, number: Number::N9 }, tn!(9p)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N1 }, tn!(1s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N2 }, tn!(2s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N3 }, tn!(3s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N4 }, tn!(4s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N5 }, tn!(5s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N0 }, tn!(0s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N6 }, tn!(6s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N7 }, tn!(7s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N8 }, tn!(8s)),
			(NumberTileClassified { suit: NumberSuit::S, number: Number::N9 }, tn!(9s)),
		] {
			let nt_actual = NumberTile::from(ntc);
			assert_eq!(nt_actual, nt);

			let ntc_actual = NumberTileClassified::from(nt);
			assert_eq!(ntc_actual, ntc);
		}
	}

	#[test]
	fn number_value() {
		assert_eq!(Number::N1.value(), 1);
		assert_eq!(Number::N2.value(), 2);
		assert_eq!(Number::N3.value(), 3);
		assert_eq!(Number::N4.value(), 4);
		assert_eq!(Number::N5.value(), 5);
		assert_eq!(Number::N0.value(), 5);
		assert_eq!(Number::N6.value(), 6);
		assert_eq!(Number::N7.value(), 7);
		assert_eq!(Number::N8.value(), 8);
		assert_eq!(Number::N9.value(), 9);
	}

	#[test]
	fn number_ord() {
		const NUMBERS: [Number; 10] = [
			Number::N1,
			Number::N2,
			Number::N3,
			Number::N4,
			Number::N5,
			Number::N0,
			Number::N6,
			Number::N7,
			Number::N8,
			Number::N9,
		];
		for a in NUMBERS {
			for b in NUMBERS {
				let expected = (a as u8).cmp(&(b as u8));
				let expected_ignore_red = match (a, b) {
					(Number::N5 | Number::N0, Number::N5 | Number::N0) => core::cmp::Ordering::Equal,
					_ => expected,
				};
				let actual = a.cmp(&b);
				assert_eq!(actual, expected);
				let actual = a.partial_cmp(&b).unwrap();
				assert_eq!(actual, expected);
				let actual = a.cmp_ignore_red(&b);
				assert_eq!(actual, expected_ignore_red);
			}
		}
	}

	#[test]
	fn kan_kou_tile_kan_representative() {
		for t1 in TILE_EACH_YONMA_WITH_RED_FIVE {
			let mut used = Tile37MultiSet::default();
			assert!(used.insert(t1));

			for t2 in TILE_EACH_YONMA_WITH_RED_FIVE {
				let mut used = used.clone();
				if !used.insert(t2) { continue; }

				for t3 in TILE_EACH_YONMA_WITH_RED_FIVE {
					let mut used = used.clone();
					if !used.insert(t3) { continue; }

					for t4 in TILE_EACH_YONMA_WITH_RED_FIVE {
						let mut used = used.clone();
						if !used.insert(t4) { continue; }

						let expected = match [t1, t2, t3, t4] {
							t![1m, 1m, 1m, 1m] => Some(KanKouToiTile::new(t!(1m), 0).unwrap()),
							t![2m, 2m, 2m, 2m] => Some(KanKouToiTile::new(t!(2m), 0).unwrap()),
							t![3m, 3m, 3m, 3m] => Some(KanKouToiTile::new(t!(3m), 0).unwrap()),
							t![4m, 4m, 4m, 4m] => Some(KanKouToiTile::new(t!(4m), 0).unwrap()),
							t![5m, 5m, 5m, 5m] => Some(KanKouToiTile::new(t!(5m), 0).unwrap()),
							t![5m, 5m, 5m, 0m] |
							t![5m, 5m, 0m, 5m] |
							t![5m, 0m, 5m, 5m] |
							t![0m, 5m, 5m, 5m] => Some(KanKouToiTile::new(t!(5m), 1).unwrap()),
							t![5m, 5m, 0m, 0m] |
							t![5m, 0m, 5m, 0m] |
							t![5m, 0m, 0m, 5m] |
							t![0m, 5m, 5m, 0m] |
							t![0m, 5m, 0m, 5m] |
							t![0m, 0m, 5m, 5m] => Some(KanKouToiTile::new(t!(5m), 2).unwrap()),
							t![5m, 0m, 0m, 0m] |
							t![0m, 5m, 0m, 0m] |
							t![0m, 0m, 5m, 0m] |
							t![0m, 0m, 0m, 5m] => Some(KanKouToiTile::new(t!(5m), 3).unwrap()),
							t![6m, 6m, 6m, 6m] => Some(KanKouToiTile::new(t!(6m), 0).unwrap()),
							t![7m, 7m, 7m, 7m] => Some(KanKouToiTile::new(t!(7m), 0).unwrap()),
							t![8m, 8m, 8m, 8m] => Some(KanKouToiTile::new(t!(8m), 0).unwrap()),
							t![9m, 9m, 9m, 9m] => Some(KanKouToiTile::new(t!(9m), 0).unwrap()),

							t![1p, 1p, 1p, 1p] => Some(KanKouToiTile::new(t!(1p), 0).unwrap()),
							t![2p, 2p, 2p, 2p] => Some(KanKouToiTile::new(t!(2p), 0).unwrap()),
							t![3p, 3p, 3p, 3p] => Some(KanKouToiTile::new(t!(3p), 0).unwrap()),
							t![4p, 4p, 4p, 4p] => Some(KanKouToiTile::new(t!(4p), 0).unwrap()),
							t![5p, 5p, 5p, 5p] => Some(KanKouToiTile::new(t!(5p), 0).unwrap()),
							t![5p, 5p, 5p, 0p] |
							t![5p, 5p, 0p, 5p] |
							t![5p, 0p, 5p, 5p] |
							t![0p, 5p, 5p, 5p] => Some(KanKouToiTile::new(t!(5p), 1).unwrap()),
							t![5p, 5p, 0p, 0p] |
							t![5p, 0p, 5p, 0p] |
							t![5p, 0p, 0p, 5p] |
							t![0p, 5p, 5p, 0p] |
							t![0p, 5p, 0p, 5p] |
							t![0p, 0p, 5p, 5p] => Some(KanKouToiTile::new(t!(5p), 2).unwrap()),
							t![5p, 0p, 0p, 0p] |
							t![0p, 5p, 0p, 0p] |
							t![0p, 0p, 5p, 0p] |
							t![0p, 0p, 0p, 5p] => Some(KanKouToiTile::new(t!(5p), 3).unwrap()),
							t![6p, 6p, 6p, 6p] => Some(KanKouToiTile::new(t!(6p), 0).unwrap()),
							t![7p, 7p, 7p, 7p] => Some(KanKouToiTile::new(t!(7p), 0).unwrap()),
							t![8p, 8p, 8p, 8p] => Some(KanKouToiTile::new(t!(8p), 0).unwrap()),
							t![9p, 9p, 9p, 9p] => Some(KanKouToiTile::new(t!(9p), 0).unwrap()),

							t![1s, 1s, 1s, 1s] => Some(KanKouToiTile::new(t!(1s), 0).unwrap()),
							t![2s, 2s, 2s, 2s] => Some(KanKouToiTile::new(t!(2s), 0).unwrap()),
							t![3s, 3s, 3s, 3s] => Some(KanKouToiTile::new(t!(3s), 0).unwrap()),
							t![4s, 4s, 4s, 4s] => Some(KanKouToiTile::new(t!(4s), 0).unwrap()),
							t![5s, 5s, 5s, 5s] => Some(KanKouToiTile::new(t!(5s), 0).unwrap()),
							t![5s, 5s, 5s, 0s] |
							t![5s, 5s, 0s, 5s] |
							t![5s, 0s, 5s, 5s] |
							t![0s, 5s, 5s, 5s] => Some(KanKouToiTile::new(t!(5s), 1).unwrap()),
							t![5s, 5s, 0s, 0s] |
							t![5s, 0s, 5s, 0s] |
							t![5s, 0s, 0s, 5s] |
							t![0s, 5s, 5s, 0s] |
							t![0s, 5s, 0s, 5s] |
							t![0s, 0s, 5s, 5s] => Some(KanKouToiTile::new(t!(5s), 2).unwrap()),
							t![5s, 0s, 0s, 0s] |
							t![0s, 5s, 0s, 0s] |
							t![0s, 0s, 5s, 0s] |
							t![0s, 0s, 0s, 5s] => Some(KanKouToiTile::new(t!(5s), 3).unwrap()),
							t![6s, 6s, 6s, 6s] => Some(KanKouToiTile::new(t!(6s), 0).unwrap()),
							t![7s, 7s, 7s, 7s] => Some(KanKouToiTile::new(t!(7s), 0).unwrap()),
							t![8s, 8s, 8s, 8s] => Some(KanKouToiTile::new(t!(8s), 0).unwrap()),
							t![9s, 9s, 9s, 9s] => Some(KanKouToiTile::new(t!(9s), 0).unwrap()),

							t![E, E, E, E] => Some(KanKouToiTile::new(t!(E), 0).unwrap()),
							t![S, S, S, S] => Some(KanKouToiTile::new(t!(S), 0).unwrap()),
							t![W, W, W, W] => Some(KanKouToiTile::new(t!(W), 0).unwrap()),
							t![N, N, N, N] => Some(KanKouToiTile::new(t!(N), 0).unwrap()),
							t![Wh, Wh, Wh, Wh] => Some(KanKouToiTile::new(t!(Wh), 0).unwrap()),
							t![G, G, G, G] => Some(KanKouToiTile::new(t!(G), 0).unwrap()),
							t![R, R, R, R] => Some(KanKouToiTile::new(t!(R), 0).unwrap()),

							_ => None,
						};
						let actual = KanKouToiTile::kan(t1, t2, t3, t4);
						assert_eq!(actual, expected);
					}
				}
			}
		}
	}

	#[test]
	fn kan_kou_tile_kou_representative() {
		for t1 in TILE_EACH_YONMA_WITH_RED_FIVE {
			let mut used = Tile37MultiSet::default();
			assert!(used.insert(t1));

			for t2 in TILE_EACH_YONMA_WITH_RED_FIVE {
				let mut used = used.clone();
				if !used.insert(t2) { continue; }

				for t3 in TILE_EACH_YONMA_WITH_RED_FIVE {
					let mut used = used.clone();
					if !used.insert(t3) { continue; }

					let expected = match [t1, t2, t3] {
						t![1m, 1m, 1m] => Some(KanKouToiTile::new(t!(1m), 0).unwrap()),
						t![2m, 2m, 2m] => Some(KanKouToiTile::new(t!(2m), 0).unwrap()),
						t![3m, 3m, 3m] => Some(KanKouToiTile::new(t!(3m), 0).unwrap()),
						t![4m, 4m, 4m] => Some(KanKouToiTile::new(t!(4m), 0).unwrap()),
						t![5m, 5m, 5m] => Some(KanKouToiTile::new(t!(5m), 0).unwrap()),
						t![5m, 5m, 0m] |
						t![5m, 0m, 5m] |
						t![0m, 5m, 5m] => Some(KanKouToiTile::new(t!(5m), 1).unwrap()),
						t![5m, 0m, 0m] |
						t![0m, 5m, 0m] |
						t![0m, 0m, 5m] => Some(KanKouToiTile::new(t!(5m), 2).unwrap()),
						t![0m, 0m, 0m] => Some(KanKouToiTile::new(t!(5m), 3).unwrap()),
						t![6m, 6m, 6m] => Some(KanKouToiTile::new(t!(6m), 0).unwrap()),
						t![7m, 7m, 7m] => Some(KanKouToiTile::new(t!(7m), 0).unwrap()),
						t![8m, 8m, 8m] => Some(KanKouToiTile::new(t!(8m), 0).unwrap()),
						t![9m, 9m, 9m] => Some(KanKouToiTile::new(t!(9m), 0).unwrap()),

						t![1p, 1p, 1p] => Some(KanKouToiTile::new(t!(1p), 0).unwrap()),
						t![2p, 2p, 2p] => Some(KanKouToiTile::new(t!(2p), 0).unwrap()),
						t![3p, 3p, 3p] => Some(KanKouToiTile::new(t!(3p), 0).unwrap()),
						t![4p, 4p, 4p] => Some(KanKouToiTile::new(t!(4p), 0).unwrap()),
						t![5p, 5p, 5p] => Some(KanKouToiTile::new(t!(5p), 0).unwrap()),
						t![5p, 5p, 0p] |
						t![5p, 0p, 5p] |
						t![0p, 5p, 5p] => Some(KanKouToiTile::new(t!(5p), 1).unwrap()),
						t![5p, 0p, 0p] |
						t![0p, 5p, 0p] |
						t![0p, 0p, 5p] => Some(KanKouToiTile::new(t!(5p), 2).unwrap()),
						t![0p, 0p, 0p] => Some(KanKouToiTile::new(t!(5p), 3).unwrap()),
						t![6p, 6p, 6p] => Some(KanKouToiTile::new(t!(6p), 0).unwrap()),
						t![7p, 7p, 7p] => Some(KanKouToiTile::new(t!(7p), 0).unwrap()),
						t![8p, 8p, 8p] => Some(KanKouToiTile::new(t!(8p), 0).unwrap()),
						t![9p, 9p, 9p] => Some(KanKouToiTile::new(t!(9p), 0).unwrap()),

						t![1s, 1s, 1s] => Some(KanKouToiTile::new(t!(1s), 0).unwrap()),
						t![2s, 2s, 2s] => Some(KanKouToiTile::new(t!(2s), 0).unwrap()),
						t![3s, 3s, 3s] => Some(KanKouToiTile::new(t!(3s), 0).unwrap()),
						t![4s, 4s, 4s] => Some(KanKouToiTile::new(t!(4s), 0).unwrap()),
						t![5s, 5s, 5s] => Some(KanKouToiTile::new(t!(5s), 0).unwrap()),
						t![5s, 5s, 0s] |
						t![5s, 0s, 5s] |
						t![0s, 5s, 5s] => Some(KanKouToiTile::new(t!(5s), 1).unwrap()),
						t![5s, 0s, 0s] |
						t![0s, 5s, 0s] |
						t![0s, 0s, 5s] => Some(KanKouToiTile::new(t!(5s), 2).unwrap()),
						t![0s, 0s, 0s] => Some(KanKouToiTile::new(t!(5s), 3).unwrap()),
						t![6s, 6s, 6s] => Some(KanKouToiTile::new(t!(6s), 0).unwrap()),
						t![7s, 7s, 7s] => Some(KanKouToiTile::new(t!(7s), 0).unwrap()),
						t![8s, 8s, 8s] => Some(KanKouToiTile::new(t!(8s), 0).unwrap()),
						t![9s, 9s, 9s] => Some(KanKouToiTile::new(t!(9s), 0).unwrap()),

						t![E, E, E] => Some(KanKouToiTile::new(t!(E), 0).unwrap()),
						t![S, S, S] => Some(KanKouToiTile::new(t!(S), 0).unwrap()),
						t![W, W, W] => Some(KanKouToiTile::new(t!(W), 0).unwrap()),
						t![N, N, N] => Some(KanKouToiTile::new(t!(N), 0).unwrap()),
						t![Wh, Wh, Wh] => Some(KanKouToiTile::new(t!(Wh), 0).unwrap()),
						t![G, G, G] => Some(KanKouToiTile::new(t!(G), 0).unwrap()),
						t![R, R, R] => Some(KanKouToiTile::new(t!(R), 0).unwrap()),

						_ => None,
					};
					let actual = KanKouToiTile::kou(t1, t2, t3);
					assert_eq!(actual, expected);
				}
			}
		}
	}

	#[test]
	fn kan_kou_tile_pair_representative() {
		for t1 in TILE_EACH_YONMA_WITH_RED_FIVE {
			let mut used = Tile37MultiSet::default();
			assert!(used.insert(t1));

			for t2 in TILE_EACH_YONMA_WITH_RED_FIVE {
				let mut used = used.clone();
				if !used.insert(t2) { continue; }

				let expected = match [t1, t2] {
					t![1m, 1m] => Some(KanKouToiTile::new(t!(1m), 0).unwrap()),
					t![2m, 2m] => Some(KanKouToiTile::new(t!(2m), 0).unwrap()),
					t![3m, 3m] => Some(KanKouToiTile::new(t!(3m), 0).unwrap()),
					t![4m, 4m] => Some(KanKouToiTile::new(t!(4m), 0).unwrap()),
					t![5m, 5m] => Some(KanKouToiTile::new(t!(5m), 0).unwrap()),
					t![5m, 0m] |
					t![0m, 5m] => Some(KanKouToiTile::new(t!(5m), 1).unwrap()),
					t![0m, 0m] => Some(KanKouToiTile::new(t!(5m), 2).unwrap()),
					t![6m, 6m] => Some(KanKouToiTile::new(t!(6m), 0).unwrap()),
					t![7m, 7m] => Some(KanKouToiTile::new(t!(7m), 0).unwrap()),
					t![8m, 8m] => Some(KanKouToiTile::new(t!(8m), 0).unwrap()),
					t![9m, 9m] => Some(KanKouToiTile::new(t!(9m), 0).unwrap()),

					t![1p, 1p] => Some(KanKouToiTile::new(t!(1p), 0).unwrap()),
					t![2p, 2p] => Some(KanKouToiTile::new(t!(2p), 0).unwrap()),
					t![3p, 3p] => Some(KanKouToiTile::new(t!(3p), 0).unwrap()),
					t![4p, 4p] => Some(KanKouToiTile::new(t!(4p), 0).unwrap()),
					t![5p, 5p] => Some(KanKouToiTile::new(t!(5p), 0).unwrap()),
					t![5p, 0p] |
					t![0p, 5p] => Some(KanKouToiTile::new(t!(5p), 1).unwrap()),
					t![0p, 0p] => Some(KanKouToiTile::new(t!(5p), 2).unwrap()),
					t![6p, 6p] => Some(KanKouToiTile::new(t!(6p), 0).unwrap()),
					t![7p, 7p] => Some(KanKouToiTile::new(t!(7p), 0).unwrap()),
					t![8p, 8p] => Some(KanKouToiTile::new(t!(8p), 0).unwrap()),
					t![9p, 9p] => Some(KanKouToiTile::new(t!(9p), 0).unwrap()),

					t![1s, 1s] => Some(KanKouToiTile::new(t!(1s), 0).unwrap()),
					t![2s, 2s] => Some(KanKouToiTile::new(t!(2s), 0).unwrap()),
					t![3s, 3s] => Some(KanKouToiTile::new(t!(3s), 0).unwrap()),
					t![4s, 4s] => Some(KanKouToiTile::new(t!(4s), 0).unwrap()),
					t![5s, 5s] => Some(KanKouToiTile::new(t!(5s), 0).unwrap()),
					t![5s, 0s] |
					t![0s, 5s] => Some(KanKouToiTile::new(t!(5s), 1).unwrap()),
					t![0s, 0s] => Some(KanKouToiTile::new(t!(5s), 2).unwrap()),
					t![6s, 6s] => Some(KanKouToiTile::new(t!(6s), 0).unwrap()),
					t![7s, 7s] => Some(KanKouToiTile::new(t!(7s), 0).unwrap()),
					t![8s, 8s] => Some(KanKouToiTile::new(t!(8s), 0).unwrap()),
					t![9s, 9s] => Some(KanKouToiTile::new(t!(9s), 0).unwrap()),

					t![E, E] => Some(KanKouToiTile::new(t!(E), 0).unwrap()),
					t![S, S] => Some(KanKouToiTile::new(t!(S), 0).unwrap()),
					t![W, W] => Some(KanKouToiTile::new(t!(W), 0).unwrap()),
					t![N, N] => Some(KanKouToiTile::new(t!(N), 0).unwrap()),
					t![Wh, Wh] => Some(KanKouToiTile::new(t!(Wh), 0).unwrap()),
					t![G, G] => Some(KanKouToiTile::new(t!(G), 0).unwrap()),
					t![R, R] => Some(KanKouToiTile::new(t!(R), 0).unwrap()),

					_ => None,
				};
				let actual = KanKouToiTile::toi(t1, t2);
				assert_eq!(actual, expected);
			}
		}
	}

	#[test]
	fn shun_rest() {
		assert_eq!(tsl!(1m).shun_rest(), (tn!(2m), tn!(3m)));
		assert_eq!(tsl!(2m).shun_rest(), (tn!(3m), tn!(4m)));
		assert_eq!(tsl!(3m).shun_rest(), (tn!(4m), tn!(5m)));
		assert_eq!(tsl!(4m).shun_rest(), (tn!(5m), tn!(6m)));
		assert_eq!(tsl!(5m).shun_rest(), (tn!(6m), tn!(7m)));
		assert_eq!(tsl!(0m).shun_rest(), (tn!(6m), tn!(7m)));
		assert_eq!(tsl!(6m).shun_rest(), (tn!(7m), tn!(8m)));
		assert_eq!(tsl!(7m).shun_rest(), (tn!(8m), tn!(9m)));

		assert_eq!(tsl!(1p).shun_rest(), (tn!(2p), tn!(3p)));
		assert_eq!(tsl!(2p).shun_rest(), (tn!(3p), tn!(4p)));
		assert_eq!(tsl!(3p).shun_rest(), (tn!(4p), tn!(5p)));
		assert_eq!(tsl!(4p).shun_rest(), (tn!(5p), tn!(6p)));
		assert_eq!(tsl!(5p).shun_rest(), (tn!(6p), tn!(7p)));
		assert_eq!(tsl!(0p).shun_rest(), (tn!(6p), tn!(7p)));
		assert_eq!(tsl!(6p).shun_rest(), (tn!(7p), tn!(8p)));
		assert_eq!(tsl!(7p).shun_rest(), (tn!(8p), tn!(9p)));

		assert_eq!(tsl!(1s).shun_rest(), (tn!(2s), tn!(3s)));
		assert_eq!(tsl!(2s).shun_rest(), (tn!(3s), tn!(4s)));
		assert_eq!(tsl!(3s).shun_rest(), (tn!(4s), tn!(5s)));
		assert_eq!(tsl!(4s).shun_rest(), (tn!(5s), tn!(6s)));
		assert_eq!(tsl!(5s).shun_rest(), (tn!(6s), tn!(7s)));
		assert_eq!(tsl!(0s).shun_rest(), (tn!(6s), tn!(7s)));
		assert_eq!(tsl!(6s).shun_rest(), (tn!(7s), tn!(8s)));
		assert_eq!(tsl!(7s).shun_rest(), (tn!(8s), tn!(9s)));
	}

	#[test]
	fn shun() {
		for &t1 in NumberTile::each(GameType::Yonma) {
			let Ok(t1) = ShunLowTile::try_from(t1) else { continue; };
			for &t2 in NumberTile::each(GameType::Yonma) {
				for &t3 in NumberTile::each(GameType::Yonma) {
					for &t_shun in &[
						ShunTile::M123,
						ShunTile::M234,
						ShunTile::M345,
						ShunTile::M340,
						ShunTile::M456,
						ShunTile::M406,
						ShunTile::M567,
						ShunTile::M067,
						ShunTile::M678,
						ShunTile::M789,
						ShunTile::P123,
						ShunTile::P234,
						ShunTile::P345,
						ShunTile::P340,
						ShunTile::P456,
						ShunTile::P406,
						ShunTile::P567,
						ShunTile::P067,
						ShunTile::P678,
						ShunTile::P789,
						ShunTile::S123,
						ShunTile::S234,
						ShunTile::S345,
						ShunTile::S340,
						ShunTile::S456,
						ShunTile::S406,
						ShunTile::S567,
						ShunTile::S067,
						ShunTile::S678,
						ShunTile::S789,
					] {
						let t_shun_actual = ShunTile::new(t1, t2, t3);
						let is_valid = matches!(
							(t1, t2, t3, t_shun),
							(tsl!(1m), tn!(2m), tn!(3m), ShunTile::M123) |
							(tsl!(2m), tn!(3m), tn!(4m), ShunTile::M234) |
							(tsl!(3m), tn!(4m), tn!(5m), ShunTile::M345) |
							(tsl!(3m), tn!(4m), tn!(0m), ShunTile::M340) |
							(tsl!(4m), tn!(5m), tn!(6m), ShunTile::M456) |
							(tsl!(4m), tn!(0m), tn!(6m), ShunTile::M406) |
							(tsl!(5m), tn!(6m), tn!(7m), ShunTile::M567) |
							(tsl!(0m), tn!(6m), tn!(7m), ShunTile::M067) |
							(tsl!(6m), tn!(7m), tn!(8m), ShunTile::M678) |
							(tsl!(7m), tn!(8m), tn!(9m), ShunTile::M789) |

							(tsl!(1p), tn!(2p), tn!(3p), ShunTile::P123) |
							(tsl!(2p), tn!(3p), tn!(4p), ShunTile::P234) |
							(tsl!(3p), tn!(4p), tn!(5p), ShunTile::P345) |
							(tsl!(3p), tn!(4p), tn!(0p), ShunTile::P340) |
							(tsl!(4p), tn!(5p), tn!(6p), ShunTile::P456) |
							(tsl!(4p), tn!(0p), tn!(6p), ShunTile::P406) |
							(tsl!(5p), tn!(6p), tn!(7p), ShunTile::P567) |
							(tsl!(0p), tn!(6p), tn!(7p), ShunTile::P067) |
							(tsl!(6p), tn!(7p), tn!(8p), ShunTile::P678) |
							(tsl!(7p), tn!(8p), tn!(9p), ShunTile::P789) |

							(tsl!(1s), tn!(2s), tn!(3s), ShunTile::S123) |
							(tsl!(2s), tn!(3s), tn!(4s), ShunTile::S234) |
							(tsl!(3s), tn!(4s), tn!(5s), ShunTile::S345) |
							(tsl!(3s), tn!(4s), tn!(0s), ShunTile::S340) |
							(tsl!(4s), tn!(5s), tn!(6s), ShunTile::S456) |
							(tsl!(4s), tn!(0s), tn!(6s), ShunTile::S406) |
							(tsl!(5s), tn!(6s), tn!(7s), ShunTile::S567) |
							(tsl!(0s), tn!(6s), tn!(7s), ShunTile::S067) |
							(tsl!(6s), tn!(7s), tn!(8s), ShunTile::S678) |
							(tsl!(7s), tn!(8s), tn!(9s), ShunTile::S789),
						);
						if is_valid {
							assert_eq!(t_shun_actual, Some(t_shun));
							assert_eq!(t_shun.shun(), (t1, t2, t3));
						}
						else {
							assert_ne!(t_shun_actual, Some(t_shun));
						}
					}
				}
			}
		}
	}

	#[test]
	fn wind_tile_as_ref_and_from() {
		for (input, expected) in [
			(tw!(E), t!(E)),
			(tw!(S), t!(S)),
			(tw!(W), t!(W)),
			(tw!(N), t!(N)),
		] {
			let actual: &Tile = input.as_ref();
			assert_eq!(*actual, expected);
			let actual = Tile::from(input);
			assert_eq!(actual, expected);
			let actual = WindTile::try_from(expected).unwrap();
			assert_eq!(actual, input);
			() = NumberTile::try_from(expected).unwrap_err();
			() = DragonTile::try_from(expected).unwrap_err();
		}
	}

	#[test]
	fn dragon_tile_as_ref_and_from() {
		for (input, expected) in [
			(td!(Wh), t!(Wh)),
			(td!(G), t!(G)),
			(td!(R), t!(R)),
		] {
			let actual: &Tile = input.as_ref();
			assert_eq!(*actual, expected);
			let actual = Tile::from(input);
			assert_eq!(actual, expected);
			let actual = DragonTile::try_from(expected).unwrap();
			assert_eq!(actual, input);
			() = NumberTile::try_from(expected).unwrap_err();
			() = WindTile::try_from(expected).unwrap_err();
		}
	}

	#[test]
	fn str() {
		for (t, s) in [
			(t!(1m), "1m"),
			(t!(2m), "2m"),
			(t!(3m), "3m"),
			(t!(4m), "4m"),
			(t!(5m), "5m"),
			(t!(0m), "0m"),
			(t!(6m), "6m"),
			(t!(7m), "7m"),
			(t!(8m), "8m"),
			(t!(9m), "9m"),
			(t!(1p), "1p"),
			(t!(2p), "2p"),
			(t!(3p), "3p"),
			(t!(4p), "4p"),
			(t!(5p), "5p"),
			(t!(0p), "0p"),
			(t!(6p), "6p"),
			(t!(7p), "7p"),
			(t!(8p), "8p"),
			(t!(9p), "9p"),
			(t!(1s), "1s"),
			(t!(2s), "2s"),
			(t!(3s), "3s"),
			(t!(4s), "4s"),
			(t!(5s), "5s"),
			(t!(0s), "0s"),
			(t!(6s), "6s"),
			(t!(7s), "7s"),
			(t!(8s), "8s"),
			(t!(9s), "9s"),
			(t!(E), "E"),
			(t!(S), "S"),
			(t!(W), "W"),
			(t!(N), "N"),
			(t!(Wh), "Wh"),
			(t!(G), "G"),
			(t!(R), "R"),
		] {
			assert_eq!(std::format!("{t}"), s);
			assert_eq!(std::format!("{t:?}"), s);

			if let Ok(t) = NumberTile::try_from(t) {
				assert_eq!(std::format!("{t}"), s);
				assert_eq!(std::format!("{t:?}"), s);

				if let Ok(t) = ShunLowTile::try_from(t) {
					assert_eq!(std::format!("{t}"), s);
					assert_eq!(std::format!("{t:?}"), s);
				}

				let t = NumberTileClassified::from(t);
				assert_eq!(std::format!("{t}"), s);
				assert_eq!(std::format!("{t:?}"), std::format!("NumberTileClassified {{ suit: {:?}, number: {:?} }}", t.suit, t.number));

				assert_eq!(std::format!("{}", t.number), &s[..1]);
				assert_eq!(std::format!("{:?}", t.number), &s[..1]);

				assert_eq!(std::format!("{}", t.suit), &s[1..]);
				assert_eq!(std::format!("{:?}", t.suit), &s[1..]);
			}
			else if let Ok(t) = WindTile::try_from(t) {
				assert_eq!(std::format!("{t}"), s);
				assert_eq!(std::format!("{t:?}"), s);
			}
			else if let Ok(t) = DragonTile::try_from(t) {
				assert_eq!(std::format!("{t}"), s);
				assert_eq!(std::format!("{t:?}"), s);
			}
			else {
				unreachable!();
			}
		}

		for (s, t) in [
			("1m", t!(1m)),
			("2m", t!(2m)),
			("3m", t!(3m)),
			("4m", t!(4m)),
			("5m", t!(5m)),
			("0m", t!(0m)),
			("6m", t!(6m)),
			("7m", t!(7m)),
			("8m", t!(8m)),
			("9m", t!(9m)),
			("1p", t!(1p)),
			("2p", t!(2p)),
			("3p", t!(3p)),
			("4p", t!(4p)),
			("5p", t!(5p)),
			("0p", t!(0p)),
			("6p", t!(6p)),
			("7p", t!(7p)),
			("8p", t!(8p)),
			("9p", t!(9p)),
			("1s", t!(1s)),
			("2s", t!(2s)),
			("3s", t!(3s)),
			("4s", t!(4s)),
			("5s", t!(5s)),
			("0s", t!(0s)),
			("6s", t!(6s)),
			("7s", t!(7s)),
			("8s", t!(8s)),
			("9s", t!(9s)),
			("E", t!(E)),
			("1z", t!(E)),
			("S", t!(S)),
			("2z", t!(S)),
			("W", t!(W)),
			("3z", t!(W)),
			("N", t!(N)),
			("4z", t!(N)),
			("Wh", t!(Wh)),
			("5z", t!(Wh)),
			("G", t!(G)),
			("6z", t!(G)),
			("R", t!(R)),
			("7z", t!(R)),
		] {
			assert_eq!(s.parse::<Tile>().unwrap(), t);

			if let Ok(t) = NumberTile::try_from(t) {
				assert_eq!(s.parse::<NumberTile>().unwrap(), t);
			}
			else if let Ok(t) = WindTile::try_from(t) {
				assert_eq!(s.parse::<WindTile>().unwrap(), t);
			}
			else if let Ok(t) = DragonTile::try_from(t) {
				assert_eq!(s.parse::<DragonTile>().unwrap(), t);
			}
			else {
				unreachable!();
			}
		}
	}
}
