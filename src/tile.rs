use generic_array::ArrayLength;

use crate::{
	ArrayVec,
	GameType,
	HandMeldType,
	SortingNetwork,
};

// Tile values are chosen such that:
// - Tile order is the same as the value order.
// - `Five` and `FiveRed` have different values but can be compared equal by masking out the difference. This is used so that pairs and kous containing akadora can be handled
//   just as easily as those not containing akadora, and so that melds / hands that differ only in the position of akadora can be considered equal.
// - `FiveRed` is ordered between `Four` and `Six` just like `Five` is.
// - Operations like `NumberTile::suit`, `NumberTile::shun_rest`, etc can be performed using arithmetic instead of requiring LUTs.
//
// Taken together, this means that `FiveRed` must set one bit that no other tile sets,
// and that this bit must be the LSB so that `Four`'s value can be less than it and `Six`'s value can be greater than it.
// Thus every tile except `FiveRed` has a value that is a multiple of 2, and `FiveRed` tiles have the same value as the corresponding `Five` tile
// but with the LSB set.

/// A tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Tile {
	Man1 = 0x00,
	Man2 = 0x02,
	Man3 = 0x04,
	Man4 = 0x06,
	Man5 = 0x08,
	/// Red `Man5`
	Man0 = 0x09,
	Man6 = 0x0A,
	Man7 = 0x0C,
	Man8 = 0x0E,
	Man9 = 0x10,
	Pin1 = 0x12,
	Pin2 = 0x14,
	Pin3 = 0x16,
	Pin4 = 0x18,
	Pin5 = 0x1A,
	/// Red `Pin5`
	Pin0 = 0x1B,
	Pin6 = 0x1C,
	Pin7 = 0x1E,
	Pin8 = 0x20,
	Pin9 = 0x22,
	Sou1 = 0x24,
	Sou2 = 0x26,
	Sou3 = 0x28,
	Sou4 = 0x2A,
	Sou5 = 0x2C,
	/// Red `Sou5`
	Sou0 = 0x2D,
	Sou6 = 0x2E,
	Sou7 = 0x30,
	Sou8 = 0x32,
	Sou9 = 0x34,
	/// East wind
	Ton = 0x36,
	/// South wind
	Nan = 0x38,
	/// West wind
	Shaa = 0x3A,
	/// North wind
	Pei = 0x3C,
	/// White dragon
	Haku = 0x3E,
	/// Green dragon
	Hatsu = 0x40,
	/// Red dragon
	Chun = 0x42,
}

/// A number tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum NumberTile {
	Man1 = 0x00,
	Man2 = 0x02,
	Man3 = 0x04,
	Man4 = 0x06,
	Man5 = 0x08,
	/// Red `Man5`
	Man0 = 0x09,
	Man6 = 0x0A,
	Man7 = 0x0C,
	Man8 = 0x0E,
	Man9 = 0x10,
	Pin1 = 0x12,
	Pin2 = 0x14,
	Pin3 = 0x16,
	Pin4 = 0x18,
	Pin5 = 0x1A,
	/// Red `Pin5`
	Pin0 = 0x1B,
	Pin6 = 0x1C,
	Pin7 = 0x1E,
	Pin8 = 0x20,
	Pin9 = 0x22,
	Sou1 = 0x24,
	Sou2 = 0x26,
	Sou3 = 0x28,
	Sou4 = 0x2A,
	Sou5 = 0x2C,
	/// Red `Sou5`
	Sou0 = 0x2D,
	Sou6 = 0x2E,
	Sou7 = 0x30,
	Sou8 = 0x32,
	Sou9 = 0x34,
}

/// A number tile that is the lowest tile of a shun.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ShunLowTile {
	Man1 = 0x00,
	Man2 = 0x02,
	Man3 = 0x04,
	Man4 = 0x06,
	Man5 = 0x08,
	/// Red `Man5`
	Man0 = 0x09,
	Man6 = 0x0A,
	Man7 = 0x0C,
	Pin1 = 0x12,
	Pin2 = 0x14,
	Pin3 = 0x16,
	Pin4 = 0x18,
	Pin5 = 0x1A,
	/// Red `Pin5`
	Pin0 = 0x1B,
	Pin6 = 0x1C,
	Pin7 = 0x1E,
	Sou1 = 0x24,
	Sou2 = 0x26,
	Sou3 = 0x28,
	Sou4 = 0x2A,
	Sou5 = 0x2C,
	/// Red `Sou5`
	Sou0 = 0x2D,
	Sou6 = 0x2E,
	Sou7 = 0x30,
}

/// A wind tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum WindTile {
	/// East
	Ton = 0x36,
	/// South
	Nan = 0x38,
	/// West
	Shaa = 0x3A,
	/// North
	Pei = 0x3C,
}

/// A dragon tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum DragonTile {
	/// White
	Haku = 0x3E,
	/// Green
	Hatsu = 0x40,
	/// Red
	Chun = 0x42,
}

/// A number tile broken down into its suit and number.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NumberTileClassified {
	pub suit: NumberSuit,
	pub number: Number,
}

/// The suit of a number tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum NumberSuit {
	/// Characters
	Man = 0,
	/// Wheels
	Pin = 1,
	/// Bamboo
	Sou = 2,
}

/// The value of a number tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Number {
	One = 0x00,
	Two = 0x02,
	Three = 0x04,
	Four = 0x06,
	Five = 0x08,
	FiveRed = 0x09,
	Six = 0x0A,
	Seven = 0x0C,
	Eight = 0x0E,
	Nine = 0x10,
}

/// A trait for comparing tiles based on treating `Five` and `FiveRed` tiles as equal.
pub trait CmpIgnoreRed {
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

	/// Returns all `Tile`s in a game of the given type.
	pub const fn all(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::Yonma => &t![
				1m, 1m, 1m, 1m,
				2m, 2m, 2m, 2m,
				3m, 3m, 3m, 3m,
				4m, 4m, 4m, 4m,
				5m, 5m, 5m, 0m,
				6m, 6m, 6m, 6m,
				7m, 7m, 7m, 7m,
				8m, 8m, 8m, 8m,
				9m, 9m, 9m, 9m,
				1p, 1p, 1p, 1p,
				2p, 2p, 2p, 2p,
				3p, 3p, 3p, 3p,
				4p, 4p, 4p, 4p,
				5p, 5p, 5p, 0p,
				6p, 6p, 6p, 6p,
				7p, 7p, 7p, 7p,
				8p, 8p, 8p, 8p,
				9p, 9p, 9p, 9p,
				1s, 1s, 1s, 1s,
				2s, 2s, 2s, 2s,
				3s, 3s, 3s, 3s,
				4s, 4s, 4s, 4s,
				5s, 5s, 5s, 0s,
				6s, 6s, 6s, 6s,
				7s, 7s, 7s, 7s,
				8s, 8s, 8s, 8s,
				9s, 9s, 9s, 9s,
				E, E, E, E,
				S, S, S, S,
				W, W, W, W,
				N, N, N, N,
				Wh, Wh, Wh, Wh,
				G, G, G, G,
				R, R, R, R,
			],

			GameType::Sanma => &t![
				1m, 1m, 1m, 1m,
				9m, 9m, 9m, 9m,
				1p, 1p, 1p, 1p,
				2p, 2p, 2p, 2p,
				3p, 3p, 3p, 3p,
				4p, 4p, 4p, 4p,
				5p, 5p, 5p, 0p,
				6p, 6p, 6p, 6p,
				7p, 7p, 7p, 7p,
				8p, 8p, 8p, 8p,
				9p, 9p, 9p, 9p,
				1s, 1s, 1s, 1s,
				2s, 2s, 2s, 2s,
				3s, 3s, 3s, 3s,
				4s, 4s, 4s, 4s,
				5s, 5s, 5s, 0s,
				6s, 6s, 6s, 6s,
				7s, 7s, 7s, 7s,
				8s, 8s, 8s, 8s,
				9s, 9s, 9s, 9s,
				E, E, E, E,
				S, S, S, S,
				W, W, W, W,
				N, N, N, N,
				Wh, Wh, Wh, Wh,
				G, G, G, G,
				R, R, R, R,
			],
		}
	}

	/// Parses a sequence of `Tile`s and an optional meld type from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
	///
	/// Ref: <https://note.com/yuarasino/n/n1ba95bf3b618>
	///
	/// Note that this library does not retain information about which tile was called or which player it was called from.
	/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
	/// but the specific position of the marker within the meld (which identifies the tile that was called)
	/// and the order of the tiles (which identifies the player who the tile was called from) are ignored.
	///
	/// If `end` is set to `Some`, parsing stops when that byte is encountered, and the remaining string is returned.
	/// If `end` is set to `None`, the whole string is parsed, and an empty string is returned.
	///
	/// # Errors
	///
	/// Returns an error if the string does not have valid syntax.
	#[expect(clippy::result_unit_err)]
	pub fn parse_run_until<N>(s: &[u8], end: Option<u8>) -> Result<(ArrayVec<Self, N>, Option<HandMeldType>, &[u8]), ()> where N: ArrayLength {
		#[derive(Clone, Copy, Debug)]
		enum Op {
			// An error variant is defined here because the alternative is `OPS: [Option<Op>; 256]` which ends up encoding `None::<Op>` as `0b03`.
			// It's nicer to encode the error case as `0b00` since most of the table will be filled with that.
			InvalidByte,
			AddToCurrentRun(Tile, bool),
			SetCurrentRunSuit(Tile, bool),
			SetMeldType(HandMeldType),
		}

		// Micro-optimization: `let op = match b { ... };` generates a jump table where the op code is inlined into the jump targets, making the function much larger.
		// Making an ops array this way forces the compiler to generate a LUT, which is preferable.
		const OPS: [Op; 256] = {
			let mut result = [Op::InvalidByte; 256];

			result[b'1' as usize] = Op::AddToCurrentRun(t!(1m), true);
			result[b'2' as usize] = Op::AddToCurrentRun(t!(2m), true);
			result[b'3' as usize] = Op::AddToCurrentRun(t!(3m), true);
			result[b'4' as usize] = Op::AddToCurrentRun(t!(4m), true);
			result[b'5' as usize] = Op::AddToCurrentRun(t!(5m), true);
			result[b'0' as usize] = Op::AddToCurrentRun(t!(0m), false);
			result[b'6' as usize] = Op::AddToCurrentRun(t!(6m), true);
			result[b'7' as usize] = Op::AddToCurrentRun(t!(7m), true);
			result[b'8' as usize] = Op::AddToCurrentRun(t!(8m), false);
			result[b'9' as usize] = Op::AddToCurrentRun(t!(9m), false);

			result[b'm' as usize] = Op::SetCurrentRunSuit(t!(1m), false);
			result[b'p' as usize] = Op::SetCurrentRunSuit(t!(1p), false);
			result[b's' as usize] = Op::SetCurrentRunSuit(t!(1s), false);
			result[b'z' as usize] = Op::SetCurrentRunSuit(t!(1z), true);

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

				Op::AddToCurrentRun(t, is_valid_z) => {
					result.push(t).map_err(|_| ())?;
					current_run_is_valid_z &= is_valid_z;
				},

				Op::SetCurrentRunSuit(suit_base, check_is_valid_z) => {
					unsafe { core::hint::assert_unchecked(current_run_start <= result.len()); }
					let current_run = &mut result[current_run_start..];
					if current_run.is_empty() || (check_is_valid_z && !current_run_is_valid_z) {
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
	pub fn indicates_dora(self, game_type: GameType) -> Self {
		// Micro-optimization: This generates branchless code and avoids the need for a LUT.
		//
		// Tested exhaustively in the `tile_indicates_dora` test.

		let this = self as u8;

		let offset = 1_u64 << (this >> 1);
		let sub_number_wrap = if (0b0000000_100000000_100000000_100000000_u64 & offset) != 0 { t!(1p) as u8 - t!(1m) as u8 } else { 0 };
		let sub_wind_wrap = if self == t!(N) { t!(Wh) as u8 - t!(E) as u8 } else { 0 };
		let sub_dragon_wrap = if self == t!(R) { t!(R) as u8 + 2 - t!(Wh) as u8 } else { 0 };
		let add_1m_sanma = if self == t!(1m) && matches!(game_type, GameType::Sanma) { t!(9m) as u8 - t!(2m) as u8 } else { 0 };

		let result = (this & !0b1) + 2 - sub_number_wrap - sub_wind_wrap - sub_dragon_wrap + add_1m_sanma;

		// SAFETY: Lines up with the explicit values given to the `Tile` variants,
		// and tested exhaustively in the `tile_indicates_dora` test.
		unsafe { core::mem::transmute::<u8, Self>(result) }
	}

	pub(crate) const fn is_simple(self) -> bool {
		// Micro-optimization: Doing `match self { t!(2m | 3m | ...` instead generates a jump table.
		// Doing `matches!(self as u8, 0x02..0x10 | ...` generates a series of range checks and branches for each range.
		// Doing this bit test on a constant generates exactly that, which is optimal.
		//
		// Tested exhaustively in the `tile_is_simple` test.
		(0b0000000_011111110_011111110_011111110_u64 & (1_u64 << ((self as u8) >> 1))) != 0
	}

	pub(crate) const fn is_red(self) -> bool {
		(self as u8) & 0b1 != 0
	}

	#[must_use]
	pub(crate) const fn remove_red(self) -> Self {
		let result = (self as u8) & !0b1;
		unsafe { core::mem::transmute::<u8, Self>(result) }
	}

	// TODO(rustup): Inline this into `From<NumberTile>` impl when `const impl From` is possible.
	pub(crate) const fn const_from_nt(t: NumberTile) -> Self {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `NumberTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from_and_try_from` test.
		unsafe { *<*const _>::cast(&raw const t) }
	}

	// TODO(rustup): Inline this into `From<ShunLowTile>` impl when `const impl From` is possible.
	pub(crate) const fn const_from_slt(t: ShunLowTile) -> Self {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `ShunLowTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from_and_try_from` test.
		unsafe { *<*const _>::cast(&raw const t) }
	}
}

impl CmpIgnoreRed for Tile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 1).cmp(&((*other as u8) >> 1))
	}
}

impl core::fmt::Debug for Tile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for Tile {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str(match self {
			t!(1m) => "1m",
			t!(2m) => "2m",
			t!(3m) => "3m",
			t!(4m) => "4m",
			t!(5m) => "5m",
			t!(0m) => "0m",
			t!(6m) => "6m",
			t!(7m) => "7m",
			t!(8m) => "8m",
			t!(9m) => "9m",
			t!(1p) => "1p",
			t!(2p) => "2p",
			t!(3p) => "3p",
			t!(4p) => "4p",
			t!(5p) => "5p",
			t!(0p) => "0p",
			t!(6p) => "6p",
			t!(7p) => "7p",
			t!(8p) => "8p",
			t!(9p) => "9p",
			t!(1s) => "1s",
			t!(2s) => "2s",
			t!(3s) => "3s",
			t!(4s) => "4s",
			t!(5s) => "5s",
			t!(0s) => "0s",
			t!(6s) => "6s",
			t!(7s) => "7s",
			t!(8s) => "8s",
			t!(9s) => "9s",
			t!(E) => "E",
			t!(S) => "S",
			t!(W) => "W",
			t!(N) => "N",
			t!(Wh) => "Wh",
			t!(G) => "G",
			t!(R) => "R",
		})
	}
}

impl From<NumberTile> for Tile {
	fn from(t: NumberTile) -> Self {
		*t.as_ref()
	}
}

impl From<ShunLowTile> for Tile {
	fn from(t: ShunLowTile) -> Self {
		*t.as_ref()
	}
}

impl From<WindTile> for Tile {
	fn from(t: WindTile) -> Self {
		*t.as_ref()
	}
}

impl From<DragonTile> for Tile {
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
			&[number @ b'0'..=b'9', suit @ (b'm' | b'p' | b's' | b'z')] => {
				let number = match number {
					b'0' => Number::FiveRed,
					b'1'..=b'9' => unsafe { core::mem::transmute::<u8, Number>((number - b'1') << 1) },
					_ => unreachable!(),
				};
				let suit = match suit {
					b'm' => NumberSuit::Man,
					b'p' => NumberSuit::Pin,
					b's' => NumberSuit::Sou,
					b'z' => {
						let tile = t!(E) as u8 + number as u8;
						return (tile <= t!(R) as u8 && tile & 0b1 == 0).then(|| unsafe { core::mem::transmute::<u8, Self>(tile) }).ok_or(());
					},
					_ => unreachable!(),
				};
				NumberTile::from(NumberTileClassified { suit, number }).into()
			},

			b"E" => t!(E),
			b"S" => t!(S),
			b"W" => t!(W),
			b"N" => t!(N),

			b"Wh" => t!(Wh),
			b"G" => t!(G),
			b"R" => t!(R),

			_ => return Err(()),
		})
	}
}

impl SortingNetwork for Tile {
	fn sort_three(arr: &mut [Self; 3]) {
		let arr = unsafe { &mut *(<*mut [Self; 3]>::cast::<[u8; 3]>(arr)) };
		SortingNetwork::sort_three(arr);
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

	/// Returns all `NumberTile`s in a game of the given type.
	pub const fn all(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::Yonma => &tn![
				1m, 1m, 1m, 1m,
				2m, 2m, 2m, 2m,
				3m, 3m, 3m, 3m,
				4m, 4m, 4m, 4m,
				5m, 5m, 5m, 0m,
				6m, 6m, 6m, 6m,
				7m, 7m, 7m, 7m,
				8m, 8m, 8m, 8m,
				9m, 9m, 9m, 9m,
				1p, 1p, 1p, 1p,
				2p, 2p, 2p, 2p,
				3p, 3p, 3p, 3p,
				4p, 4p, 4p, 4p,
				5p, 5p, 5p, 0p,
				6p, 6p, 6p, 6p,
				7p, 7p, 7p, 7p,
				8p, 8p, 8p, 8p,
				9p, 9p, 9p, 9p,
				1s, 1s, 1s, 1s,
				2s, 2s, 2s, 2s,
				3s, 3s, 3s, 3s,
				4s, 4s, 4s, 4s,
				5s, 5s, 5s, 0s,
				6s, 6s, 6s, 6s,
				7s, 7s, 7s, 7s,
				8s, 8s, 8s, 8s,
				9s, 9s, 9s, 9s,
			],

			GameType::Sanma => &tn![
				1m, 1m, 1m, 1m,
				9m, 9m, 9m, 9m,
				1p, 1p, 1p, 1p,
				2p, 2p, 2p, 2p,
				3p, 3p, 3p, 3p,
				4p, 4p, 4p, 4p,
				5p, 5p, 5p, 0p,
				6p, 6p, 6p, 6p,
				7p, 7p, 7p, 7p,
				8p, 8p, 8p, 8p,
				9p, 9p, 9p, 9p,
				1s, 1s, 1s, 1s,
				2s, 2s, 2s, 2s,
				3s, 3s, 3s, 3s,
				4s, 4s, 4s, 4s,
				5s, 5s, 5s, 0s,
				6s, 6s, 6s, 6s,
				7s, 7s, 7s, 7s,
				8s, 8s, 8s, 8s,
				9s, 9s, 9s, 9s,
			],
		}
	}

	pub const fn number(self) -> Number {
		// Micro-optimization: Doing the math in `usize` avoids rustc inserting `zext.b` on RV to clamp intermediate results to `u8`.

		// TODO(rustup): Replace with `.min()` when `usize: impl const Ord` becomes stable.
		const fn const_min(a: usize, b: usize) -> usize {
			if a < b { a } else { b }
		}

		// Micro-optimization: There are three ways to normalize `n = self as usize` into the manzu range.
		//
		// - Tree subtraction and minimum: `let n2 = n.min(n.wrapping_sub(0x12)); let n = n2.min(n.wrapping_sub(0x24));`
		// - Linear subtraction and minimum: `let n = n.min(n.wrapping_sub(0x12)); let n = n.min(n.wrapping_sub(0x12));`
		// - Linear conditional subtraction: `let n = n < 0x12 ? n : n - 0x12; let n = n < 0x12 ? n : n - 0x12;`
		//
		// The first two work because we know that `n <= 0x34`, so if the subtraction overflows the result will be greater than the original value.
		//
		// The first is better than the second because the two subtractions are independent, so they can execute in parallel on an OoO CPU with multiple adders.
		// Neither rustc, clang nor gcc are smart enough to optimize the second into the first.
		//
		// The third is clearest, but neither rustc nor clang are smart enough to optimize it into the second, even when they know `self as usize`'s range.
		// gcc is able to optimize it into something that resembles the first (it selects between a subtraction by 0x12 and a subtraction by 0x24),
		// though it ends up using branches instead of `minu` / `cmov` so it's worse than the first version.
		//
		// So we write the first version manually.
		//
		// Ref: https://gcc.godbolt.org/z/oYscP7TWs
		let n = self as usize - t!(1m) as usize;
		let n = const_min(
			const_min(
				n,
				n.wrapping_sub(t!(1p) as usize - t!(1m) as usize),
			),
			n.wrapping_sub(t!(1s) as usize - t!(1m) as usize),
		);
		let n = n + Number::One as usize;
		// SAFETY: Lines up with the explicit values given to the `NumberTile`, `Number` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		#[expect(clippy::cast_possible_truncation)]
		unsafe { core::mem::transmute::<u8, Number>(n as u8) }
	}

	pub const fn suit(self) -> NumberSuit {
		let this = self as u8 - tn!(1m) as u8;
		let suit = NumberSuit::Sou as u8 - (this < tn!(1p) as u8 - t!(1m) as u8) as u8 - (this < tn!(1s) as u8 - t!(1m) as u8) as u8;
		// SAFETY: Lines up with the explicit values given to the `NumberTile`, `Number` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute::<u8, NumberSuit>(suit) }
	}

	pub(crate) const fn previous_in_sequence(self) -> Option<Self> {
		// Micro-optimization: Same trick as `Tile::is_simple`.
		//
		// Tested exhaustively in the `number_tile_previous_next_in_sequence` test.

		if 0b000000001_000000001_000000001_u32 & (1_u32 << (self as u8 >> 1)) == 0 {
			let prev = (self as u8 & !0b1) - 2;
			let prev = unsafe { core::mem::transmute::<u8, Self>(prev) };
			Some(prev)
		}
		else {
			None
		}
	}

	pub(crate) const fn next_in_sequence(self) -> Option<Self> {
		// Micro-optimization: Same trick as `Tile::is_simple`.
		//
		// Tested exhaustively in the `number_tile_previous_next_in_sequence` test.

		if 0b100000000_100000000_100000000_u32 & (1_u32 << (self as u8 >> 1)) == 0 {
			let next = (self as u8 & !0b1) + 2;
			let next = unsafe { core::mem::transmute::<u8, Self>(next) };
			Some(next)
		}
		else {
			None
		}
	}

	pub(crate) fn is_next_in_sequence(self, previous: Self) -> bool {
		previous.next_in_sequence().eq_ignore_red(&Some(self))
	}

	/// Extracts the `Number`s of each of the given `Self`s, assuming that all `Self`s have the same `NumberSuit`.
	///
	/// SAFETY: It is unsound if all `Self`s do not have the same `NumberSuit`.
	pub(crate) unsafe fn unchecked_numbers_assume_suit(ts: [Self; 5]) -> [Number; 5] {
		const DIFF_8: u8 = t!(1p) as u8 - t!(1m) as u8;
		const DIFF_32: u32 = {
			let diff = DIFF_8 as u32;
			(diff << 24) | (diff << 16) | (diff << 8) | diff
		};

		let t1 = ts[0] as u8;
		let ts = ((ts[4] as u32) << 24) | ((ts[3] as u32) << 16) | ((ts[2] as u32) << 8) | (ts[1] as u32);

		let (diff_8, diff_32) = if t1 >= t!(1p) as u8 { (DIFF_8, DIFF_32) } else { (0, 0) };
		let (t1, ts) = (t1 - diff_8, ts - diff_32);
		let (diff_8, diff_32) = if t1 >= t!(1p) as u8 { (DIFF_8, DIFF_32) } else { (0, 0) };
		let (t1, ts) = (t1 - diff_8, ts - diff_32);

		let [t2, t3, t4, t5] = ts.to_le_bytes();
		let n1 = unsafe { core::mem::transmute::<u8, Number>(t1) };
		let n2 = unsafe { core::mem::transmute::<u8, Number>(t2) };
		let n3 = unsafe { core::mem::transmute::<u8, Number>(t3) };
		let n4 = unsafe { core::mem::transmute::<u8, Number>(t4) };
		let n5 = unsafe { core::mem::transmute::<u8, Number>(t5) };
		[n1, n2, n3, n4, n5]
	}

	pub(crate) const fn is_red(self) -> bool {
		Tile::const_from_nt(self).is_red()
	}

	#[must_use]
	pub(crate) const fn make_red(self) -> Self {
		if 0b000010000_000010000_000010000_u32 & (0b1 << (self as u8 >> 1)) != 0 {
			let result = (self as u8) | 0b1;
			unsafe { core::mem::transmute::<u8, Self>(result) }
		}
		else {
			self
		}
	}

	// TODO(rustup): Inline this into `From<NumberTileClassified>` impl when `const impl From` is possible.
	pub(crate) const fn const_from(t: NumberTileClassified) -> Self {
		let NumberTileClassified { suit, number } = t;
		// Using a `match` for every combination is safer but generates branches based on `suit`
		// that add constant 0x12 or 0x24 instead of the multiplication by 0x12 (via `lea` / `sh*add`), so we do it manually.
		//
		// SAFETY: Lines up with the explicit values given to the `Number` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute((suit as u8) * (tn!(1p) as u8 - tn!(1m) as u8) + (number as u8 - Number::One as u8) + tn!(1m) as u8) }
	}

	// TODO(rustup): Inline this into `From<ShunLowTile>` impl when `const impl From` is possible.
	pub(crate) const fn const_from_slt(t: ShunLowTile) -> Self {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `ShunLowTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from_and_try_from` test.
		unsafe { *<*const _>::cast(&raw const t) }
	}
}

impl AsRef<Tile> for NumberTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `NumberTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from_and_try_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

impl CmpIgnoreRed for NumberTile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 1).cmp(&((*other as u8) >> 1))
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

impl From<NumberTileClassified> for NumberTile {
	fn from(t: NumberTileClassified) -> Self {
		Self::const_from(t)
	}
}

impl From<ShunLowTile> for NumberTile {
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

impl SortingNetwork for NumberTile {
	fn sort_three(arr: &mut [Self; 3]) {
		let arr = unsafe { &mut *(<*mut [Self; 3]>::cast::<[u8; 3]>(arr)) };
		SortingNetwork::sort_three(arr);
	}
}

impl TryFrom<Tile> for NumberTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		if t >= t!(1m) && t <= t!(9s) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `NumberTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from`, `wind_tile_as_ref_and_from` and `wind_tile_as_ref_and_from` tests.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl ShunLowTile {
	pub const fn number(self) -> Number {
		let result = NumberTile::const_from_slt(self).number();
		// Helps eliminate bounds checks in callers that use this to index arrays.
		unsafe { core::hint::assert_unchecked(result as u8 <= Number::Seven as u8); }
		result
	}

	pub const fn suit(self) -> NumberSuit {
		NumberTile::const_from_slt(self).suit()
	}

	pub(crate) const fn shun_rest(self) -> (NumberTile, NumberTile) {
		let this = self as u8 & !0b1;
		let next = this + 2;
		let next = unsafe { core::mem::transmute::<u8, NumberTile>(next) };
		let next_next = this + 4;
		let next_next = unsafe { core::mem::transmute::<u8, NumberTile>(next_next) };
		(next, next_next)
	}

	pub(crate) const fn is_red(self) -> bool {
		Tile::const_from_slt(self).is_red()
	}

	#[must_use]
	pub(crate) const fn make_red(self) -> Self {
		if 0b000010000_000010000_000010000_u32 & (0b1 << (self as u8 >> 1)) != 0 {
			let result = (self as u8) | 0b1;
			unsafe { core::mem::transmute::<u8, Self>(result) }
		}
		else {
			self
		}
	}

	#[must_use]
	pub(crate) const fn remove_red(self) -> Self {
		let result = (self as u8) & !0b1;
		unsafe { core::mem::transmute::<u8, Self>(result) }
	}
}

impl AsRef<Tile> for ShunLowTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `ShunLowTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

impl AsRef<NumberTile> for ShunLowTile {
	fn as_ref(&self) -> &NumberTile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `ShunLowTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref_and_from` test.
		unsafe { &*<*const _>::cast(self) }
	}
}

impl CmpIgnoreRed for ShunLowTile {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 1).cmp(&((*other as u8) >> 1))
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

impl TryFrom<NumberTile> for ShunLowTile {
	type Error = ();

	fn try_from(t: NumberTile) -> Result<Self, Self::Error> {
		// Micro-optimization: Same trick as `Tile::is_simple`.
		//
		// Tested exhaustively in the `shun_rest` test.

		if 0b001111111_001111111_001111111_u32 & (1_u32 << (t as u8 >> 1)) != 0 {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `NumberTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from`, `wind_tile_as_ref_and_from` and `wind_tile_as_ref_and_from` tests.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl TryFrom<Tile> for ShunLowTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		// Micro-optimization: Same trick as `Tile::is_simple`.
		//
		// Tested exhaustively in the `shun_rest` test.

		if 0b0000000_001111111_001111111_001111111_u64 & (1_u64 << (t as u8 >> 1)) != 0 {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `NumberTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from`, `wind_tile_as_ref_and_from` and `wind_tile_as_ref_and_from` tests.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl AsRef<Tile> for WindTile {
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

impl TryFrom<Tile> for WindTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		if t >= t!(E) && t <= t!(N) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `WindTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from`, `wind_tile_as_ref_and_from` and `wind_tile_as_ref_and_from` tests.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl AsRef<Tile> for DragonTile {
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

impl TryFrom<Tile> for DragonTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		if t >= t!(Wh) && t <= t!(R) {
			// SAFETY: Lines up with the explicit values given to the `Tile` and `DragonTile` variants,
			// and tested exhaustively in the `number_tile_as_ref_and_from_and_try_from`, `wind_tile_as_ref_and_from` and `wind_tile_as_ref_and_from` tests.
			let t = unsafe { core::mem::transmute::<u8, Self>(t as u8) };
			Ok(t)
		}
		else {
			Err(())
		}
	}
}

impl core::fmt::Display for NumberTileClassified {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "{}{}", self.number, self.suit)
	}
}

impl From<NumberTile> for NumberTileClassified {
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
		f.write_str(match self {
			Self::Man => "m",
			Self::Pin => "p",
			Self::Sou => "s",
		})
	}
}

impl Number {
	pub const fn value(self) -> u8 {
		((self as u8) >> 1) + 1
	}
}

impl CmpIgnoreRed for Number {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		((*self as u8) >> 1).cmp(&((*other as u8) >> 1))
	}
}

impl core::fmt::Debug for Number {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for Number {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str(match self {
			Self::One => "1",
			Self::Two => "2",
			Self::Three => "3",
			Self::Four => "4",
			Self::Five => "5",
			Self::FiveRed => "0",
			Self::Six => "6",
			Self::Seven => "7",
			Self::Eight => "8",
			Self::Nine => "9",
		})
	}
}

impl<T> CmpIgnoreRed for Option<T> where T: CmpIgnoreRed {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		match (self, other) {
			(Some(this), Some(other)) => this.cmp_ignore_red(other),
			(Some(_), None) => core::cmp::Ordering::Greater,
			(None, Some(_)) => core::cmp::Ordering::Less,
			(None, None) => core::cmp::Ordering::Equal,
		}
	}
}

impl<T, U> CmpIgnoreRed for (T, U) where T: CmpIgnoreRed, U: CmpIgnoreRed {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		match self.0.cmp_ignore_red(&other.0) {
			core::cmp::Ordering::Equal => self.1.cmp_ignore_red(&other.1),
			result => result,
		}
	}
}

impl<T, U, V> CmpIgnoreRed for (T, U, V) where T: CmpIgnoreRed, U: CmpIgnoreRed, V: CmpIgnoreRed {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		match self.0.cmp_ignore_red(&other.0) {
			core::cmp::Ordering::Equal => match self.1.cmp_ignore_red(&other.1) {
				core::cmp::Ordering::Equal => self.2.cmp_ignore_red(&other.2),
				result => result,
			},
			result => result,
		}
	}
}

impl<T, U, V, W, X, Y, Z> CmpIgnoreRed for (T, U, V, W, X, Y, Z)
where
	T: CmpIgnoreRed,
	U: CmpIgnoreRed,
	V: CmpIgnoreRed,
	W: CmpIgnoreRed,
	X: CmpIgnoreRed,
	Y: CmpIgnoreRed,
	Z: CmpIgnoreRed,
{
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		match self.0.cmp_ignore_red(&other.0) {
			core::cmp::Ordering::Equal => match self.1.cmp_ignore_red(&other.1) {
				core::cmp::Ordering::Equal => match self.2.cmp_ignore_red(&other.2) {
					core::cmp::Ordering::Equal => match self.3.cmp_ignore_red(&other.3) {
						core::cmp::Ordering::Equal => match self.4.cmp_ignore_red(&other.4) {
							core::cmp::Ordering::Equal => match self.5.cmp_ignore_red(&other.5) {
								core::cmp::Ordering::Equal => self.6.cmp_ignore_red(&other.6),
								result => result,
							},
							result => result,
						},
						result => result,
					},
					result => result,
				},
				result => result,
			},
			result => result,
		}
	}
}

impl<T> CmpIgnoreRed for [T] where T: CmpIgnoreRed {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		// Match `[T]: PartialOrd` impl:
		// 1. Elements are compared until unequal elements are found or one slice ends.
		// 2. If all elements equal, result is the comparison of the slice lengths.
		let this_len = self.len();
		let other_len = other.len();
		let common_len = this_len.min(other_len);
		let (this, this_rest) = self.split_at(common_len);
		let (other, other_rest) = other.split_at(common_len);
		// This uses an indexed `while` loop instead of `for` so that it can be `const fn`
		let mut i = 0;
		while i < common_len {
			let this = &this[i];
			let other = &other[i];
			let result = this.cmp_ignore_red(other);
			if !matches!(result, core::cmp::Ordering::Equal) {
				return result;
			}
			i += 1;
		}
		this_rest.len().cmp(&other_rest.len())
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

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

	#[test]
	fn tile_is_simple() {
		assert!(!t!(1m).is_simple());
		assert!(t!(2m).is_simple());
		assert!(t!(3m).is_simple());
		assert!(t!(4m).is_simple());
		assert!(t!(5m).is_simple());
		assert!(t!(0m).is_simple());
		assert!(t!(6m).is_simple());
		assert!(t!(7m).is_simple());
		assert!(t!(8m).is_simple());
		assert!(!t!(9m).is_simple());
		assert!(!t!(1p).is_simple());
		assert!(t!(2p).is_simple());
		assert!(t!(3p).is_simple());
		assert!(t!(4p).is_simple());
		assert!(t!(5p).is_simple());
		assert!(t!(0p).is_simple());
		assert!(t!(6p).is_simple());
		assert!(t!(7p).is_simple());
		assert!(t!(8p).is_simple());
		assert!(!t!(9p).is_simple());
		assert!(!t!(1s).is_simple());
		assert!(t!(2s).is_simple());
		assert!(t!(3s).is_simple());
		assert!(t!(4s).is_simple());
		assert!(t!(5s).is_simple());
		assert!(t!(0s).is_simple());
		assert!(t!(6s).is_simple());
		assert!(t!(7s).is_simple());
		assert!(t!(8s).is_simple());
		assert!(!t!(9s).is_simple());
		assert!(!t!(E).is_simple());
		assert!(!t!(S).is_simple());
		assert!(!t!(W).is_simple());
		assert!(!t!(N).is_simple());
		assert!(!t!(Wh).is_simple());
		assert!(!t!(G).is_simple());
		assert!(!t!(R).is_simple());
	}

	#[test]
	fn tile_ord() {
		for a in Tile::each(GameType::Yonma).iter().copied().chain(t![0m, 0p, 0s]) {
			for b in Tile::each(GameType::Yonma).iter().copied().chain(t![0m, 0p, 0s]) {
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
	fn number_tile_previous_next_in_sequence() {
		assert_eq!(tn!(1m).previous_in_sequence(), None);
		assert_eq!(tn!(1m).next_in_sequence(), Some(tn!(2m)));
		assert_eq!(tn!(2m).previous_in_sequence(), Some(tn!(1m)));
		assert_eq!(tn!(2m).next_in_sequence(), Some(tn!(3m)));
		assert_eq!(tn!(3m).previous_in_sequence(), Some(tn!(2m)));
		assert_eq!(tn!(3m).next_in_sequence(), Some(tn!(4m)));
		assert_eq!(tn!(4m).previous_in_sequence(), Some(tn!(3m)));
		assert_eq!(tn!(4m).next_in_sequence(), Some(tn!(5m)));
		assert_eq!(tn!(5m).previous_in_sequence(), Some(tn!(4m)));
		assert_eq!(tn!(5m).next_in_sequence(), Some(tn!(6m)));
		assert_eq!(tn!(0m).previous_in_sequence(), Some(tn!(4m)));
		assert_eq!(tn!(0m).next_in_sequence(), Some(tn!(6m)));
		assert_eq!(tn!(6m).previous_in_sequence(), Some(tn!(5m)));
		assert_eq!(tn!(6m).next_in_sequence(), Some(tn!(7m)));
		assert_eq!(tn!(7m).previous_in_sequence(), Some(tn!(6m)));
		assert_eq!(tn!(7m).next_in_sequence(), Some(tn!(8m)));
		assert_eq!(tn!(8m).previous_in_sequence(), Some(tn!(7m)));
		assert_eq!(tn!(8m).next_in_sequence(), Some(tn!(9m)));
		assert_eq!(tn!(9m).previous_in_sequence(), Some(tn!(8m)));
		assert_eq!(tn!(9m).next_in_sequence(), None);

		assert_eq!(tn!(1p).previous_in_sequence(), None);
		assert_eq!(tn!(1p).next_in_sequence(), Some(tn!(2p)));
		assert_eq!(tn!(2p).previous_in_sequence(), Some(tn!(1p)));
		assert_eq!(tn!(2p).next_in_sequence(), Some(tn!(3p)));
		assert_eq!(tn!(3p).previous_in_sequence(), Some(tn!(2p)));
		assert_eq!(tn!(3p).next_in_sequence(), Some(tn!(4p)));
		assert_eq!(tn!(4p).previous_in_sequence(), Some(tn!(3p)));
		assert_eq!(tn!(4p).next_in_sequence(), Some(tn!(5p)));
		assert_eq!(tn!(5p).previous_in_sequence(), Some(tn!(4p)));
		assert_eq!(tn!(5p).next_in_sequence(), Some(tn!(6p)));
		assert_eq!(tn!(0p).previous_in_sequence(), Some(tn!(4p)));
		assert_eq!(tn!(0p).next_in_sequence(), Some(tn!(6p)));
		assert_eq!(tn!(6p).previous_in_sequence(), Some(tn!(5p)));
		assert_eq!(tn!(6p).next_in_sequence(), Some(tn!(7p)));
		assert_eq!(tn!(7p).previous_in_sequence(), Some(tn!(6p)));
		assert_eq!(tn!(7p).next_in_sequence(), Some(tn!(8p)));
		assert_eq!(tn!(8p).previous_in_sequence(), Some(tn!(7p)));
		assert_eq!(tn!(8p).next_in_sequence(), Some(tn!(9p)));
		assert_eq!(tn!(9p).previous_in_sequence(), Some(tn!(8p)));
		assert_eq!(tn!(9p).next_in_sequence(), None);

		assert_eq!(tn!(1s).previous_in_sequence(), None);
		assert_eq!(tn!(1s).next_in_sequence(), Some(tn!(2s)));
		assert_eq!(tn!(2s).previous_in_sequence(), Some(tn!(1s)));
		assert_eq!(tn!(2s).next_in_sequence(), Some(tn!(3s)));
		assert_eq!(tn!(3s).previous_in_sequence(), Some(tn!(2s)));
		assert_eq!(tn!(3s).next_in_sequence(), Some(tn!(4s)));
		assert_eq!(tn!(4s).previous_in_sequence(), Some(tn!(3s)));
		assert_eq!(tn!(4s).next_in_sequence(), Some(tn!(5s)));
		assert_eq!(tn!(5s).previous_in_sequence(), Some(tn!(4s)));
		assert_eq!(tn!(5s).next_in_sequence(), Some(tn!(6s)));
		assert_eq!(tn!(0s).previous_in_sequence(), Some(tn!(4s)));
		assert_eq!(tn!(0s).next_in_sequence(), Some(tn!(6s)));
		assert_eq!(tn!(6s).previous_in_sequence(), Some(tn!(5s)));
		assert_eq!(tn!(6s).next_in_sequence(), Some(tn!(7s)));
		assert_eq!(tn!(7s).previous_in_sequence(), Some(tn!(6s)));
		assert_eq!(tn!(7s).next_in_sequence(), Some(tn!(8s)));
		assert_eq!(tn!(8s).previous_in_sequence(), Some(tn!(7s)));
		assert_eq!(tn!(8s).next_in_sequence(), Some(tn!(9s)));
		assert_eq!(tn!(9s).previous_in_sequence(), Some(tn!(8s)));
		assert_eq!(tn!(9s).next_in_sequence(), None);
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
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::One }, tn!(1m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Two }, tn!(2m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Three }, tn!(3m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Four }, tn!(4m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Five }, tn!(5m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::FiveRed }, tn!(0m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Six }, tn!(6m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Seven }, tn!(7m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Eight }, tn!(8m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Nine }, tn!(9m)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::One }, tn!(1p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Two }, tn!(2p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Three }, tn!(3p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Four }, tn!(4p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Five }, tn!(5p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::FiveRed }, tn!(0p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Six }, tn!(6p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Seven }, tn!(7p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Eight }, tn!(8p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Nine }, tn!(9p)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::One }, tn!(1s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Two }, tn!(2s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Three }, tn!(3s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Four }, tn!(4s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Five }, tn!(5s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::FiveRed }, tn!(0s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Six }, tn!(6s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Seven }, tn!(7s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Eight }, tn!(8s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Nine }, tn!(9s)),
		] {
			let nt_actual: NumberTile = ntc.into();
			assert_eq!(nt_actual, nt);

			let ntc_actual: NumberTileClassified = nt.into();
			assert_eq!(ntc_actual.suit, ntc.suit);
			assert_eq!(ntc_actual.number, ntc.number);
		}
	}

	#[test]
	fn number_value() {
		assert_eq!(Number::One.value(), 1);
		assert_eq!(Number::Two.value(), 2);
		assert_eq!(Number::Three.value(), 3);
		assert_eq!(Number::Four.value(), 4);
		assert_eq!(Number::Five.value(), 5);
		assert_eq!(Number::FiveRed.value(), 5);
		assert_eq!(Number::Six.value(), 6);
		assert_eq!(Number::Seven.value(), 7);
		assert_eq!(Number::Eight.value(), 8);
		assert_eq!(Number::Nine.value(), 9);
	}

	#[test]
	fn number_ord() {
		const NUMBERS: [Number; 10] = [
			Number::One,
			Number::Two,
			Number::Three,
			Number::Four,
			Number::Five,
			Number::FiveRed,
			Number::Six,
			Number::Seven,
			Number::Eight,
			Number::Nine,
		];
		for a in NUMBERS {
			for b in NUMBERS {
				let expected = (a as u8).cmp(&(b as u8));
				let expected_ignore_red = match (a, b) {
					(Number::Five | Number::FiveRed, Number::Five | Number::FiveRed) => core::cmp::Ordering::Equal,
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
