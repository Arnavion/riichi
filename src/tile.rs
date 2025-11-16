use generic_array::typenum;

use crate::{
	ArrayVec,
	GameType,
	HandMeldType,
};

/// A tile.
#[derive(Clone, Copy, Eq)]
#[repr(u8)]
pub enum Tile {
	Man1 = 0,
	Man2 = 1,
	Man3 = 2,
	Man4 = 3,
	Man5 = 4,
	Man0 = 5,
	Man6 = 6,
	Man7 = 7,
	Man8 = 8,
	Man9 = 9,
	Pin1 = 10,
	Pin2 = 11,
	Pin3 = 12,
	Pin4 = 13,
	Pin5 = 14,
	Pin0 = 15,
	Pin6 = 16,
	Pin7 = 17,
	Pin8 = 18,
	Pin9 = 19,
	Sou1 = 20,
	Sou2 = 21,
	Sou3 = 22,
	Sou4 = 23,
	Sou5 = 24,
	Sou0 = 25,
	Sou6 = 26,
	Sou7 = 27,
	Sou8 = 28,
	Sou9 = 29,
	Ton = 30,
	Nan = 31,
	Shaa = 32,
	Pei = 33,
	Haku = 34,
	Hatsu = 35,
	Chun = 36,
}

/// A number tile.
#[derive(Clone, Copy, Eq)]
#[repr(u8)]
pub enum NumberTile {
	Man1 = 0,
	Man2 = 1,
	Man3 = 2,
	Man4 = 3,
	Man5 = 4,
	Man0 = 5,
	Man6 = 6,
	Man7 = 7,
	Man8 = 8,
	Man9 = 9,
	Pin1 = 10,
	Pin2 = 11,
	Pin3 = 12,
	Pin4 = 13,
	Pin5 = 14,
	Pin0 = 15,
	Pin6 = 16,
	Pin7 = 17,
	Pin8 = 18,
	Pin9 = 19,
	Sou1 = 20,
	Sou2 = 21,
	Sou3 = 22,
	Sou4 = 23,
	Sou5 = 24,
	Sou0 = 25,
	Sou6 = 26,
	Sou7 = 27,
	Sou8 = 28,
	Sou9 = 29,
}

/// A wind tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum WindTile {
	/// East
	Ton = 30,
	/// South
	Nan = 31,
	/// West
	Shaa = 32,
	/// North
	Pei = 33,
}

/// A dragon tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum DragonTile {
	/// White
	Haku = 34,
	/// Green
	Hatsu = 35,
	/// Red
	Chun = 36,
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
///
/// Note that the `PartialEq` impl considers `Five` to be equal to `FiveRed`.
#[derive(Clone, Copy, Eq)]
#[repr(u8)]
pub enum Number {
	One = 0,
	Two = 1,
	Three = 2,
	Four = 3,
	Five = 4,
	FiveRed = 5,
	Six = 6,
	Seven = 7,
	Eight = 8,
	Nine = 9,
}

assert_size_of!(Tile, 1);

assert_size_of!(NumberTile, 1);

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
	/// # Errors
	///
	/// Returns an error if the string does not have valid syntax.
	#[expect(clippy::result_unit_err)]
	pub fn parse_run(s: &str) -> Result<(ArrayVec<Self, typenum::U13>, Option<HandMeldType>), ()> {
		let mut result = ArrayVec::new();
		let mut result_type = None;

		let mut current_run = ArrayVec::<_, typenum::U13>::new();

		for b in s.as_bytes() {
			match b {
				b'1' => current_run.push(Number::One).map_err(|_| ())?,
				b'2' => current_run.push(Number::Two).map_err(|_| ())?,
				b'3' => current_run.push(Number::Three).map_err(|_| ())?,
				b'4' => current_run.push(Number::Four).map_err(|_| ())?,
				b'5' => current_run.push(Number::Five).map_err(|_| ())?,
				b'0' => current_run.push(Number::FiveRed).map_err(|_| ())?,
				b'6' => current_run.push(Number::Six).map_err(|_| ())?,
				b'7' => current_run.push(Number::Seven).map_err(|_| ())?,
				b'8' => current_run.push(Number::Eight).map_err(|_| ())?,
				b'9' => current_run.push(Number::Nine).map_err(|_| ())?,

				b'm' => {
					if current_run.is_empty() {
						return Err(());
					}

					result.extend(core::mem::take(&mut current_run).into_iter().map(|number| Tile::from(NumberTile::from(NumberTileClassified { suit: NumberSuit::Man, number }))));
				},

				b'p' => {
					if current_run.is_empty() {
						return Err(());
					}

					result.extend(core::mem::take(&mut current_run).into_iter().map(|number| Tile::from(NumberTile::from(NumberTileClassified { suit: NumberSuit::Pin, number }))));
				},

				b's' => {
					if current_run.is_empty() {
						return Err(());
					}

					result.extend(core::mem::take(&mut current_run).into_iter().map(|number| Tile::from(NumberTile::from(NumberTileClassified { suit: NumberSuit::Sou, number }))));
				},

				b'z' => {
					if current_run.is_empty() {
						return Err(());
					}

					for number in core::mem::take(&mut current_run) {
						result.push(match number {
							Number::One => Tile::Ton,
							Number::Two => Tile::Nan,
							Number::Three => Tile::Shaa,
							Number::Four => Tile::Pei,
							Number::Five => Tile::Haku,
							Number::Six => Tile::Hatsu,
							Number::Seven => Tile::Chun,
							_ => return Err(()),
						}).map_err(|_| ())?;
					}
				},

				b'+' => if result_type.replace(HandMeldType::Ankan).is_some() {
					return Err(());
				},

				b'=' => if result_type.replace(HandMeldType::Shouminkan).is_some() {
					return Err(());
				},

				b'-' => if result_type.replace(HandMeldType::MinjunMinkouDaiminkan).is_some() {
					return Err(());
				},

				_ => return Err(()),
			}
		}

		if !current_run.is_empty() {
			return Err(());
		}

		Ok((result, result_type))
	}

	/// Returns the tile that would be a dora tile if this tile was revealed in the dead wall.
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
	///
	/// # Panics
	///
	/// Panics if `self` is not a valid tile for `game_type`.
	pub fn indicates_dora(self, game_type: GameType) -> Self {
		const DORAS: [(Tile, Option<Tile>); 37] = [
			(t!(2m), Some(t!(9m))),
			(t!(3m), None),
			(t!(4m), None),
			(t!(5m), None),
			(t!(6m), None),
			(t!(6m), None),
			(t!(7m), None),
			(t!(8m), None),
			(t!(9m), None),
			(t!(1m), Some(t!(1m))),
			(t!(2p), Some(t!(2p))),
			(t!(3p), Some(t!(3p))),
			(t!(4p), Some(t!(4p))),
			(t!(5p), Some(t!(5p))),
			(t!(6p), Some(t!(6p))),
			(t!(6p), Some(t!(6p))),
			(t!(7p), Some(t!(7p))),
			(t!(8p), Some(t!(8p))),
			(t!(9p), Some(t!(9p))),
			(t!(1p), Some(t!(1p))),
			(t!(2s), Some(t!(2s))),
			(t!(3s), Some(t!(3s))),
			(t!(4s), Some(t!(4s))),
			(t!(5s), Some(t!(5s))),
			(t!(6s), Some(t!(6s))),
			(t!(6s), Some(t!(6s))),
			(t!(7s), Some(t!(7s))),
			(t!(8s), Some(t!(8s))),
			(t!(9s), Some(t!(9s))),
			(t!(1s), Some(t!(1s))),
			(t!(S), Some(t!(S))),
			(t!(W), Some(t!(W))),
			(t!(N), Some(t!(N))),
			(t!(E), Some(t!(E))),
			(t!(G), Some(t!(G))),
			(t!(R), Some(t!(R))),
			(t!(Wh), Some(t!(Wh))),
		];

		let (yonma, sanma) = DORAS[self as usize];
		match game_type {
			GameType::Yonma => yonma,
			GameType::Sanma => match sanma {
				Some(t) => t,
				None => unreachable!("{self} does not exist in sanma"),
			},
		}
	}

	pub(crate) const fn is_simple(self) -> bool {
		match self {
			t!(
				2m | 3m | 4m | 5m | 0m | 6m | 7m | 8m |
				2p | 3p | 4p | 5p | 0p | 6p | 7p | 8p |
				2s | 3s | 4s | 5s | 0s | 6s | 7s | 8s
			) => true,
			t!(1m | 9m | 1p | 9p | 1s | 9s | E | S | W | N | Wh | G | R) => false,
		}
	}

	// TODO(rustup): Inline this into `From<NumberTile>` impl when `const impl From` is possible.
	pub(crate) const fn const_from(t: NumberTile) -> Self {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `NumberTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref` test.
		unsafe { *<*const _>::cast(&raw const t) }
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
		Ok(match s {
			"1m" => Self::Man1,
			"2m" => Self::Man2,
			"3m" => Self::Man3,
			"4m" => Self::Man4,
			"5m" => Self::Man5,
			"0m" => Self::Man0,
			"6m" => Self::Man6,
			"7m" => Self::Man7,
			"8m" => Self::Man8,
			"9m" => Self::Man9,

			"1p" => Self::Pin1,
			"2p" => Self::Pin2,
			"3p" => Self::Pin3,
			"4p" => Self::Pin4,
			"5p" => Self::Pin5,
			"0p" => Self::Pin0,
			"6p" => Self::Pin6,
			"7p" => Self::Pin7,
			"8p" => Self::Pin8,
			"9p" => Self::Pin9,

			"1s" => Self::Sou1,
			"2s" => Self::Sou2,
			"3s" => Self::Sou3,
			"4s" => Self::Sou4,
			"5s" => Self::Sou5,
			"0s" => Self::Sou0,
			"6s" => Self::Sou6,
			"7s" => Self::Sou7,
			"8s" => Self::Sou8,
			"9s" => Self::Sou9,

			"E" |
			"1z" => Self::Ton,
			"S" |
			"2z" => Self::Nan,
			"W" |
			"3z" => Self::Shaa,
			"N" |
			"4z" => Self::Pei,

			"Wh" |
			"5z" => Self::Haku,
			"G" |
			"6z" => Self::Hatsu,
			"R" |
			"7z" => Self::Chun,

			_ => return Err(()),
		})
	}
}

impl Ord for Tile {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		// Micro-optimization: Doing it this way generates good branchless code with low dependencies. Tested exhaustively in the `tile_ord` test.
		//
		// Using usize instead of u8 makes a difference. LLVM doesn't understand that `x + x_diff` does not overflow, even if this uses `.unchecked_add`,
		// and inserts instructions to clamp the sum to u8 (`zext.b` etc).
		//
		// Adding `< t!(0x)` instead of subtracting `>= t!(0x)` is better for RV since the latter requires extra instructions to invert the result of each `sltiu`.
		let this = *self as usize;
		let other = *other as usize;
		let this_diff = usize::from(this < t!(0m) as usize) + usize::from(this < t!(0p) as usize) + usize::from(this < t!(0s) as usize);
		let other_diff = usize::from(other < t!(0m) as usize) + usize::from(other < t!(0p) as usize) + usize::from(other < t!(0s) as usize);
		(this + this_diff).cmp(&(other + other_diff))
	}
}

impl PartialEq for Tile {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

impl PartialOrd for Tile {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
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
		// SAFETY: Lines up with the explicit values given to the `NumberTile` and `Number` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute::<u8, Number>((self as u8) % 10) }
	}

	pub const fn suit(self) -> NumberSuit {
		// SAFETY: Lines up with the explicit values given to the `NumberTile` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute::<u8, NumberSuit>((self as u8) / 10) }
	}

	pub(crate) fn shun_rest(self) -> Option<(Self, Self)> {
		let NumberTileClassified { suit, number } = self.into();
		let (number2, number3) = number.shun_rest()?;
		Some((
			(NumberTileClassified { suit, number: number2 }).into(),
			(NumberTileClassified { suit, number: number3 }).into(),
		))
	}

	pub(crate) fn previous_in_sequence(self) -> Option<Self> {
		let number = self.number().previous_in_sequence()?;
		Some((NumberTileClassified { suit: self.suit(), number }).into())
	}

	pub(crate) fn next_in_sequence(self) -> Option<Self> {
		let number = self.number().next_in_sequence()?;
		Some((NumberTileClassified { suit: self.suit(), number }).into())
	}

	pub(crate) fn is_next_in_sequence(self, previous: Self) -> bool {
		self.suit() == previous.suit() && Some(self.number()) == previous.number().next_in_sequence()
	}

	// TODO(rustup): Inline this into `From<NumberTileClassified>` impl when `const impl From` is possible.
	pub(crate) const fn const_from(t: NumberTileClassified) -> Self {
		let NumberTileClassified { suit, number } = t;
		// Using a `match` for every combination is safer but generates branches based on `suit`
		// that add constant 10 or 20 instead of the multiplication by 10 (via `lea` / `sh*add`), so we do it manually.
		//
		// SAFETY: Lines up with the explicit values given to the `Number` and `NumberSuit` variants,
		// and tested exhaustively in the `number_tile_convert_classified` test.
		unsafe { core::mem::transmute((suit as u8) * 10 + (number as u8)) }
	}
}

impl AsRef<Tile> for NumberTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `NumberTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `number_tile_as_ref` test.
		unsafe { &*<*const _>::cast(self) }
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

impl core::str::FromStr for NumberTile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let t: Tile = s.parse()?;
		t.try_into()
	}
}

impl Ord for NumberTile {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		AsRef::<Tile>::as_ref(self).cmp(AsRef::<Tile>::as_ref(other))
	}
}

impl PartialEq for NumberTile {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

impl PartialOrd for NumberTile {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl TryFrom<Tile> for NumberTile {
	type Error = ();

	fn try_from(t: Tile) -> Result<Self, Self::Error> {
		Ok(match t {
			t!(1m) => tn!(1m),
			t!(2m) => tn!(2m),
			t!(3m) => tn!(3m),
			t!(4m) => tn!(4m),
			t!(5m) => tn!(5m),
			t!(0m) => tn!(0m),
			t!(6m) => tn!(6m),
			t!(7m) => tn!(7m),
			t!(8m) => tn!(8m),
			t!(9m) => tn!(9m),
			t!(1p) => tn!(1p),
			t!(2p) => tn!(2p),
			t!(3p) => tn!(3p),
			t!(4p) => tn!(4p),
			t!(5p) => tn!(5p),
			t!(0p) => tn!(0p),
			t!(6p) => tn!(6p),
			t!(7p) => tn!(7p),
			t!(8p) => tn!(8p),
			t!(9p) => tn!(9p),
			t!(1s) => tn!(1s),
			t!(2s) => tn!(2s),
			t!(3s) => tn!(3s),
			t!(4s) => tn!(4s),
			t!(5s) => tn!(5s),
			t!(0s) => tn!(0s),
			t!(6s) => tn!(6s),
			t!(7s) => tn!(7s),
			t!(8s) => tn!(8s),
			t!(9s) => tn!(9s),
			_ => return Err(()),
		})
	}
}

impl AsRef<Tile> for WindTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `WindTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `wind_tile_as_ref` test.
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
		Ok(match t {
			t!(E) => tw!(E),
			t!(S) => tw!(S),
			t!(W) => tw!(W),
			t!(N) => tw!(N),
			_ => return Err(()),
		})
	}
}

impl AsRef<Tile> for DragonTile {
	fn as_ref(&self) -> &Tile {
		// SAFETY: Both are repr(u8) and thus have the same size and alignment, and every bit pattern of `DragonTile` is valid for `Tile`.
		//
		// Tested exhaustively in the `dragon_tile_as_ref` test.
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
		Ok(match t {
			t!(Wh) => td!(Wh),
			t!(G) => td!(G),
			t!(R) => td!(R),
			_ => return Err(()),
		})
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
		let this = self as u8;
		this + ((this < 5) as u8)
	}

	const fn shun_rest(self) -> Option<(Self, Self)> {
		// self            : 1 2 3 4 5 0 6 7 8 9
		// self as u8      : 0 1 2 3 4 5 6 7 8 9
		// next as u8      : 1 2 3 4 6 6 7 8 X X
		// next            : 2 3 4 5 6 6 7 8 X X
		// next_next as u8 : 2 3 4 6 7 7 8 9 X X
		// next_next       : 3 4 5 6 7 7 8 9 X X

		// Micro-optimization: Using a `match` instead generates a LUT. Tested exhaustively in the `number_shun_rest` test.
		let n = self as u8;
		let next = n + 1 + ((n == 4) as u8);
		let next_next = next + 1 + ((n == 3) as u8);

		// TODO: rustc generates an additional `zext.b` etc to truncate `next` to u8, and no amount of `assert_unchecked()`s seem to be able to
		// convince it that that is unnecessary.

		if next_next <= 9 {
			let next = unsafe { core::mem::transmute::<u8, Self>(next) };
			let next_next = unsafe { core::mem::transmute::<u8, Self>(next_next) };
			Some((next, next_next))
		}
		else {
			None
		}
	}

	pub(crate) const fn previous_in_sequence(self) -> Option<Self> {
		// self         : 1 2 3 4 5 0 6 7 8 9
		// self as u8   : 0 1 2 3 4 5 6 7 8 9
		// result as u8 : X 0 1 2 3 3 4 6 7 8
		// result       : X 1 2 3 4 4 5 6 7 8

		// Micro-optimization: Using a `match` instead generates a LUT. Tested exhaustively in the `number_previous_next_in_sequence` test.
		//
		// This does the arithmetic in `usize` instead of `u8`, otherwise rustc emits additional instructions (`zext.b` etc) to clamp the overflowd result to `u8`,
		// even though it will eventually clamp it to 10 (`None`).
		let n = self as usize;
		let n = (n - ((n == 5 || n == 6) as usize)).wrapping_sub(1);

		if n <= 9 {
			#[expect(clippy::cast_possible_truncation)]
			let n = n as u8;
			Some(unsafe { core::mem::transmute::<u8, Self>(n) })
		}
		else {
			None
		}
	}

	pub(crate) const fn next_in_sequence(self) -> Option<Self> {
		// self         : 1 2 3 4 5 0 6 7 8 9
		// self as u8   : 0 1 2 3 4 5 6 7 8 9
		// result as u8 : 1 2 3 4 6 6 7 8 9 X
		// result       : 2 3 4 5 6 6 7 8 9 X

		// Micro-optimization: Using a `match` instead generates a LUT. Tested exhaustively in the `number_previous_next_in_sequence` test.
		let n = self as u8;
		let n = n + 1 + ((n == 4) as u8);

		// Without this hint, rustc generates additional code to truncate the sum to u8 and then clamp it to 10 (`None`).
		// But as the comments above this show, in the case where the result should be mapped to `None` n is already 10, so those instructions are unnecessary.
		// This hint convinces rustc to not emit them.
		//
		// Of course the fact that rustc uses 10 to represent `None` is an internal detail so there is no forward guarantee that this assert will
		// result in that optimization forever. But at the very least it will always be true and not cause UB.
		//
		// TODO(rustup): Annotating `fn value()`'s return type as `core::pat::pattern_type!(u8 is 1..9)` might remove the need for this, if that ever gets stabilized.
		unsafe { core::hint::assert_unchecked(n <= 10); }

		if n <= 9 {
			Some(unsafe { core::mem::transmute::<u8, Self>(n) })
		}
		else {
			None
		}
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

/// Note that `Five` is considered to be equal to `FiveRed`.
impl Ord for Number {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		self.value().cmp(&other.value())
	}
}

/// Note that `Five` is considered to be equal to `FiveRed`.
impl PartialEq for Number {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

/// Note that `Five` is considered to be equal to `FiveRed`.
impl PartialOrd for Number {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn tile_ord() {
		for &a in Tile::each(GameType::Yonma) {
			for &b in Tile::each(GameType::Yonma) {
				let expected = match (a, b) {
					(t!(5m | 0m), t!(5m | 0m)) |
					(t!(5p | 0p), t!(5p | 0p)) |
					(t!(5s | 0s), t!(5s | 0s)) => core::cmp::Ordering::Equal,
					(a, b) => (a as u8).cmp(&(b as u8)),
				};
				let actual = a.cmp(&b);
				assert_eq!(actual, expected);
			}
		}
	}

	#[test]
	fn number_tile_as_ref() {
		for (input, expected) in &[
			(tn!(1m), t!(1m)),
			(tn!(2m), t!(2m)),
			(tn!(3m), t!(3m)),
			(tn!(4m), t!(4m)),
			(tn!(6m), t!(6m)),
			(tn!(7m), t!(7m)),
			(tn!(8m), t!(8m)),
			(tn!(9m), t!(9m)),
			(tn!(1p), t!(1p)),
			(tn!(2p), t!(2p)),
			(tn!(3p), t!(3p)),
			(tn!(4p), t!(4p)),
			(tn!(6p), t!(6p)),
			(tn!(7p), t!(7p)),
			(tn!(8p), t!(8p)),
			(tn!(9p), t!(9p)),
			(tn!(1s), t!(1s)),
			(tn!(2s), t!(2s)),
			(tn!(3s), t!(3s)),
			(tn!(4s), t!(4s)),
			(tn!(6s), t!(6s)),
			(tn!(7s), t!(7s)),
			(tn!(8s), t!(8s)),
			(tn!(9s), t!(9s)),
		] {
			let actual: &Tile = input.as_ref();
			assert_eq!(actual, expected);
		}

		assert!(matches!(tn!(5m).as_ref(), &t!(5m)));
		assert!(matches!(tn!(0m).as_ref(), &t!(0m)));
		assert!(matches!(tn!(5p).as_ref(), &t!(5p)));
		assert!(matches!(tn!(0p).as_ref(), &t!(0p)));
		assert!(matches!(tn!(5s).as_ref(), &t!(5s)));
		assert!(matches!(tn!(0s).as_ref(), &t!(0s)));
	}

	#[test]
	fn number_tile_convert_classified() {
		for (ntc, nt) in [
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::One }, tn!(1m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Two }, tn!(2m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Three }, tn!(3m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Four }, tn!(4m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Six }, tn!(6m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Seven }, tn!(7m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Eight }, tn!(8m)),
			(NumberTileClassified { suit: NumberSuit::Man, number: Number::Nine }, tn!(9m)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::One }, tn!(1p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Two }, tn!(2p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Three }, tn!(3p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Four }, tn!(4p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Six }, tn!(6p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Seven }, tn!(7p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Eight }, tn!(8p)),
			(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Nine }, tn!(9p)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::One }, tn!(1s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Two }, tn!(2s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Three }, tn!(3s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Four }, tn!(4s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Six }, tn!(6s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Seven }, tn!(7s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Eight }, tn!(8s)),
			(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Nine }, tn!(9s)),
		] {
			let nt_actual: NumberTile = ntc.into();
			assert_eq!(nt_actual, nt);

			let ntc_actual: NumberTileClassified = nt.into();
			assert_eq!(ntc_actual, ntc);
		}

		assert!(matches!(NumberTile::from(NumberTileClassified { suit: NumberSuit::Man, number: Number::Five }), tn!(5m)));
		assert!(matches!(NumberTileClassified::from(tn!(5m)), NumberTileClassified { suit: NumberSuit::Man, number: Number::Five }));
		assert!(matches!(NumberTile::from(NumberTileClassified { suit: NumberSuit::Man, number: Number::FiveRed }), tn!(0m)));
		assert!(matches!(NumberTileClassified::from(tn!(0m)), NumberTileClassified { suit: NumberSuit::Man, number: Number::FiveRed }));
		assert!(matches!(NumberTile::from(NumberTileClassified { suit: NumberSuit::Pin, number: Number::Five }), tn!(5p)));
		assert!(matches!(NumberTileClassified::from(tn!(5p)), NumberTileClassified { suit: NumberSuit::Pin, number: Number::Five }));
		assert!(matches!(NumberTile::from(NumberTileClassified { suit: NumberSuit::Pin, number: Number::FiveRed }), tn!(0p)));
		assert!(matches!(NumberTileClassified::from(tn!(0p)), NumberTileClassified { suit: NumberSuit::Pin, number: Number::FiveRed }));
		assert!(matches!(NumberTile::from(NumberTileClassified { suit: NumberSuit::Sou, number: Number::Five }), tn!(5s)));
		assert!(matches!(NumberTileClassified::from(tn!(5s)), NumberTileClassified { suit: NumberSuit::Sou, number: Number::Five }));
		assert!(matches!(NumberTile::from(NumberTileClassified { suit: NumberSuit::Sou, number: Number::FiveRed }), tn!(0s)));
		assert!(matches!(NumberTileClassified::from(tn!(0s)), NumberTileClassified { suit: NumberSuit::Sou, number: Number::FiveRed }));
	}

	#[test]
	fn number_previous_next_in_sequence() {
		assert!(Number::One.previous_in_sequence().is_none());
		assert!(matches!(Number::One.next_in_sequence(), Some(Number::Two)));
		assert!(matches!(Number::Two.previous_in_sequence(), Some(Number::One)));
		assert!(matches!(Number::Two.next_in_sequence(), Some(Number::Three)));
		assert!(matches!(Number::Three.previous_in_sequence(), Some(Number::Two)));
		assert!(matches!(Number::Three.next_in_sequence(), Some(Number::Four)));
		assert!(matches!(Number::Four.previous_in_sequence(), Some(Number::Three)));
		assert!(matches!(Number::Four.next_in_sequence(), Some(Number::Five)));
		assert!(matches!(Number::Five.previous_in_sequence(), Some(Number::Four)));
		assert!(matches!(Number::Five.next_in_sequence(), Some(Number::Six)));
		assert!(matches!(Number::FiveRed.previous_in_sequence(), Some(Number::Four)));
		assert!(matches!(Number::FiveRed.next_in_sequence(), Some(Number::Six)));
		assert!(matches!(Number::Six.previous_in_sequence(), Some(Number::Five)));
		assert!(matches!(Number::Six.next_in_sequence(), Some(Number::Seven)));
		assert!(matches!(Number::Seven.previous_in_sequence(), Some(Number::Six)));
		assert!(matches!(Number::Seven.next_in_sequence(), Some(Number::Eight)));
		assert!(matches!(Number::Eight.previous_in_sequence(), Some(Number::Seven)));
		assert!(matches!(Number::Eight.next_in_sequence(), Some(Number::Nine)));
		assert!(matches!(Number::Nine.previous_in_sequence(), Some(Number::Eight)));
		assert!(Number::Nine.next_in_sequence().is_none());
	}

	#[test]
	fn number_shun_rest() {
		assert!(matches!(Number::One.shun_rest(), Some((Number::Two, Number::Three))));
		assert!(matches!(Number::Two.shun_rest(), Some((Number::Three, Number::Four))));
		assert!(matches!(Number::Three.shun_rest(), Some((Number::Four, Number::Five))));
		assert!(matches!(Number::Four.shun_rest(), Some((Number::Five, Number::Six))));
		assert!(matches!(Number::Five.shun_rest(), Some((Number::Six, Number::Seven))));
		assert!(matches!(Number::FiveRed.shun_rest(), Some((Number::Six, Number::Seven))));
		assert!(matches!(Number::Six.shun_rest(), Some((Number::Seven, Number::Eight))));
		assert!(matches!(Number::Seven.shun_rest(), Some((Number::Eight, Number::Nine))));
		assert!(Number::Eight.shun_rest().is_none());
		assert!(Number::Nine.shun_rest().is_none());
	}

	#[test]
	fn wind_tile_as_ref() {
		for (input, expected) in &[
			(tw!(E), t!(E)),
			(tw!(S), t!(S)),
			(tw!(W), t!(W)),
			(tw!(N), t!(N)),
		] {
			let actual: &Tile = input.as_ref();
			assert_eq!(actual, expected);
		}
	}

	#[test]
	fn dragon_tile_as_ref() {
		for (input, expected) in &[
			(td!(Wh), t!(Wh)),
			(td!(G), t!(G)),
			(td!(R), t!(R)),
		] {
			let actual: &Tile = input.as_ref();
			assert_eq!(actual, expected);
		}
	}
}
