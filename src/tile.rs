use crate::{
	GameType,
	HandMeldType,
};

/// A tile.
#[derive(Clone, Copy, Eq)]
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
pub enum DragonTile {
	/// White
	Haku = 34,
	/// Green
	Hatsu = 35,
	/// Red
	Chun = 36,
}

/// A tile broken down into its category.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TileClassified {
	Number(NumberTile),
	Wind(WindTile),
	Dragon(DragonTile),
}

/// A number tile broken down into its suit and number.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NumberTileClassified {
	pub suit: NumberSuit,
	pub number: Number,
}

/// The suit of a number tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum NumberSuit {
	/// Characters
	Man,
	/// Wheels
	Pin,
	/// Bamboo
	Sou,
}

/// The value of a number tile.
///
/// Note that the `PartialEq` impl considers `Five` to be equal to `FiveRed`.
#[derive(Clone, Copy, Eq)]
pub enum Number {
	One,
	Two,
	Three,
	Four,
	Five,
	FiveRed,
	Six,
	Seven,
	Eight,
	Nine,
}

assert_size_of!(Tile, 1);

assert_size_of!(NumberTile, 1);

impl Tile {
	/// Returns one of each type of `Tile` in a game of the given type.
	pub const fn each(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::FourPlayer => &t![
				1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
				E, S, W, N,
				Wh, G, R,
			],

			GameType::ThreePlayer => &t![
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
			GameType::FourPlayer => &t![
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

			GameType::ThreePlayer => &t![
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
	pub fn parse_run(s: &str) -> Result<(Vec<Self>, Option<HandMeldType>), ()> {
		let mut result = vec![];
		let mut result_type = None;

		let mut current_run = vec![];

		for b in s.as_bytes() {
			match b {
				b'1' => current_run.push(Number::One),
				b'2' => current_run.push(Number::Two),
				b'3' => current_run.push(Number::Three),
				b'4' => current_run.push(Number::Four),
				b'5' => current_run.push(Number::Five),
				b'0' => current_run.push(Number::FiveRed),
				b'6' => current_run.push(Number::Six),
				b'7' => current_run.push(Number::Seven),
				b'8' => current_run.push(Number::Eight),
				b'9' => current_run.push(Number::Nine),

				b'm' => {
					if current_run.is_empty() {
						return Err(());
					}

					result.extend(current_run.drain(..).map(|number| Tile::from(NumberTile::from(NumberTileClassified { suit: NumberSuit::Man, number }))));
				},

				b'p' => {
					if current_run.is_empty() {
						return Err(());
					}

					result.extend(current_run.drain(..).map(|number| Tile::from(NumberTile::from(NumberTileClassified { suit: NumberSuit::Pin, number }))));
				},

				b's' => {
					if current_run.is_empty() {
						return Err(());
					}

					result.extend(current_run.drain(..).map(|number| Tile::from(NumberTile::from(NumberTileClassified { suit: NumberSuit::Sou, number }))));
				},

				b'z' => {
					if current_run.is_empty() {
						return Err(());
					}

					for number in current_run.drain(..) {
						result.push(match number {
							Number::One => Tile::Ton,
							Number::Two => Tile::Nan,
							Number::Three => Tile::Shaa,
							Number::Four => Tile::Pei,
							Number::Five => Tile::Haku,
							Number::Six => Tile::Hatsu,
							Number::Seven => Tile::Chun,
							_ => return Err(()),
						});
					}
				},

				b'-' => if result_type.replace(HandMeldType::MinjunMinkouDaiminkan).is_some() {
					return Err(());
				},

				b'=' => if result_type.replace(HandMeldType::Shouminkan).is_some() {
					return Err(());
				},

				b'+' => if result_type.replace(HandMeldType::Ankan).is_some() {
					return Err(());
				},

				b' ' => {
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
	/// assert_eq!(t!(2m).indicates_dora(GameType::FourPlayer), t!(3m));
	/// assert_eq!(t!(1m).indicates_dora(GameType::ThreePlayer), t!(9m));
	/// ```
	///
	/// # Panics
	///
	/// Panics if `self` is not a valid tile for `game_type`.
	pub const fn indicates_dora(self, game_type: GameType) -> Self {
		// Having a top-level `match game_type` is wasteful in code because it needs all the arms except 1m to be repeated,
		// but generates a compact LUT for each. A top-level `match self` with the `match game_type` only for 1m ends up generating a large
		// jump table instead.
		match game_type {
			GameType::FourPlayer => match self {
				t!(1m) => t!(2m),
				t!(2m) => t!(3m),
				t!(3m) => t!(4m),
				t!(4m) => t!(5m),
				t!(5m | 0m) => t!(6m),
				t!(6m) => t!(7m),
				t!(7m) => t!(8m),
				t!(8m) => t!(9m),
				t!(9m) => t!(1m),
				t!(1p) => t!(2p),
				t!(2p) => t!(3p),
				t!(3p) => t!(4p),
				t!(4p) => t!(5p),
				t!(5p | 0p) => t!(6p),
				t!(6p) => t!(7p),
				t!(7p) => t!(8p),
				t!(8p) => t!(9p),
				t!(9p) => t!(1p),
				t!(1s) => t!(2s),
				t!(2s) => t!(3s),
				t!(3s) => t!(4s),
				t!(4s) => t!(5s),
				t!(5s | 0s) => t!(6s),
				t!(6s) => t!(7s),
				t!(7s) => t!(8s),
				t!(8s) => t!(9s),
				t!(9s) => t!(1s),
				t!(E) => t!(S),
				t!(S) => t!(W),
				t!(W) => t!(N),
				t!(N) => t!(E),
				t!(Wh) => t!(G),
				t!(G) => t!(R),
				t!(R) => t!(Wh),
			},

			GameType::ThreePlayer => match self {
				t!(1m) => t!(9m),
				t!(9m) => t!(1m),
				t!(1p) => t!(2p),
				t!(2p) => t!(3p),
				t!(3p) => t!(4p),
				t!(4p) => t!(5p),
				t!(5p | 0p) => t!(6p),
				t!(6p) => t!(7p),
				t!(7p) => t!(8p),
				t!(8p) => t!(9p),
				t!(9p) => t!(1p),
				t!(1s) => t!(2s),
				t!(2s) => t!(3s),
				t!(3s) => t!(4s),
				t!(4s) => t!(5s),
				t!(5s | 0s) => t!(6s),
				t!(6s) => t!(7s),
				t!(7s) => t!(8s),
				t!(8s) => t!(9s),
				t!(9s) => t!(1s),
				t!(E) => t!(S),
				t!(S) => t!(W),
				t!(W) => t!(N),
				t!(N) => t!(E),
				t!(Wh) => t!(G),
				t!(G) => t!(R),
				t!(R) => t!(Wh),
				_ => unreachable!(),
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
}

impl std::fmt::Debug for Tile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for Tile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match (*self).into() {
			TileClassified::Number(tile) => tile.fmt(f),
			TileClassified::Wind(tile) => tile.fmt(f),
			TileClassified::Dragon(tile) => tile.fmt(f),
		}
	}
}

impl From<NumberTile> for Tile {
	fn from(t: NumberTile) -> Self {
		match t {
			tn!(1m) => t!(1m),
			tn!(2m) => t!(2m),
			tn!(3m) => t!(3m),
			tn!(4m) => t!(4m),
			tn!(5m) => t!(5m),
			tn!(0m) => t!(0m),
			tn!(6m) => t!(6m),
			tn!(7m) => t!(7m),
			tn!(8m) => t!(8m),
			tn!(9m) => t!(9m),
			tn!(1p) => t!(1p),
			tn!(2p) => t!(2p),
			tn!(3p) => t!(3p),
			tn!(4p) => t!(4p),
			tn!(5p) => t!(5p),
			tn!(0p) => t!(0p),
			tn!(6p) => t!(6p),
			tn!(7p) => t!(7p),
			tn!(8p) => t!(8p),
			tn!(9p) => t!(9p),
			tn!(1s) => t!(1s),
			tn!(2s) => t!(2s),
			tn!(3s) => t!(3s),
			tn!(4s) => t!(4s),
			tn!(5s) => t!(5s),
			tn!(0s) => t!(0s),
			tn!(6s) => t!(6s),
			tn!(7s) => t!(7s),
			tn!(8s) => t!(8s),
			tn!(9s) => t!(9s),
		}
	}
}

impl From<WindTile> for Tile {
	fn from(t: WindTile) -> Self {
		match t {
			tw!(E) => t!(E),
			tw!(S) => t!(S),
			tw!(W) => t!(W),
			tw!(N) => t!(N),
		}
	}
}

impl From<DragonTile> for Tile {
	fn from(t: DragonTile) -> Self {
		match t {
			td!(Wh) => t!(Wh),
			td!(G) => t!(G),
			td!(R) => t!(R),
		}
	}
}

impl std::str::FromStr for Tile {
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
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		#[expect(clippy::match_same_arms)]
		match ((*self).into(), (*other).into()) {
			(TileClassified::Number(this), TileClassified::Number(other)) => this.cmp(&other),
			(TileClassified::Number(_), TileClassified::Wind(_) | TileClassified::Dragon(_)) => std::cmp::Ordering::Less,

			(TileClassified::Wind(_), TileClassified::Number(_)) => std::cmp::Ordering::Greater,
			(TileClassified::Wind(this), TileClassified::Wind(other)) => this.cmp(&other),
			(TileClassified::Wind(_), TileClassified::Dragon(_)) => std::cmp::Ordering::Less,

			(TileClassified::Dragon(_), TileClassified::Number(_) | TileClassified::Wind(_)) => std::cmp::Ordering::Greater,
			(TileClassified::Dragon(this), TileClassified::Dragon(other)) => this.cmp(&other),
		}
	}
}

impl PartialEq for Tile {
	fn eq(&self, other: &Self) -> bool {
		match ((*self).into(), (*other).into()) {
			(TileClassified::Number(this), TileClassified::Number(other)) => this == other,
			(TileClassified::Wind(this), TileClassified::Wind(other)) => this == other,
			(TileClassified::Dragon(this), TileClassified::Dragon(other)) => this == other,
			_ => false,
		}
	}
}

impl PartialOrd for Tile {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl NumberTile {
	/// Returns one of each type of `NumberTile` in a game of the given type.
	pub const fn each(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::FourPlayer => &tn![
				1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
			],

			GameType::ThreePlayer => &tn![
				1m, 9m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
			],
		}
	}

	/// Returns all `NumberTile`s in a game of the given type.
	pub const fn all(game_type: GameType) -> &'static [Self] {
		match game_type {
			GameType::FourPlayer => &tn![
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

			GameType::ThreePlayer => &tn![
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
		match self {
			tn!(1m | 1p | 1s) => Number::One,
			tn!(2m | 2p | 2s) => Number::Two,
			tn!(3m | 3p | 3s) => Number::Three,
			tn!(4m | 4p | 4s) => Number::Four,
			tn!(5m | 5p | 5s) => Number::Five,
			tn!(0m | 0p | 0s) => Number::FiveRed,
			tn!(6m | 6p | 6s) => Number::Six,
			tn!(7m | 7p | 7s) => Number::Seven,
			tn!(8m | 8p | 8s) => Number::Eight,
			tn!(9m | 9p | 9s) => Number::Nine,
		}
	}

	pub const fn suit(self) -> NumberSuit {
		match self {
			tn!(1m | 2m | 3m | 4m | 5m | 0m | 6m | 7m | 8m | 9m) => NumberSuit::Man,
			tn!(1p | 2p | 3p | 4p | 5p | 0p | 6p | 7p | 8p | 9p) => NumberSuit::Pin,
			tn!(1s | 2s | 3s | 4s | 5s | 0s | 6s | 7s | 8s | 9s) => NumberSuit::Sou,
		}
	}

	pub(crate) fn shun_rest(self) -> Option<(Self, Self)> {
		let NumberTileClassified { suit, number } = self.into();
		let (number2, number3) = number.shun_rest()?;
		Some((
			(NumberTileClassified { suit, number: number2 }).into(),
			(NumberTileClassified { suit, number: number3 }).into(),
		))
	}

	pub(crate) fn is_next_in_sequence(self, previous: Self) -> bool {
		self.suit() == previous.suit() && self.number() == previous.number().next_in_sequence()
	}
}

impl std::fmt::Debug for NumberTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for NumberTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}{}", self.number(), self.suit())
	}
}

impl From<NumberTileClassified> for NumberTile {
	fn from(t: NumberTileClassified) -> Self {
		match t {
			NumberTileClassified { suit: NumberSuit::Man, number: Number::One } => tn!(1m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Two } => tn!(2m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Three } => tn!(3m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Four } => tn!(4m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Five } => tn!(5m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::FiveRed } => tn!(0m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Six } => tn!(6m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Seven } => tn!(7m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Eight } => tn!(8m),
			NumberTileClassified { suit: NumberSuit::Man, number: Number::Nine } => tn!(9m),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::One } => tn!(1p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Two } => tn!(2p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Three } => tn!(3p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Four } => tn!(4p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Five } => tn!(5p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::FiveRed } => tn!(0p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Six } => tn!(6p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Seven } => tn!(7p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Eight } => tn!(8p),
			NumberTileClassified { suit: NumberSuit::Pin, number: Number::Nine } => tn!(9p),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::One } => tn!(1s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Two } => tn!(2s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Three } => tn!(3s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Four } => tn!(4s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Five } => tn!(5s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::FiveRed } => tn!(0s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Six } => tn!(6s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Seven } => tn!(7s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Eight } => tn!(8s),
			NumberTileClassified { suit: NumberSuit::Sou, number: Number::Nine } => tn!(9s),
		}
	}
}

impl std::str::FromStr for NumberTile {
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

			_ => return Err(()),
		})
	}
}

impl Ord for NumberTile {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		self.suit().cmp(&other.suit()).then_with(|| self.number().cmp(&other.number()))
	}
}

impl PartialEq for NumberTile {
	fn eq(&self, other: &Self) -> bool {
		self.suit() == other.suit() && self.number() == other.number()
	}
}

impl PartialOrd for NumberTile {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
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

impl std::fmt::Debug for WindTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for WindTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Ton => f.write_str("E"),
			Self::Nan => f.write_str("S"),
			Self::Shaa => f.write_str("W"),
			Self::Pei => f.write_str("N"),
		}
	}
}

impl std::str::FromStr for WindTile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(match s {
			"E" |
			"1z" => Self::Ton,
			"S" |
			"2z" => Self::Nan,
			"W" |
			"3z" => Self::Shaa,
			"N" |
			"4z" => Self::Pei,

			_ => return Err(()),
		})
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

impl std::fmt::Debug for DragonTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for DragonTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Haku => f.write_str("Wh"),
			Self::Hatsu => f.write_str("G"),
			Self::Chun => f.write_str("R"),
		}
	}
}

impl std::str::FromStr for DragonTile {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(match s {
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

impl From<Tile> for TileClassified {
	fn from(t: Tile) -> Self {
		match t {
			t!(1m) => Self::Number(tn!(1m)),
			t!(2m) => Self::Number(tn!(2m)),
			t!(3m) => Self::Number(tn!(3m)),
			t!(4m) => Self::Number(tn!(4m)),
			t!(5m) => Self::Number(tn!(5m)),
			t!(0m) => Self::Number(tn!(0m)),
			t!(6m) => Self::Number(tn!(6m)),
			t!(7m) => Self::Number(tn!(7m)),
			t!(8m) => Self::Number(tn!(8m)),
			t!(9m) => Self::Number(tn!(9m)),
			t!(1p) => Self::Number(tn!(1p)),
			t!(2p) => Self::Number(tn!(2p)),
			t!(3p) => Self::Number(tn!(3p)),
			t!(4p) => Self::Number(tn!(4p)),
			t!(5p) => Self::Number(tn!(5p)),
			t!(0p) => Self::Number(tn!(0p)),
			t!(6p) => Self::Number(tn!(6p)),
			t!(7p) => Self::Number(tn!(7p)),
			t!(8p) => Self::Number(tn!(8p)),
			t!(9p) => Self::Number(tn!(9p)),
			t!(1s) => Self::Number(tn!(1s)),
			t!(2s) => Self::Number(tn!(2s)),
			t!(3s) => Self::Number(tn!(3s)),
			t!(4s) => Self::Number(tn!(4s)),
			t!(5s) => Self::Number(tn!(5s)),
			t!(0s) => Self::Number(tn!(0s)),
			t!(6s) => Self::Number(tn!(6s)),
			t!(7s) => Self::Number(tn!(7s)),
			t!(8s) => Self::Number(tn!(8s)),
			t!(9s) => Self::Number(tn!(9s)),
			t!(E) => Self::Wind(tw!(E)),
			t!(S) => Self::Wind(tw!(S)),
			t!(W) => Self::Wind(tw!(W)),
			t!(N) => Self::Wind(tw!(N)),
			t!(Wh) => Self::Dragon(td!(Wh)),
			t!(G) => Self::Dragon(td!(G)),
			t!(R) => Self::Dragon(td!(R)),
		}
	}
}

impl From<NumberTile> for NumberTileClassified {
	fn from(t: NumberTile) -> Self {
		Self { suit: t.suit(), number: t.number() }
	}
}

impl std::fmt::Debug for NumberSuit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for NumberSuit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Man => f.write_str("m"),
			Self::Pin => f.write_str("p"),
			Self::Sou => f.write_str("s"),
		}
	}
}

impl Number {
	pub const fn value(self) -> u8 {
		match self {
			Self::One => 1,
			Self::Two => 2,
			Self::Three => 3,
			Self::Four => 4,
			Self::Five |
			Self::FiveRed => 5,
			Self::Six => 6,
			Self::Seven => 7,
			Self::Eight => 8,
			Self::Nine => 9,
		}
	}

	const fn shun_rest(self) -> Option<(Self, Self)> {
		Some(match self {
			Self::One => (Self::Two, Self::Three),
			Self::Two => (Self::Three, Self::Four),
			Self::Three => (Self::Four, Self::Five),
			Self::Four => (Self::Five, Self::Six),
			Self::Five |
			Self::FiveRed => (Self::Six, Self::Seven),
			Self::Six => (Self::Seven, Self::Eight),
			Self::Seven => (Self::Eight, Self::Nine),
			Self::Eight |
			Self::Nine => return None,
		})
	}

	pub(crate) const fn next_in_sequence(self) -> Self {
		match self {
			Self::One => Self::Two,
			Self::Two => Self::Three,
			Self::Three => Self::Four,
			Self::Four => Self::Five,
			Self::Five |
			Self::FiveRed => Self::Six,
			Self::Six => Self::Seven,
			Self::Seven => Self::Eight,
			Self::Eight => Self::Nine,
			Self::Nine => Self::One,
		}
	}
}

impl std::fmt::Debug for Number {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for Number {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::One => f.write_str("1"),
			Self::Two => f.write_str("2"),
			Self::Three => f.write_str("3"),
			Self::Four => f.write_str("4"),
			Self::Five => f.write_str("5"),
			Self::FiveRed => f.write_str("0"),
			Self::Six => f.write_str("6"),
			Self::Seven => f.write_str("7"),
			Self::Eight => f.write_str("8"),
			Self::Nine => f.write_str("9"),
		}
	}
}

/// Note that `Five` is considered to be equal to `FiveRed`.
impl Ord for Number {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		self.value().cmp(&other.value())
	}
}

/// Note that `Five` is considered to be equal to `FiveRed`.
impl PartialEq for Number {
	fn eq(&self, other: &Self) -> bool {
		self.value() == other.value()
	}
}

/// Note that `Five` is considered to be equal to `FiveRed`.
impl PartialOrd for Number {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}
