use crate::GameType;

/// A tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum Tile {
	Number(NumberTile),
	Wind(WindTile),
	Dragon(DragonTile),
}

/// A number tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct NumberTile {
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

/// A wind tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum WindTile {
	/// East
	Ton,
	/// South
	Nan,
	/// West
	Shaa,
	/// North
	Pei,
}

/// A dragon tile.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum DragonTile {
	/// White
	Haku,
	/// Green
	Hatsu,
	/// Red
	Chun,
}

// TODO: Would be nice to make it size 1 without comprising on the enum-ness.
assert_size_of!(Tile, 2);

// TODO: Would be nice to make it size 1 without comprising on the separation of `Number` and `NumberSuit`.
assert_size_of!(NumberTile, 2);

impl Tile {
	pub fn all(game_type: GameType) -> impl Iterator<Item = Self> {
		match game_type {
			GameType::FourPlayer => [
				t!(1m), t!(1m), t!(1m), t!(1m),
				t!(2m), t!(2m), t!(2m), t!(2m),
				t!(3m), t!(3m), t!(3m), t!(3m),
				t!(4m), t!(4m), t!(4m), t!(4m),
				t!(5m), t!(5m), t!(5m), t!(0m),
				t!(6m), t!(6m), t!(6m), t!(6m),
				t!(7m), t!(7m), t!(7m), t!(7m),
				t!(8m), t!(8m), t!(8m), t!(8m),
				t!(9m), t!(9m), t!(9m), t!(9m),
				t!(1p), t!(1p), t!(1p), t!(1p),
				t!(2p), t!(2p), t!(2p), t!(2p),
				t!(3p), t!(3p), t!(3p), t!(3p),
				t!(4p), t!(4p), t!(4p), t!(4p),
				t!(5p), t!(5p), t!(5p), t!(0p),
				t!(6p), t!(6p), t!(6p), t!(6p),
				t!(7p), t!(7p), t!(7p), t!(7p),
				t!(8p), t!(8p), t!(8p), t!(8p),
				t!(9p), t!(9p), t!(9p), t!(9p),
				t!(1s), t!(1s), t!(1s), t!(1s),
				t!(2s), t!(2s), t!(2s), t!(2s),
				t!(3s), t!(3s), t!(3s), t!(3s),
				t!(4s), t!(4s), t!(4s), t!(4s),
				t!(5s), t!(5s), t!(5s), t!(0s),
				t!(6s), t!(6s), t!(6s), t!(6s),
				t!(7s), t!(7s), t!(7s), t!(7s),
				t!(8s), t!(8s), t!(8s), t!(8s),
				t!(9s), t!(9s), t!(9s), t!(9s),
				t!(E), t!(E), t!(E), t!(E),
				t!(S), t!(S), t!(S), t!(S),
				t!(W), t!(W), t!(W), t!(W),
				t!(N), t!(N), t!(N), t!(N),
				t!(Wh), t!(Wh), t!(Wh), t!(Wh),
				t!(G), t!(G), t!(G), t!(G),
				t!(R), t!(R), t!(R), t!(R),
			].iter().copied(),

			GameType::ThreePlayer => [
				t!(1m), t!(1m), t!(1m), t!(1m),
				t!(9m), t!(9m), t!(9m), t!(9m),
				t!(1p), t!(1p), t!(1p), t!(1p),
				t!(2p), t!(2p), t!(2p), t!(2p),
				t!(3p), t!(3p), t!(3p), t!(3p),
				t!(4p), t!(4p), t!(4p), t!(4p),
				t!(5p), t!(5p), t!(5p), t!(0p),
				t!(6p), t!(6p), t!(6p), t!(6p),
				t!(7p), t!(7p), t!(7p), t!(7p),
				t!(8p), t!(8p), t!(8p), t!(8p),
				t!(9p), t!(9p), t!(9p), t!(9p),
				t!(1s), t!(1s), t!(1s), t!(1s),
				t!(2s), t!(2s), t!(2s), t!(2s),
				t!(3s), t!(3s), t!(3s), t!(3s),
				t!(4s), t!(4s), t!(4s), t!(4s),
				t!(5s), t!(5s), t!(5s), t!(0s),
				t!(6s), t!(6s), t!(6s), t!(6s),
				t!(7s), t!(7s), t!(7s), t!(7s),
				t!(8s), t!(8s), t!(8s), t!(8s),
				t!(9s), t!(9s), t!(9s), t!(9s),
				t!(E), t!(E), t!(E), t!(E),
				t!(S), t!(S), t!(S), t!(S),
				t!(W), t!(W), t!(W), t!(W),
				t!(N), t!(N), t!(N), t!(N),
				t!(Wh), t!(Wh), t!(Wh), t!(Wh),
				t!(G), t!(G), t!(G), t!(G),
				t!(R), t!(R), t!(R), t!(R),
			].iter().copied(),
		}
	}

	/// Returns the tile that would be a dora tile if this tile was revealed in the dead wall.
	///
	/// # Example
	///
	/// ```rust
	/// # use riichi::{GameType, t};
	/// assert_eq!(t!(2m).indicates_dora(GameType::FourPlayer), t!(3m));
	/// assert_eq!(t!(1m).indicates_dora(GameType::ThreePlayer), t!(9m));
	/// ```
	pub const fn indicates_dora(self, game_type: GameType) -> Self {
		match self {
			Self::Number(tile) => Self::Number(tile.indicates_dora(game_type)),
			Self::Dragon(tile) => Self::Dragon(tile.indicates_dora()),
			Self::Wind(tile) => Self::Wind(tile.indicates_dora()),
		}
	}

	pub(crate) const fn is_simple(self) -> bool {
		match self {
			Tile::Number(t) => t.is_simple(),
			Tile::Wind(_) |
			Tile::Dragon(_) => false,
		}
	}

	pub(crate) const fn is_terminal(self) -> bool {
		match self {
			Tile::Number(t) => t.is_terminal(),
			Tile::Wind(_) |
			Tile::Dragon(_) => false,
		}
	}

	pub(crate) const fn is_honor(self) -> bool {
		match self {
			Tile::Number(_) => false,
			Tile::Wind(_) |
			Tile::Dragon(_) => true,
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
		match self {
			Self::Number(tile) => tile.fmt(f),
			Self::Wind(tile) => tile.fmt(f),
			Self::Dragon(tile) => tile.fmt(f),
		}
	}
}

impl NumberTile {
	pub fn all(game_type: GameType) -> impl Iterator<Item = Self> {
		match game_type {
			GameType::FourPlayer => [
				tn!(1m), tn!(1m), tn!(1m), tn!(1m),
				tn!(2m), tn!(2m), tn!(2m), tn!(2m),
				tn!(3m), tn!(3m), tn!(3m), tn!(3m),
				tn!(4m), tn!(4m), tn!(4m), tn!(4m),
				tn!(5m), tn!(5m), tn!(5m), tn!(0m),
				tn!(6m), tn!(6m), tn!(6m), tn!(6m),
				tn!(7m), tn!(7m), tn!(7m), tn!(7m),
				tn!(8m), tn!(8m), tn!(8m), tn!(8m),
				tn!(9m), tn!(9m), tn!(9m), tn!(9m),
				tn!(1p), tn!(1p), tn!(1p), tn!(1p),
				tn!(2p), tn!(2p), tn!(2p), tn!(2p),
				tn!(3p), tn!(3p), tn!(3p), tn!(3p),
				tn!(4p), tn!(4p), tn!(4p), tn!(4p),
				tn!(5p), tn!(5p), tn!(5p), tn!(0p),
				tn!(6p), tn!(6p), tn!(6p), tn!(6p),
				tn!(7p), tn!(7p), tn!(7p), tn!(7p),
				tn!(8p), tn!(8p), tn!(8p), tn!(8p),
				tn!(9p), tn!(9p), tn!(9p), tn!(9p),
				tn!(1s), tn!(1s), tn!(1s), tn!(1s),
				tn!(2s), tn!(2s), tn!(2s), tn!(2s),
				tn!(3s), tn!(3s), tn!(3s), tn!(3s),
				tn!(4s), tn!(4s), tn!(4s), tn!(4s),
				tn!(5s), tn!(5s), tn!(5s), tn!(0s),
				tn!(6s), tn!(6s), tn!(6s), tn!(6s),
				tn!(7s), tn!(7s), tn!(7s), tn!(7s),
				tn!(8s), tn!(8s), tn!(8s), tn!(8s),
				tn!(9s), tn!(9s), tn!(9s), tn!(9s),
			].iter().copied(),

			GameType::ThreePlayer => [
				tn!(1m), tn!(1m), tn!(1m), tn!(1m),
				tn!(9m), tn!(9m), tn!(9m), tn!(9m),
				tn!(1p), tn!(1p), tn!(1p), tn!(1p),
				tn!(2p), tn!(2p), tn!(2p), tn!(2p),
				tn!(3p), tn!(3p), tn!(3p), tn!(3p),
				tn!(4p), tn!(4p), tn!(4p), tn!(4p),
				tn!(5p), tn!(5p), tn!(5p), tn!(0p),
				tn!(6p), tn!(6p), tn!(6p), tn!(6p),
				tn!(7p), tn!(7p), tn!(7p), tn!(7p),
				tn!(8p), tn!(8p), tn!(8p), tn!(8p),
				tn!(9p), tn!(9p), tn!(9p), tn!(9p),
				tn!(1s), tn!(1s), tn!(1s), tn!(1s),
				tn!(2s), tn!(2s), tn!(2s), tn!(2s),
				tn!(3s), tn!(3s), tn!(3s), tn!(3s),
				tn!(4s), tn!(4s), tn!(4s), tn!(4s),
				tn!(5s), tn!(5s), tn!(5s), tn!(0s),
				tn!(6s), tn!(6s), tn!(6s), tn!(6s),
				tn!(7s), tn!(7s), tn!(7s), tn!(7s),
				tn!(8s), tn!(8s), tn!(8s), tn!(8s),
				tn!(9s), tn!(9s), tn!(9s), tn!(9s),
			].iter().copied(),
		}
	}

	/// Returns the tile that would be a dora tile if this tile was revealed in the dead wall.
	///
	/// # Example
	///
	/// ```rust
	/// # use riichi::{GameType, tn};
	/// assert_eq!(tn!(2m).indicates_dora(GameType::FourPlayer), tn!(3m));
	/// assert_eq!(tn!(1m).indicates_dora(GameType::ThreePlayer), tn!(9m));
	/// ```
	pub const fn indicates_dora(self, game_type: GameType) -> Self {
		let number =
			if matches!((self, game_type), (tn!(1m), GameType::ThreePlayer)) {
				Number::Nine
			}
			else {
				self.number.next_in_sequence()
			};
		Self { suit: self.suit, number }
	}

	pub(crate) fn is_next_in_sequence(self, previous: Self) -> bool {
		self.suit == previous.suit && self.number == previous.number.next_in_sequence()
	}

	pub(crate) const fn is_simple(self) -> bool {
		!self.is_terminal()
	}

	pub(crate) const fn is_terminal(self) -> bool {
		matches!(self.number, Number::One | Number::Nine)
	}
}

impl std::fmt::Debug for NumberTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for NumberTile {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}{}", self.number, self.suit)
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

	const fn next_in_sequence(self) -> Self {
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

impl WindTile {
	pub const fn all() -> [Self; 16] {
		[
			tw!(E), tw!(E), tw!(E), tw!(E),
			tw!(S), tw!(S), tw!(S), tw!(S),
			tw!(W), tw!(W), tw!(W), tw!(W),
			tw!(N), tw!(N), tw!(N), tw!(N),
		]
	}

	/// Returns the tile that would be a dora tile if this tile was revealed in the dead wall.
	///
	/// # Example
	///
	/// ```rust
	/// # use riichi::tw;
	/// assert_eq!(tw!(N).indicates_dora(), tw!(E));
	/// ```
	pub const fn indicates_dora(self) -> Self {
		match self {
			Self::Ton => Self::Nan,
			Self::Nan => Self::Shaa,
			Self::Shaa => Self::Pei,
			Self::Pei => Self::Ton,
		}
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

impl DragonTile {
	pub const fn all() -> [Self; 12] {
		[
			td!(Wh), td!(Wh), td!(Wh), td!(Wh),
			td!(G), td!(G), td!(G), td!(G),
			td!(R), td!(R), td!(R), td!(R),
		]
	}

	/// Returns the tile that would be a dora tile if this tile was revealed in the dead wall.
	///
	/// # Example
	///
	/// ```rust
	/// # use riichi::td;
	/// assert_eq!(td!(R).indicates_dora(), td!(Wh));
	/// ```
	pub const fn indicates_dora(self) -> Self {
		match self {
			Self::Haku => Self::Hatsu,
			Self::Hatsu => Self::Chun,
			Self::Chun => Self::Haku,
		}
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
