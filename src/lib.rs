#![feature(
	array_windows,
	generic_const_exprs,
	iter_next_chunk,
	maybe_uninit_array_assume_init,
	maybe_uninit_slice,
)]
#![expect(
	incomplete_features, // For generic_const_exprs
)]

//! # To simulate a round
//!
//! Make an initial [`Hand`] for each player with [`make_hand`] or using [`Hand`] directly. Wrap each in [`HandStable`] using `.into()`.
//!
//! Each time a tile is drawn from the wall or discarded or made into a shouminkan, every other player checks to see if
//! their `HandStable` can use that tile to end the round (see the process of "To score a hand" below) or to form
//! [a minjun](HandStable::find_minjuns) (chii on left player's discard) or [a minkou](HandStable::find_minkous) (pon) or [an ankan](HandStable::find_ankan)
//! or [a shouminkan](HandStable::find_shouminkan) or [a daiminkan](HandStable::find_daiminkan) (kan).
//!
//! In the case where a [`ScorableHand`] is found and the player decides to end the round with that hand, end the round and
//! distribute points accordingly.
//!
//! In the case where the player chooses to form a kan, the result is another `HandStable` and it becomes this player's turn to draw from the wall.
//!
//! In the case where the player chooses to form a minjun or minkou, the result is a [`HandTentative`]
//! and one tile must be [discarded](HandTentative::discard) to return to a `HandStable` and continue with the next player's turn.
//!
//! Otherwise if it was this player's turn and this tile was drawn from the wall, the player chooses to either discard the new tile,
//! or to replace one of the tiles in their `HandStable` with it and discard the replaced tile.
//!
//! # To score a hand
//!
//! Make a [`Hand`] with [`make_hand`] or using [`Hand`] directly. Wrap it in a [`HandStable`] if desired.
//!
//! Draw a tile and call [`Hand::to_scorable_hands`] or [`HandStable::to_scorable_hands`] to get a set of [`ScorableHand`]s.
//!
//! For each `ScorableHand`, call [`ScorableHand::score`] to get a [`ScoreRaw`] for that hand
//! that breaks down all the fu / han / yakuman for that hand, if the hand can actually score.
//!
//! For each `ScoreRaw`, call `.into()` to get a [`Score`] for that hand that aggregates
//! all the fu / han / yakuman for that hand.
//!
//! For each `Score`, call [`Score::score`] to get a [`Points`] value with the breakdown of points
//! taken from each player type.
//!
//! For each `Points`, call [`Points::total`] to get a total numerical point value.
//!
//! Pick the [`ScorableHand`] with the largest numerical point value.
//!
//! # Example
//!
//! ```rust
//! # #![feature(generic_const_exprs)]
//! # #![expect(incomplete_features)]
//! #
//! # use riichi::{
//! #     DragonTile,
//! #     Fu,
//! #     GameType,
//! #     Han,
//! #     Number, NumberSuit, NumberTile,
//! #     Points,
//! #     Riichi,
//! #     Score, ScoreRaw,
//! #     Tile, TsumoOrRon,
//! #     WindTile, WinningTileFrom,
//! #     make_hand, make_scorable_hand,
//! #     t, tw,
//! # };
//! #
//! # // Source: https://mahjongsoul.game.yo-star.com/?paipu=251104-fbcdd597-8e44-4ad9-924b-607ffc64fb97_a913354171
//! #
//! // Hand containing 2s .. Wh tiles, an ankan of four E tiles
//! let hand = make_hand!(2s 3s 3s 4s 4s 8s 8s Wh Wh Wh { ankan E E E E });
//! // Add a 2s to the hand using ron and check for scorable hands.
//! let winning_tile_from = WinningTileFrom::Ron;
//! let mut hands = hand.to_scorable_hands(t!(2s), winning_tile_from.into());
//! assert_eq!(hands.len(), 1);
//! let hand = hands.pop_first().unwrap();
//! assert_eq!(hand, make_scorable_hand!({ anjun 2s 3s 4s } { ankou Wh Wh Wh } { ankan E E E E } { minjun 2s 3s 4s ryanmen_left } { 8s 8s }));
//!
//! let game_type = GameType::ThreePlayer;
//! let score = hand.score(
//!     Riichi::Riichi { ippatsu: false, double: false },
//!     winning_tile_from,
//!     0,
//!     game_type,
//!     [t!(G), t!(5p), t!(5s), t!(6p), t!(S), t!(N)],
//!     tw!(E),
//!     tw!(S),
//! ).unwrap();
//! assert_eq!(score, ScoreRaw {
//!     base: Fu(20),
//!     win_condition: Fu(10),
//!     meld2: Fu(32), // { ankan E E E E }
//!     meld3: Fu(8), // { ankou Wh Wh Wh }
//!     riichi: Han(1),
//!     iipeikou: Han(1),
//!     yakuhai_ton: Han(1),
//!     yakuhai_haku: Han(1),
//!     honitsu: Han(3),
//!     dora: Han(4),
//!     ..Default::default()
//! });
//!
//! let score: Score = score.into();
//! assert_eq!(score, Score { fu: 70, han: 11, yakuman: 0 });
//!
//! let is_dealer = false;
//! let score = score.score(is_dealer, winning_tile_from.into());
//! assert_eq!(score, Points::FromRon(24000));
//!
//! let score = score.total(is_dealer, game_type);
//! assert_eq!(score, 24000);
//! ```

// Refs:
//
// - https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
// - https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175
/// Returns a [`Tile`] corresponding to the input.
///
/// The expansion is usable as both an expr and a pat.
///
/// # Examples
///
/// ```rust
/// # use riichi::{DragonTile, Number, NumberSuit, NumberTile, Tile, WindTile, t};
/// let tile = t!(4m);
/// assert_eq!(tile, Tile::Number(NumberTile { suit: NumberSuit::Man, number: Number::Four }));
///
/// let tile = t!(5p);
/// assert_eq!(tile, Tile::Number(NumberTile { suit: NumberSuit::Pin, number: Number::Five }));
///
/// let tile = t!(6s);
/// assert_eq!(tile, Tile::Number(NumberTile { suit: NumberSuit::Sou, number: Number::Six }));
///
/// // Red fives are represented by the number 0.
/// let tile = t!(0s);
/// assert_eq!(tile, Tile::Number(NumberTile { suit: NumberSuit::Sou, number: Number::FiveRed }));
///
/// // Wind tiles are E, S, W, N or 1z, 2z, 3z, 4z.
/// let tile = t!(E);
/// assert_eq!(tile, Tile::Wind(WindTile::Ton));
/// let tile = t!(2z);
/// assert_eq!(tile, Tile::Wind(WindTile::Nan));
///
/// // Dragon tiles are Wh, G, R or 5z, 6z, 7z.
/// let tile = t!(Wh);
/// assert_eq!(tile, Tile::Dragon(DragonTile::Haku));
/// let tile = t!(6z);
/// assert_eq!(tile, Tile::Dragon(DragonTile::Hatsu));
/// ```
#[macro_export]
macro_rules! t {
	(1m) => { $crate::Tile::Number($crate::tn!(1m)) };
	(2m) => { $crate::Tile::Number($crate::tn!(2m)) };
	(3m) => { $crate::Tile::Number($crate::tn!(3m)) };
	(4m) => { $crate::Tile::Number($crate::tn!(4m)) };
	(5m) => { $crate::Tile::Number($crate::tn!(5m)) };
	(0m) => { $crate::Tile::Number($crate::tn!(0m)) };
	(6m) => { $crate::Tile::Number($crate::tn!(6m)) };
	(7m) => { $crate::Tile::Number($crate::tn!(7m)) };
	(8m) => { $crate::Tile::Number($crate::tn!(8m)) };
	(9m) => { $crate::Tile::Number($crate::tn!(9m)) };

	(1p) => { $crate::Tile::Number($crate::tn!(1p)) };
	(2p) => { $crate::Tile::Number($crate::tn!(2p)) };
	(3p) => { $crate::Tile::Number($crate::tn!(3p)) };
	(4p) => { $crate::Tile::Number($crate::tn!(4p)) };
	(5p) => { $crate::Tile::Number($crate::tn!(5p)) };
	(0p) => { $crate::Tile::Number($crate::tn!(0p)) };
	(6p) => { $crate::Tile::Number($crate::tn!(6p)) };
	(7p) => { $crate::Tile::Number($crate::tn!(7p)) };
	(8p) => { $crate::Tile::Number($crate::tn!(8p)) };
	(9p) => { $crate::Tile::Number($crate::tn!(9p)) };

	(1s) => { $crate::Tile::Number($crate::tn!(1s)) };
	(2s) => { $crate::Tile::Number($crate::tn!(2s)) };
	(3s) => { $crate::Tile::Number($crate::tn!(3s)) };
	(4s) => { $crate::Tile::Number($crate::tn!(4s)) };
	(5s) => { $crate::Tile::Number($crate::tn!(5s)) };
	(0s) => { $crate::Tile::Number($crate::tn!(0s)) };
	(6s) => { $crate::Tile::Number($crate::tn!(6s)) };
	(7s) => { $crate::Tile::Number($crate::tn!(7s)) };
	(8s) => { $crate::Tile::Number($crate::tn!(8s)) };
	(9s) => { $crate::Tile::Number($crate::tn!(9s)) };

	(E) => { $crate::Tile::Wind($crate::tw!(E)) };
	(1z) => { $crate::Tile::Wind($crate::tw!(1z)) };
	(S) => { $crate::Tile::Wind($crate::tw!(S)) };
	(2z) => { $crate::Tile::Wind($crate::tw!(2z)) };
	(W) => { $crate::Tile::Wind($crate::tw!(W)) };
	(3z) => { $crate::Tile::Wind($crate::tw!(3z)) };
	(N) => { $crate::Tile::Wind($crate::tw!(N)) };
	(4z) => { $crate::Tile::Wind($crate::tw!(4z)) };

	(Wh) => { $crate::Tile::Dragon($crate::td!(Wh)) };
	(5z) => { $crate::Tile::Dragon($crate::td!(5z)) };
	(G) => { $crate::Tile::Dragon($crate::td!(G)) };
	(6z) => { $crate::Tile::Dragon($crate::td!(6z)) };
	(R) => { $crate::Tile::Dragon($crate::td!(R)) };
	(7z) => { $crate::Tile::Dragon($crate::td!(7z)) };
}

/// Returns a [`NumberTile`] corresponding to the input.
///
/// The expansion is usable as both an expr and a pat.
///
/// # Examples
///
/// ```rust
/// # use riichi::{Number, NumberSuit, NumberTile, tn};
/// let tile = tn!(4m);
/// assert_eq!(tile, NumberTile { suit: NumberSuit::Man, number: Number::Four });
///
/// let tile = tn!(5p);
/// assert_eq!(tile, NumberTile { suit: NumberSuit::Pin, number: Number::Five });
///
/// let tile = tn!(6s);
/// assert_eq!(tile, NumberTile { suit: NumberSuit::Sou, number: Number::Six });
///
/// // Red fives are represented by the number 0.
/// let tile = tn!(0s);
/// assert_eq!(tile, NumberTile { suit: NumberSuit::Sou, number: Number::FiveRed });
/// ```
#[macro_export]
macro_rules! tn {
	(1m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::One } };
	(2m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Two } };
	(3m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Three } };
	(4m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Four } };
	(5m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Five } };
	(0m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::FiveRed } };
	(6m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Six } };
	(7m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Seven } };
	(8m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Eight } };
	(9m) => { $crate::NumberTile { suit: $crate::NumberSuit::Man, number: $crate::Number::Nine } };

	(1p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::One } };
	(2p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Two } };
	(3p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Three } };
	(4p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Four } };
	(5p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Five } };
	(0p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::FiveRed } };
	(6p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Six } };
	(7p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Seven } };
	(8p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Eight } };
	(9p) => { $crate::NumberTile { suit: $crate::NumberSuit::Pin, number: $crate::Number::Nine } };

	(1s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::One } };
	(2s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Two } };
	(3s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Three } };
	(4s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Four } };
	(5s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Five } };
	(0s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::FiveRed } };
	(6s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Six } };
	(7s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Seven } };
	(8s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Eight } };
	(9s) => { $crate::NumberTile { suit: $crate::NumberSuit::Sou, number: $crate::Number::Nine } };
}

/// Returns a [`WindTile`] corresponding to the input.
///
/// The expansion is usable as both an expr and a pat.
///
/// # Examples
///
/// ```rust
/// # use riichi::{WindTile, tw};
/// // Wind tiles are E, S, W, N or 1z, 2z, 3z, 4z.
/// let tile = tw!(E);
/// assert_eq!(tile, WindTile::Ton);
/// let tile = tw!(2z);
/// assert_eq!(tile, WindTile::Nan);
/// ```
#[macro_export]
macro_rules! tw {
	(E) => { $crate::WindTile::Ton };
	(1z) => { $crate::WindTile::Ton };
	(S) => { $crate::WindTile::Nan };
	(2z) => { $crate::WindTile::Nan };
	(W) => { $crate::WindTile::Shaa };
	(3z) => { $crate::WindTile::Shaa };
	(N) => { $crate::WindTile::Pei };
	(4z) => { $crate::WindTile::Pei };
}

/// Returns a [`DragonTile`] corresponding to the input.
///
/// The expansion is usable as both an expr and a pat.
///
/// # Examples
///
/// ```rust
/// # use riichi::{DragonTile, td};
/// // Dragon tiles are Wh, G, R or 5z, 6z, 7z.
/// let tile = td!(Wh);
/// assert_eq!(tile, DragonTile::Haku);
/// let tile = td!(6z);
/// assert_eq!(tile, DragonTile::Hatsu);
/// ```
#[macro_export]
macro_rules! td {
	(Wh) => { $crate::DragonTile::Haku };
	(5z) => { $crate::DragonTile::Haku };
	(G) => { $crate::DragonTile::Hatsu };
	(6z) => { $crate::DragonTile::Hatsu };
	(R) => { $crate::DragonTile::Chun };
	(7z) => { $crate::DragonTile::Chun };
}

/// Creates a [`Hand`] value from the tiles and melds given in the input.
///
/// Individual tiles are specified using the same tokens as what the [`t`] macro takes.
///
/// Melds are specified as `{ <meld_type> <tile1> <tile2> <tile3> [<tile4>] }`, where `<meld_type>` is one of:
///
/// - `minjun` - open sequence formed by chii
/// - `minkou` - open triplet formed by pon
/// - `ankan` - closed quad formed by kan
/// - `minkan` - open quad formed by kan
///
/// # Examples
///
/// ```rust
/// # #![feature(generic_const_exprs)]
/// # #![expect(incomplete_features)]
/// #
/// # use riichi::{Hand, HandMeld, make_hand, t};
/// // Hand containing 2s .. Wh tiles, an ankan of four E tiles.
/// let hand = make_hand!(2s 3s 3s 4s 4s 8s 8s Wh Wh Wh { ankan E E E E });
/// assert!(matches!(hand, Hand(
///     [
///         t!(2s),
///         t!(3s),
///         t!(3s),
///         t!(4s),
///         t!(4s),
///         t!(8s),
///         t!(8s),
///         t!(Wh),
///         t!(Wh),
///         t!(Wh),
///     ],
///     [
///         HandMeld::Ankan([t!(E), t!(E), t!(E), t!(E)]),
///     ],
/// )));
/// ```
#[macro_export]
macro_rules! make_hand {
	(@meld { minjun $t1:tt $t2:tt $t3:tt }) => {
		$crate::HandMeld::Minjun([
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		])
	};

	(@meld { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::HandMeld::Minkou([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
		])
	};

	(@meld { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::HandMeld::Ankan([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
		])
	};

	(@meld { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::HandMeld::Minkan([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
		])
	};

	($t1:tt $m1:tt $m2:tt $m3:tt $m4:tt) => {
		$crate::Hand::<1, 4>(
			[
				$crate::t!($t1),
			],
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
				$crate::make_hand!(@meld $m4),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $m1:tt $m2:tt $m3:tt) => {
		$crate::Hand::<4, 3>(
			[
				$crate::t!($t1),
				$crate::t!($t2),
				$crate::t!($t3),
				$crate::t!($t4),
			],
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $m1:tt $m2:tt) => {
		$crate::Hand::<7, 2>(
			[
				$crate::t!($t1),
				$crate::t!($t2),
				$crate::t!($t3),
				$crate::t!($t4),
				$crate::t!($t5),
				$crate::t!($t6),
				$crate::t!($t7),
			],
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $m1:tt) => {
		$crate::Hand::<10, 1>(
			[
				$crate::t!($t1),
				$crate::t!($t2),
				$crate::t!($t3),
				$crate::t!($t4),
				$crate::t!($t5),
				$crate::t!($t6),
				$crate::t!($t7),
				$crate::t!($t8),
				$crate::t!($t9),
				$crate::t!($t10),
			],
			[
				$crate::make_hand!(@meld $m1),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt) => {
		$crate::Hand::<13, 0>(
			[
				$crate::t!($t1),
				$crate::t!($t2),
				$crate::t!($t3),
				$crate::t!($t4),
				$crate::t!($t5),
				$crate::t!($t6),
				$crate::t!($t7),
				$crate::t!($t8),
				$crate::t!($t9),
				$crate::t!($t10),
				$crate::t!($t11),
				$crate::t!($t12),
				$crate::t!($t13),
			],
			[],
		)
	};
}

/// Creates a [`ScorableHand`] value from the melds and pairs given in the input.
///
/// Individual tiles are specified using the same tokens as what the [`t`] macro takes.
///
/// Hands are either [regular](ScorableHand::Regular) (standard four-melds-one-pair shape),
/// [chiitoi](ScorableHand::Chiitoi) (seven-pairs shape) or
/// [kokushi musou](ScorableHand::KokushiMusou) (fourteen individual tiles).
///
/// # Regular hands
///
/// `make_scorable_hand!(<meld1> <meld2> <meld3> <meld4> <pair>)`
///
/// The first three melds are specified as `{ <meld_type> <tile1> <tile2> <tile3> [<tile4>] }`, where `<meld_type>` is one of:
///
/// - `anjun`: Closed sequence held in hand. Eg `{ anjun 2m 3m 4m }`
/// - `minjun`: Open sequence formed by chii. Eg `{ minjun 2m 3m 4m }`
/// - `ankou` - Closed triplet held in hand. Eg `{ ankou 3p 3p 3p }`
/// - `minkou` - Open triplet formed by pon. Eg `{ minkou 3p 3p 3p }`
/// - `ankan` - Closed quad formed by kan. Eg `{ ankan 4s 4s 4s 4s }`
/// - `minkan` - Open quad formed by kan. Eg `{ minkan 4s 4s 4s 4s }`
///
/// The fourth meld is specified like the first three melds, except it takes an additional optional input to specify the wait
/// for the hand:
///
/// - `kanchan` indicates that the fourth meld had a kanchan wait.
/// - `penchan` indicates that the fourth meld had a penchan wait.
/// - `ryanmen_left` indicates that the fourth meld had a ryanmen wait and the left tile (lower number) completed the hand.
/// - `ryanmen_right` indicates that the fourth meld had a ryanmen wait and the right tile (highest number) completed the hand.
/// - `shanpon` indicates that the fourth meld had a shanpon wait, and that the meld was completed via tsumo.
/// - Not specifying any of these indicates that the fourth meld was already complete and the hand had a tanki wait.
///
/// Eg `{ anjun 1m 2m 3m penchan }` indicates this meld had a penchan wait and was completed (3m) using tsumo.
///
/// Eg `{ minjun 1m 2m 3m penchan }` indicates this meld had a penchan wait and was completed (3m) using ron.
///
/// Eg `{ minjun 1m 2m 3m }` indicates this meld was already complete, and the pair was the one that had the wait.
///
/// The final pair is specified as `{ <tile1> <tile2> }`. Eg `{ R R }`
///
/// # Chiitoi
///
/// `make_scorable_hand!(<pair1> <pair2> <pair3> <pair4> <pair5> <pair6> <pair7>)`
///
/// Each of the seven pairs is specified as `{ <tile1> <tile2> }`. Eg `{ 1m 1m }`
///
/// # Kokushi musou
///
/// `make_scorable_hand!(<tile1> <tile2> <tile3> <tile4> <tile5> <tile6> <tile7> <tile8> <tile9> <tile10> <tile11> <tile12> <tile13> <tile14> [juusanmen])`
///
/// The fourteen tiles are listed individually.
///
/// Specifying `juusanmen` at the end indicates this hand had a thirteen-sided wait.
///
/// # Examples
///
/// ```rust
/// # use riichi::{
/// #     ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair,
/// #     TsumoOrRon,
/// #     make_scorable_hand,
/// #     t, tn,
/// # };
/// let hand = make_scorable_hand!({ anjun 2s 3s 4s } { ankou Wh Wh Wh } { ankan E E E E } { minjun 2s 3s 4s ryanmen_left } { 8s 8s });
/// assert_eq!(hand, ScorableHand::Regular {
///     melds: (
///         [
///             ScorableHandMeld::Anjun([tn!(2s), tn!(3s), tn!(4s)]),
///             ScorableHandMeld::Ankan([t!(E), t!(E), t!(E), t!(E)]),
///             ScorableHandMeld::Ankou([t!(Wh), t!(Wh), t!(Wh)]),
///         ],
///         ScorableHandFourthMeld::RyanmenLeft { tiles: [tn!(2s), tn!(3s), tn!(4s)], tsumo_or_ron: TsumoOrRon::Ron },
///     ),
///     pair: ScorableHandPair([t!(8s), t!(8s)]),
/// });
/// ```
///
/// ```rust
/// # use riichi::{ScorableHand, ScorableHandPair, make_scorable_hand, t, tn};
/// let hand = make_scorable_hand!({ 1m 1m } { 3m 3m } { 4m 4m } { 5p 5p } { 2s 2s } { W W } { Wh Wh });
/// assert_eq!(hand, ScorableHand::Chiitoi([
///     ScorableHandPair([t!(1m), t!(1m)]),
///     ScorableHandPair([t!(3m), t!(3m)]),
///     ScorableHandPair([t!(4m), t!(4m)]),
///     ScorableHandPair([t!(5p), t!(5p)]),
///     ScorableHandPair([t!(2s), t!(2s)]),
///     ScorableHandPair([t!(W), t!(W)]),
///     ScorableHandPair([t!(Wh), t!(Wh)]),
/// ]));
/// ```
///
/// ```rust
/// # use riichi::{ScorableHand, make_scorable_hand, t};
/// let hand = make_scorable_hand!(1m 9m 1p 9p 1s 1s 9s E S W N G R Wh);
/// assert_eq!(hand, ScorableHand::KokushiMusou {
///     tiles: [
///         t!(1m), t!(9m),
///         t!(1p), t!(9p),
///         t!(1s), t!(1s), t!(9s),
///         t!(E), t!(S), t!(W), t!(N),
///         t!(Wh), t!(G), t!(R),
///     ],
///     was_juusanmen_wait: false,
/// });
/// ```
#[macro_export]
macro_rules! make_scorable_hand {
	(@meld { anjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandMeld::Anjun(tiles)
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::Anjun(tiles))
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt kanchan }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::Kanchan { tiles, tsumo_or_ron: $crate::TsumoOrRon::Tsumo }
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt penchan }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron: $crate::TsumoOrRon::Tsumo }
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt ryanmen_left }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::RyanmenLeft { tiles, tsumo_or_ron: $crate::TsumoOrRon::Tsumo }
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt ryanmen_right }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::RyanmenRight { tiles, tsumo_or_ron: $crate::TsumoOrRon::Tsumo }
	}};

	(@meld { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandMeld::Minjun(tiles)
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::Minjun(tiles))
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt kanchan }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::Kanchan { tiles, tsumo_or_ron: $crate::TsumoOrRon::Ron }
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt penchan }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron: $crate::TsumoOrRon::Ron }
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt ryanmen_left }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::RyanmenLeft { tiles, tsumo_or_ron: $crate::TsumoOrRon::Ron }
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt ryanmen_right }) => {{
		let mut tiles = [
			$crate::tn!($t1),
			$crate::tn!($t2),
			$crate::tn!($t3),
		];
		tiles.sort_unstable();
		$crate::ScorableHandFourthMeld::RyanmenRight { tiles, tsumo_or_ron: $crate::TsumoOrRon::Ron }
	}};

	(@meld { ankou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandMeld::Ankou([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
		])
	};

	(@meldr4 { ankou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::Ankou([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
		]))
	};

	(@meldr4 { ankou $t1:tt $t2:tt $t3:tt shanpon }) => {
		$crate::ScorableHandFourthMeld::Shanpon {
			tiles: [
				$crate::t!($t1),
				$crate::t!($t2),
				$crate::t!($t3),
			],
			tsumo_or_ron: $crate::TsumoOrRon::Tsumo,
		}
	};

	(@meld { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandMeld::Minkou([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
		])
	};

	(@meldr4 { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::Minkou([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
		]))
	};

	(@meldr4 { minkou $t1:tt $t2:tt $t3:tt shanpon }) => {
		$crate::ScorableHandFourthMeld::Shanpon {
			tiles: [
				$crate::t!($t1),
				$crate::t!($t2),
				$crate::t!($t3),
			],
			tsumo_or_ron: $crate::TsumoOrRon::Ron,
		}
	};

	(@meld { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandMeld::Ankan([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
		])
	};

	(@meldr4 { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::Ankan([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
		]))
	};

	(@meld { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandMeld::Minkan([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
		])
	};

	(@meldr4 { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::Minkan([
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
		]))
	};

	($m1:tt $m2:tt $m3:tt $m4:tt { $p1:tt $p2:tt }) => {{
		let m1 = $crate::make_scorable_hand!(@meld $m1);
		let m2 = $crate::make_scorable_hand!(@meld $m2);
		let m3 = $crate::make_scorable_hand!(@meld $m3);
		let m4 = $crate::make_scorable_hand!(@meldr4 $m4);
		$crate::ScorableHand::regular(
			[m1, m2, m3],
			m4,
			$crate::ScorableHandPair([
				$crate::t!($p1),
				$crate::t!($p2),
			]),
		)
	}};

	({ $p1:tt $p2:tt } { $p3:tt $p4:tt } { $p5:tt $p6:tt } { $p7:tt $p8:tt } { $p9:tt $p10:tt } { $p11:tt $p12:tt } { $p13:tt $p14:tt }) => {{
		let mut pairs = [
			$crate::ScorableHandPair([
				$crate::t!($p1),
				$crate::t!($p2),
			]),
			$crate::ScorableHandPair([
				$crate::t!($p3),
				$crate::t!($p4),
			]),
			$crate::ScorableHandPair([
				$crate::t!($p5),
				$crate::t!($p6),
			]),
			$crate::ScorableHandPair([
				$crate::t!($p7),
				$crate::t!($p8),
			]),
			$crate::ScorableHandPair([
				$crate::t!($p9),
				$crate::t!($p10),
			]),
			$crate::ScorableHandPair([
				$crate::t!($p11),
				$crate::t!($p12),
			]),
			$crate::ScorableHandPair([
				$crate::t!($p13),
				$crate::t!($p14),
			]),
		];
		pairs.sort_unstable();
		$crate::ScorableHand::Chiitoi(pairs)
	}};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt) => {{
		let mut ts = [
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
			$crate::t!($t5),
			$crate::t!($t6),
			$crate::t!($t7),
			$crate::t!($t8),
			$crate::t!($t9),
			$crate::t!($t10),
			$crate::t!($t11),
			$crate::t!($t12),
			$crate::t!($t13),
			$crate::t!($t14),
		];
		ts.sort_unstable();
		$crate::ScorableHand::KokushiMusou { tiles: ts, was_juusanmen_wait: false }
	}};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt juusanmen) => {{
		let mut ts = [
			$crate::t!($t1),
			$crate::t!($t2),
			$crate::t!($t3),
			$crate::t!($t4),
			$crate::t!($t5),
			$crate::t!($t6),
			$crate::t!($t7),
			$crate::t!($t8),
			$crate::t!($t9),
			$crate::t!($t10),
			$crate::t!($t11),
			$crate::t!($t12),
			$crate::t!($t13),
			$crate::t!($t14),
		];
		ts.sort_unstable();
		$crate::ScorableHand::KokushiMusou { tiles: ts, was_juusanmen_wait: true }
	}};
}

macro_rules! assert_size_of {
	($ty:ty, $size:expr) => { const _: () = [()][(std::mem::size_of::<$ty>() != $size) as usize]; };
}

mod multiset;
use multiset::MultiSet;

mod tile;
pub use tile::{
	DragonTile,
	Number, NumberSuit, NumberTile,
	Tile,
	WindTile,
};

mod scorable_hand;
pub use scorable_hand::{
	ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair,
};

mod score;
pub use score::{
	Fu,
	Han,
	Points,
	Riichi,
	Score, ScoreRaw,
	WinningTileFrom,
	Yakuman,
};

mod hand;
pub use hand::{
	Hand, HandMeld, HandStable, HandTentative,
	Minjuns, Minkous,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GameType {
	FourPlayer,
	ThreePlayer,
}

/// Indicates where the winning tile was drawn from.
///
/// This can be constructed from a [`WinningTileFrom`] with `.into()`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TsumoOrRon {
	/// The tile was drawn from the wall.
	Tsumo,
	/// The tile was taken from another player's discard or shouminkan.
	Ron,
}

fn concat<T, const N1: usize, const N2: usize>(ts1: [T; N1], ts2: [T; N2]) -> [T; N1 + N2] {
	let ts = ts1.into_iter().chain(ts2).next_chunk();
	unsafe { ts.unwrap_unchecked() }
}
