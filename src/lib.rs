#![no_std]

//! # To simulate a round
//!
//! Make an initial [`Hand`] for each player with [`make_hand`] or using [`Hand`] directly. Wrap each in [`HandStable`] using `.into()`.
//!
//! Each time a tile is drawn from the wall or discarded or made into a shouminkan, every other player checks to see if
//! their `HandStable` can use that tile to end the round (see the process of "To score a hand" below) or to form
//! [a minjun](HandStable::find_minjuns) (chii on left player's discard) or [a minkou](HandStable::find_minkous) (pon) or [an ankan](HandTentative::find_ankans)
//! or [a shouminkan](HandTentative::find_shouminkans) or [a daiminkan](HandStable::find_daiminkan) (kan).
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
//! Draw a tile and call [`Hand::into_scorable_hands`] or [`HandStable::into_scorable_hands`] to get a set of [`ScorableHand`]s.
//!
//! For each `ScorableHand`, call [`ScorableHand::score`] to get a [`Score`] for that hand
//! that breaks down all the fu / han / yakuman for that hand, if the hand can actually score,
//! and a [`ScoreAggregate`] that aggregates all the fu / han / yakuman for that hand.
//!
//! For each `Score`, call [`Score::score`] to get a [`Points`] value with the breakdown of points
//! taken from each seat.
//!
//! For each `Points`, call [`Points::total`] to get a total numerical point value.
//!
//! Pick the [`ScorableHand`] with the largest numerical point value.
//!
//! Call [`Points::to_absolute`] to get the change of points for each seat.
//!
//! See [`HandStable::max_score`] for a function to do all that in one function, and `bin/score.rs` for a code example.
//!
//! # Examples
//!
//! ## Chinroutou
//!
//! ```rust
//! # #![deny(unused)]
//! #
//! # use riichi::{
//! #     Fu,
//! #     GameType,
//! #     Han,
//! #     Points,
//! #     Riichi,
//! #     ScorableHand, Score, ScoreAggregate,
//! #     WinningTileFrom,
//! #     Yakuman,
//! #     make_hand, make_scorable_hand,
//! #     t, tw, t34multiset,
//! # };
//! #
//! # // Source: https://mahjongsoul.game.yo-star.com/?paipu=251210-b014a75f-d290-4337-80af-1b024410ded1_a913354171
//! #
//! // Hand containing 11m999p99s tiles and two minkous of 111s and 111p
//! let hand = make_hand!(1m 1m 9p 9p 9p 9s 9s { minkou 1s 1s 1s } { minkou 1p 1p 1p });
//! // Add a 9s to the hand using tsumo and check for scorable hands.
//! let winning_tile = t!(9s);
//! let winning_tile_from = WinningTileFrom::Tsumo;
//! let mut hands: std::collections::BTreeSet<_> = hand.into_scorable_hands(winning_tile, winning_tile_from.into()).collect();
//! assert_eq!(hands.len(), 1);
//! let hand = hands.pop_first().unwrap();
//! assert_eq!(hand, make_scorable_hand!({ minkou 1s 1s 1s } { minkou 1p 1p 1p } { ankou 9p 9p 9p } { ankou 9s 9s 9s shanpon } { 1m 1m }));
//!
//! let game_type = GameType::Yonma;
//! let rules = Default::default();
//! let dead_wall = t34multiset![S];
//! let doras = dead_wall.indicates_dora(game_type);
//! let round_wind = tw!(E);
//! let seat_wind = tw!(N);
//! let (score, score_aggregate) = ScorableHand::from(hand).score(
//!     &rules,
//!     &doras,
//!     round_wind,
//!     seat_wind,
//!     0,
//!     Riichi::NotRiichi,
//!     winning_tile,
//!     winning_tile_from,
//! ).unwrap();
//! assert_eq!(score, Score {
//!     base: Fu(20),
//!     meld1: Fu(4),
//!     meld2: Fu(4),
//!     meld3: Fu(8),
//!     meld4: Fu(8),
//!     tsumo: Fu(2),
//!     rounding: Fu(4),
//!     toitoi: Han(2),
//!     chinroutou: Yakuman(1),
//!     ..Default::default()
//! });
//!
//! assert_eq!(score_aggregate, ScoreAggregate { fu: Fu(50), han: Han(2), yakuman: Yakuman(1), ..Default::default() });
//! assert_eq!(score.to_aggregate(&rules), score_aggregate);
//!
//! let score = score.score(game_type, &Default::default(), 0, 0, seat_wind, winning_tile_from.ron_seat(), None, None);
//! assert_eq!(score, Points { shimocha: 16000, toimen: 8000, kamicha: 8000, ..Default::default() });
//!
//! let score = score.total();
//! assert_eq!(score, 32000);
//! ```
//!
//! ## Sanbaiman
//!
//! ```rust
//! # #![deny(unused)]
//! #
//! # use riichi::{
//! #     Fu,
//! #     GameType,
//! #     Han,
//! #     Points,
//! #     Riichi,
//! #     ScorableHand, Score, ScoreAggregate, SeatRelative,
//! #     WinningTileFrom,
//! #     make_hand, make_scorable_hand,
//! #     t, tw, t34multiset,
//! # };
//! #
//! # // Source: https://mahjongsoul.game.yo-star.com/?paipu=251104-fbcdd597-8e44-4ad9-924b-607ffc64fb97_a913354171
//! #
//! // Hand containing 2334488s555z and an ankan of EEEE
//! let hand = make_hand!(2s 3s 3s 4s 4s 8s 8s Wh Wh Wh { ankan E E E E });
//! // Add a 2s to the hand using ron and check for scorable hands.
//! let winning_tile = t!(2s);
//! let winning_tile_from = WinningTileFrom::Ron { seat: SeatRelative::Shimocha, tsubame_gaeshi: false };
//! let mut hands: std::collections::BTreeSet<_> = hand.into_scorable_hands(winning_tile, winning_tile_from.into()).collect();
//! assert_eq!(hands.len(), 1);
//! let hand = hands.pop_first().unwrap();
//! assert_eq!(hand, make_scorable_hand!({ ankan E E E E } { anjun 2s 3s 4s } { ankou Wh Wh Wh } { minjun 2s 3s 4s ryanmen_low } { 8s 8s }));
//!
//! let game_type = GameType::Sanma;
//! let rules = Default::default();
//! let dead_wall = t34multiset![G, 5p, 5s, 6p, S, N];
//! let doras = dead_wall.indicates_dora(game_type);
//! let round_wind = tw!(E);
//! let seat_wind = tw!(S);
//! let (score, score_aggregate) = ScorableHand::from(hand).score(
//!     &rules,
//!     &doras,
//!     round_wind,
//!     seat_wind,
//!     0,
//!     Riichi::Riichi { ippatsu: false, double: false },
//!     winning_tile,
//!     winning_tile_from,
//! ).unwrap();
//! assert_eq!(score, Score {
//!     base: Fu(20),
//!     meld1: Fu(32),
//!     meld3: Fu(8),
//!     menzen_kafu: Fu(10),
//!     riichi: Han(1),
//!     iipeikou: Han(1),
//!     yakuhai_ton: Han(1),
//!     yakuhai_haku: Han(1),
//!     honitsu: Han(3),
//!     dora: Han(4),
//!     ..Default::default()
//! });
//!
//! assert_eq!(score_aggregate, ScoreAggregate { fu: Fu(70), han: Han(11), ..Default::default() });
//! assert_eq!(score.to_aggregate(&rules), score_aggregate);
//!
//! let score = score.score(game_type, &Default::default(), 0, 0, seat_wind, winning_tile_from.ron_seat(), None, None);
//! assert_eq!(score, Points { shimocha: 24000, ..Default::default() });
//!
//! let score = score.total();
//! assert_eq!(score, 24000);
//! ```

// Refs:
//
// - https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
// - https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=30869

/// When invoked with a single token as the input, this returns a [`Tile`] corresponding to the input.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `,`, this returns an array of `Tile`s corresponding to the inputs.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `|`, this returns the same sequence with the tokens expanded to `Tile`s.
/// The expansion is usable as a pat.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{Tile, t};
/// #
/// let tile = t!(4m);
/// assert_eq!(tile, Tile::M4);
///
/// let tile = t!(5p);
/// assert_eq!(tile, Tile::P5);
///
/// let tile = t!(6s);
/// assert_eq!(tile, Tile::S6);
///
/// // Red fives are represented by the number 0.
/// let tile = t!(0s);
/// assert_eq!(tile, Tile::S0);
///
/// // Wind tiles are E, S, W, N or 1z, 2z, 3z, 4z.
/// let tile = t!(E);
/// assert_eq!(tile, Tile::Z1);
/// let tile = t!(2z);
/// assert_eq!(tile, Tile::Z2);
///
/// // Dragon tiles are Wh, G, R or P, F, C or 5z, 6z, 7z.
/// let tile = t!(Wh);
/// assert_eq!(tile, Tile::Z5);
/// let tile = t!(F);
/// assert_eq!(tile, Tile::Z6);
/// let tile = t!(7z);
/// assert_eq!(tile, Tile::Z7);
///
/// // Array of tiles.
/// let tiles = t![1m, 9s, E, Wh];
/// assert_eq!(tiles, [Tile::M1, Tile::S9, Tile::Z1, Tile::Z5]);
///
/// // Pattern of tiles.
/// core::assert_matches!(tiles[0], t!(1m | 9s));
/// ```
#[macro_export]
macro_rules! t {
	(1m) => { $crate::Tile::M1 };
	(2m) => { $crate::Tile::M2 };
	(3m) => { $crate::Tile::M3 };
	(4m) => { $crate::Tile::M4 };
	(5m) => { $crate::Tile::M5 };
	(0m) => { $crate::Tile::M0 };
	(6m) => { $crate::Tile::M6 };
	(7m) => { $crate::Tile::M7 };
	(8m) => { $crate::Tile::M8 };
	(9m) => { $crate::Tile::M9 };

	(1p) => { $crate::Tile::P1 };
	(2p) => { $crate::Tile::P2 };
	(3p) => { $crate::Tile::P3 };
	(4p) => { $crate::Tile::P4 };
	(5p) => { $crate::Tile::P5 };
	(0p) => { $crate::Tile::P0 };
	(6p) => { $crate::Tile::P6 };
	(7p) => { $crate::Tile::P7 };
	(8p) => { $crate::Tile::P8 };
	(9p) => { $crate::Tile::P9 };

	(1s) => { $crate::Tile::S1 };
	(2s) => { $crate::Tile::S2 };
	(3s) => { $crate::Tile::S3 };
	(4s) => { $crate::Tile::S4 };
	(5s) => { $crate::Tile::S5 };
	(0s) => { $crate::Tile::S0 };
	(6s) => { $crate::Tile::S6 };
	(7s) => { $crate::Tile::S7 };
	(8s) => { $crate::Tile::S8 };
	(9s) => { $crate::Tile::S9 };

	(E) => { $crate::Tile::Z1 };
	(1z) => { $crate::Tile::Z1 };
	(S) => { $crate::Tile::Z2 };
	(2z) => { $crate::Tile::Z2 };
	(W) => { $crate::Tile::Z3 };
	(3z) => { $crate::Tile::Z3 };
	(N) => { $crate::Tile::Z4 };
	(4z) => { $crate::Tile::Z4 };

	(Wh) => { $crate::Tile::Z5 };
	(P) => { $crate::Tile::Z5 };
	(5z) => { $crate::Tile::Z5 };
	(G) => { $crate::Tile::Z6 };
	(F) => { $crate::Tile::Z6 };
	(6z) => { $crate::Tile::Z6 };
	(R) => { $crate::Tile::Z7 };
	(C) => { $crate::Tile::Z7 };
	(7z) => { $crate::Tile::Z7 };

	($($t:tt),*) => { [$($crate::t!($t)),*] };
	($($t:tt ,)*) => { [$($crate::t!($t) ,)*] };
	($($t:tt)|*) => { $($crate::t!($t))|* };
}

/// When invoked with a single token as the input, this returns a [`NumberTile`] corresponding to the input.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `,`, this returns an array of `NumberTile`s corresponding to the inputs.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `|`, this returns the same sequence with the tokens expanded to `NumberTile`s.
/// The expansion is usable as a pat.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{NumberTile, tn};
/// #
/// let tile = tn!(4m);
/// assert_eq!(tile, NumberTile::M4);
///
/// let tile = tn!(5p);
/// assert_eq!(tile, NumberTile::P5);
///
/// let tile = tn!(6s);
/// assert_eq!(tile, NumberTile::S6);
///
/// // Red fives are represented by the number 0.
/// let tile = tn!(0s);
/// assert_eq!(tile, NumberTile::S0);
///
/// // Array of tiles.
/// let tiles = tn![1m, 2m, 3m, 4m];
/// assert_eq!(tiles, [NumberTile::M1, NumberTile::M2, NumberTile::M3, NumberTile::M4]);
///
/// // Pattern of tiles.
/// core::assert_matches!(tiles[0], tn!(1m | 2m));
/// ```
#[macro_export]
macro_rules! tn {
	(1m) => { $crate::NumberTile::M1 };
	(2m) => { $crate::NumberTile::M2 };
	(3m) => { $crate::NumberTile::M3 };
	(4m) => { $crate::NumberTile::M4 };
	(5m) => { $crate::NumberTile::M5 };
	(0m) => { $crate::NumberTile::M0 };
	(6m) => { $crate::NumberTile::M6 };
	(7m) => { $crate::NumberTile::M7 };
	(8m) => { $crate::NumberTile::M8 };
	(9m) => { $crate::NumberTile::M9 };

	(1p) => { $crate::NumberTile::P1 };
	(2p) => { $crate::NumberTile::P2 };
	(3p) => { $crate::NumberTile::P3 };
	(4p) => { $crate::NumberTile::P4 };
	(5p) => { $crate::NumberTile::P5 };
	(0p) => { $crate::NumberTile::P0 };
	(6p) => { $crate::NumberTile::P6 };
	(7p) => { $crate::NumberTile::P7 };
	(8p) => { $crate::NumberTile::P8 };
	(9p) => { $crate::NumberTile::P9 };

	(1s) => {$crate::NumberTile::S1 };
	(2s) => {$crate::NumberTile::S2 };
	(3s) => {$crate::NumberTile::S3 };
	(4s) => {$crate::NumberTile::S4 };
	(5s) => {$crate::NumberTile::S5 };
	(0s) => {$crate::NumberTile::S0 };
	(6s) => {$crate::NumberTile::S6 };
	(7s) => {$crate::NumberTile::S7 };
	(8s) => {$crate::NumberTile::S8 };
	(9s) => {$crate::NumberTile::S9 };

	($($t:tt),*) => { [$($crate::tn!($t)),*] };
	($($t:tt ,)*) => { [$($crate::tn!($t) ,)*] };
	($($t:tt)|*) => { $($crate::tn!($t))|* };
}

/// When invoked with a single token as the input, this returns a [`ShunLowTile`] corresponding to the input.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `,`, this returns an array of `ShunLowTile`s corresponding to the inputs.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `|`, this returns the same sequence with the tokens expanded to `ShunLowTile`s.
/// The expansion is usable as a pat.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{ShunLowTile, tsl};
/// #
/// let tile = tsl!(4m);
/// assert_eq!(tile, ShunLowTile::M4);
///
/// let tile = tsl!(5p);
/// assert_eq!(tile, ShunLowTile::P5);
///
/// let tile = tsl!(6s);
/// assert_eq!(tile, ShunLowTile::S6);
///
/// // Red fives are represented by the number 0.
/// let tile = tsl!(0s);
/// assert_eq!(tile, ShunLowTile::S0);
///
/// // Array of tiles.
/// let tiles = tsl![1m, 2m, 3m, 4m];
/// assert_eq!(tiles, [ShunLowTile::M1, ShunLowTile::M2, ShunLowTile::M3, ShunLowTile::M4]);
///
/// // Pattern of tiles.
/// core::assert_matches!(tiles[0], tsl!(1m | 2m));
/// ```
#[macro_export]
macro_rules! tsl {
	(1m) => { $crate::ShunLowTile::M1 };
	(2m) => { $crate::ShunLowTile::M2 };
	(3m) => { $crate::ShunLowTile::M3 };
	(4m) => { $crate::ShunLowTile::M4 };
	(5m) => { $crate::ShunLowTile::M5 };
	(0m) => { $crate::ShunLowTile::M0 };
	(6m) => { $crate::ShunLowTile::M6 };
	(7m) => { $crate::ShunLowTile::M7 };

	(1p) => { $crate::ShunLowTile::P1 };
	(2p) => { $crate::ShunLowTile::P2 };
	(3p) => { $crate::ShunLowTile::P3 };
	(4p) => { $crate::ShunLowTile::P4 };
	(5p) => { $crate::ShunLowTile::P5 };
	(0p) => { $crate::ShunLowTile::P0 };
	(6p) => { $crate::ShunLowTile::P6 };
	(7p) => { $crate::ShunLowTile::P7 };

	(1s) => {$crate::ShunLowTile::S1 };
	(2s) => {$crate::ShunLowTile::S2 };
	(3s) => {$crate::ShunLowTile::S3 };
	(4s) => {$crate::ShunLowTile::S4 };
	(5s) => {$crate::ShunLowTile::S5 };
	(0s) => {$crate::ShunLowTile::S0 };
	(6s) => {$crate::ShunLowTile::S6 };
	(7s) => {$crate::ShunLowTile::S7 };

	($($t:tt),*) => { [$($crate::tsl!($t)),*] };
	($($t:tt ,)*) => { [$($crate::tsl!($t) ,)*] };
	($($t:tt)|*) => { $($crate::tsl!($t))|* };
}

/// When invoked with a single token as the input, this returns a [`WindTile`] corresponding to the input.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `,`, this returns an array of `WindTile`s corresponding to the inputs.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `|`, this returns the same sequence with the tokens expanded to `WindTile`s.
/// The expansion is usable as a pat.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{WindTile, tw};
/// #
/// // Wind tiles are E, S, W, N or 1z, 2z, 3z, 4z.
/// let tile = tw!(E);
/// assert_eq!(tile, WindTile::Z1);
/// let tile = tw!(2z);
/// assert_eq!(tile, WindTile::Z2);
///
/// // Array of tiles.
/// let tiles = tw![E, S, W, N];
/// assert_eq!(tiles, [WindTile::Z1, WindTile::Z2, WindTile::Z3, WindTile::Z4]);
///
/// // Pattern of tiles.
/// core::assert_matches!(tiles[0], tw!(E | S));
/// ```
#[macro_export]
macro_rules! tw {
	(E) => { $crate::WindTile::Z1 };
	(1z) => { $crate::WindTile::Z1 };
	(S) => { $crate::WindTile::Z2 };
	(2z) => { $crate::WindTile::Z2 };
	(W) => { $crate::WindTile::Z3 };
	(3z) => { $crate::WindTile::Z3 };
	(N) => { $crate::WindTile::Z4 };
	(4z) => { $crate::WindTile::Z4 };

	($($t:tt),*) => { [$($crate::tw!($t)),*] };
	($($t:tt ,)*) => { [$($crate::tw!($t) ,)*] };
	($($t:tt)|*) => { $($crate::tw!($t))|* };
}

/// When invoked with a single token as the input, this returns a [`DragonTile`] corresponding to the input.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `,`, this returns an array of `DragonTile`s corresponding to the inputs.
/// The expansion is usable as both an expr and a pat.
///
/// When invoked with a sequence of tokens delimited by `|`, this returns the same sequence with the tokens expanded to `DragonTile`s.
/// The expansion is usable as a pat.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{DragonTile, td};
/// #
/// // Dragon tiles are Wh, G, R or P, F, C or 5z, 6z, 7z.
/// let tile = td!(Wh);
/// assert_eq!(tile, DragonTile::Z5);
/// let tile = td!(F);
/// assert_eq!(tile, DragonTile::Z6);
/// let tile = td!(7z);
/// assert_eq!(tile, DragonTile::Z7);
///
/// // Array of tiles.
/// let tiles = td![Wh, G, R];
/// assert_eq!(tiles, [DragonTile::Z5, DragonTile::Z6, DragonTile::Z7]);
///
/// // Pattern of tiles.
/// core::assert_matches!(tiles[0], td!(Wh | G));
/// ```
#[macro_export]
macro_rules! td {
	(Wh) => { $crate::DragonTile::Z5 };
	(P) => { $crate::DragonTile::Z5 };
	(5z) => { $crate::DragonTile::Z5 };
	(G) => { $crate::DragonTile::Z6 };
	(F) => { $crate::DragonTile::Z6 };
	(6z) => { $crate::DragonTile::Z6 };
	(R) => { $crate::DragonTile::Z7 };
	(C) => { $crate::DragonTile::Z7 };
	(7z) => { $crate::DragonTile::Z7 };

	($($t:tt),*) => { [$($crate::td!($t)),*] };
	($($t:tt ,)*) => { [$($crate::td!($t) ,)*] };
	($($t:tt)|*) => { $($crate::td!($t))|* };
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
/// The expansion is usable as an expr.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{Hand, HandMeld, Tile37CountedMultiSet, make_hand, t};
/// #
/// // Hand containing 2334488s555z and an ankan of EEEE
/// let hand = make_hand!(2s 3s 3s 4s 4s 8s 8s Wh Wh Wh { ankan E E E E });
/// assert_eq!(hand, Hand(
///     Tile37CountedMultiSet::new(&t![2s, 3s, 3s, 4s, 4s, 8s, 8s, Wh, Wh, Wh].into()).unwrap(),
///     [
///         HandMeld::ankan(t!(E), t!(E), t!(E), t!(E)).unwrap(),
///     ].into(),
/// ));
/// ```
#[macro_export]
macro_rules! make_hand {
	(@meld { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::HandMeld::ankan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap()
	};

	(@meld { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::HandMeld::minkan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap()
	};

	(@meld { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::HandMeld::minkou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap()
	};

	(@meld { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::HandMeld::minjun(t1, tiles[1], tiles[2]).unwrap()
	}};

	($t1:tt $m1:tt $m2:tt $m3:tt $m4:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U1, $crate::generic_array::typenum::U4>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1,].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
				$crate::make_hand!(@meld $m4),
			].into(),
		)
	};

	($t1:tt $t2:tt $m1:tt $m2:tt $m3:tt $m4:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U2, $crate::generic_array::typenum::U4>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
				$crate::make_hand!(@meld $m4),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $m1:tt $m2:tt $m3:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U4, $crate::generic_array::typenum::U3>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $m1:tt $m2:tt $m3:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U5, $crate::generic_array::typenum::U3>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $m1:tt $m2:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U7, $crate::generic_array::typenum::U2>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $m1:tt $m2:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U8, $crate::generic_array::typenum::U2>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $m1:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U10, $crate::generic_array::typenum::U1>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $m1:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U11, $crate::generic_array::typenum::U1>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11].into()).unwrap(),
			[
				$crate::make_hand!(@meld $m1),
			].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U13, $crate::generic_array::typenum::U0>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13].into()).unwrap(),
			[].into(),
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt) => {
		$crate::Hand::<$crate::generic_array::typenum::U14, $crate::generic_array::typenum::U0>(
			$crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13, $t14].into()).unwrap(),
			[].into(),
		)
	};
}

/// Creates a [`ScorableHandRegular`] or [`ScorableHandChiitoi`] or [`ScorableHandKokushiMusou`] value from the input.
///
/// Individual tiles are specified using the same tokens as what the [`t`] macro takes.
///
/// Hands are either [regular](ScorableHandRegular) (standard four-melds-one-pair shape),
/// [chiitoi](ScorableHandChiitoi) (seven-pairs shape) or
/// [kokushi musou](ScorableHandKokushiMusou) (fourteen individual tiles).
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
/// The fourth meld is specified like the first three melds, except it takes an additional optional input to specify the winning tile for the hand:
///
/// - `kanchan` indicates that the fourth meld had a kanchan wait and the kanchan tile completed the hand.
/// - `penchan` indicates that the fourth meld had a penchan wait and the penchan tile completed the hand.
/// - `ryanmen_low` indicates that the fourth meld had a ryanmen wait and the lowest number tile completed the hand.
/// - `ryanmen_high` indicates that the fourth meld had a ryanmen wait and the highest number tile completed the hand.
/// - `shanpon` indicates that the fourth meld had a shanpon wait and one of its tiles completed the hand.
/// - Not specifying any of these indicates that the fourth meld was already complete and the hand had a tanki wait.
///
/// Eg `{ anjun 1m 2m 3m penchan }` indicates this meld had a penchan wait and was completed (3m) using tsumo.
///
/// Eg `{ minjun 1m 2m 3m penchan }` indicates this meld had a penchan wait and was completed (3m) using ron.
///
/// Eg `{ minjun 1m 2m 3m }` indicates this meld was already complete, and the pair was the one that had the wait.
///
/// The final pair is specified as `{ <tile1> <tile2> }` if the wait was in the fourth meld or if it was a tanki wait won by tsumo,
/// and `{ <tile1> <tile2> ron }` if it was a tanki wait won by ron. Eg `{ R R }`, `{ Wh Wh ron }`
///
/// # Chiitoi
///
/// `make_scorable_hand!(<pair1> <pair2> <pair3> <pair4> <pair5> <pair6> <pair7>)`
///
/// Each of the seven pairs is specified as `{ <tile1> <tile2> }`. Eg `{ 1m 1m }`
/// The seventh pair is the winning pair. If it was won by ron, it is specified as `{ <tile1> <tile2> ron }`.
///
/// # Kokushi musou
///
/// `make_scorable_hand!(<tile1> <tile2> <tile3> <tile4> <tile5> <tile6> <tile7> <tile8> <tile9> <tile10> <tile11> <tile12> <tile13> <tile14> [ron])`
///
/// The fourteen tiles are listed individually. The fourteenth tile is the winning tile.
///
/// Specifying `ron` at the end indicates the hand was won by ron.
///
/// # Examples
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{
/// #     ScorableHandFourthMeld, ScorableHandMeld, ScorableHandRegular, ScorableHandRegularPair,
/// #     TsumoOrRon,
/// #     make_scorable_hand,
/// #     t, tn, tsl,
/// # };
/// #
/// let hand = make_scorable_hand!({ anjun 2s 3s 4s } { ankou Wh Wh Wh } { ankan E E E E } { minjun 2s 3s 4s ryanmen_low } { 8s 8s });
/// assert_eq!(hand, ScorableHandRegular {
///     m1: ScorableHandMeld::anjun(tsl!(2s), tn!(3s), tn!(4s)).unwrap(),
///     m2: ScorableHandMeld::ankou(t!(Wh), t!(Wh), t!(Wh)).unwrap(),
///     m3: ScorableHandMeld::ankan(t!(E), t!(E), t!(E), t!(E)).unwrap(),
///     m4: ScorableHandFourthMeld::ryanmen_low(tsl!(2s), tn!(3s), tn!(4s), TsumoOrRon::Ron).unwrap(),
///     pair: ScorableHandRegularPair::antoi(t!(8s), t!(8s)).unwrap(),
/// });
/// ```
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{ScorableHandChiitoi, ScorableHandPair, TsumoOrRon, make_scorable_hand, t};
/// #
/// let hand = make_scorable_hand!({ 1m 1m } { 3m 3m } { 4m 4m } { 5p 5p } { 2s 2s } { W W } { Wh Wh });
/// assert_eq!(hand, ScorableHandChiitoi {
///     pairs: [
///           ScorableHandPair::new(t!(1m), t!(1m)).unwrap(),
///           ScorableHandPair::new(t!(3m), t!(3m)).unwrap(),
///           ScorableHandPair::new(t!(4m), t!(4m)).unwrap(),
///           ScorableHandPair::new(t!(5p), t!(5p)).unwrap(),
///           ScorableHandPair::new(t!(2s), t!(2s)).unwrap(),
///           ScorableHandPair::new(t!(W), t!(W)).unwrap(),
///     ],
///     p7: ScorableHandPair::new(t!(Wh), t!(Wh)).unwrap(),
///     tsumo_or_ron: TsumoOrRon::Tsumo,
/// });
/// ```
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{ScorableHandKokushiMusou, TsumoOrRon, make_scorable_hand, t};
/// #
/// let hand = make_scorable_hand!(1m 9m 1p 9p 1s 1s 9s E S W N G R Wh);
/// assert_eq!(hand, ScorableHandKokushiMusou {
///     duplicate: t!(1s),
///     t14: t!(Wh),
///     tsumo_or_ron: TsumoOrRon::Tsumo,
/// });
/// ```
#[macro_export]
macro_rules! make_scorable_hand {
	(@meld { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandMeld::ankan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap()
	};

	(@meldr4 { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandFourthMeld::tanki($crate::ScorableHandMeld::ankan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap())
	};

	(@meld { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandMeld::minkan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap()
	};

	(@meldr4 { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandFourthMeld::tanki($crate::ScorableHandMeld::minkan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap())
	};

	(@meld { ankou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandMeld::ankou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap()
	};

	(@meldr4 { ankou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandFourthMeld::tanki($crate::ScorableHandMeld::ankou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap())
	};

	(@meldr4 { ankou $t1:tt $t2:tt $t3:tt shanpon }) => {
		$crate::ScorableHandFourthMeld::shanpon($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::TsumoOrRon::Tsumo).unwrap()
	};

	(@meld { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandMeld::minkou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap()
	};

	(@meldr4 { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandFourthMeld::tanki($crate::ScorableHandMeld::minkou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap())
	};

	(@meldr4 { minkou $t1:tt $t2:tt $t3:tt shanpon }) => {
		$crate::ScorableHandFourthMeld::shanpon($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::TsumoOrRon::Ron).unwrap()
	};

	(@meld { anjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandMeld::anjun(t1, tiles[1], tiles[2]).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::tanki($crate::ScorableHandMeld::anjun(t1, tiles[1], tiles[2]).unwrap())
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt kanchan }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::kanchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt penchan }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::penchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt ryanmen_low }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::ryanmen_low(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt ryanmen_high }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::ryanmen_high(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meld { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandMeld::minjun(t1, tiles[1], tiles[2]).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::tanki($crate::ScorableHandMeld::minjun(t1, tiles[1], tiles[2]).unwrap())
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt kanchan }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::kanchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt penchan }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::penchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt ryanmen_low }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::ryanmen_low(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt ryanmen_high }) => {{
		let mut tiles = [$crate::tn!($t1), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap();
		$crate::ScorableHandFourthMeld::ryanmen_high(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	($m1:tt $m2:tt $m3:tt $m4:tt { $p1:tt $p2:tt }) => {{
		let m1 = $crate::make_scorable_hand!(@meld $m1);
		let m2 = $crate::make_scorable_hand!(@meld $m2);
		let m3 = $crate::make_scorable_hand!(@meld $m3);
		let m4 = $crate::make_scorable_hand!(@meldr4 $m4);
		$crate::ScorableHandRegular::new(
			m1, m2, m3, m4,
			$crate::ScorableHandPair::new($crate::t!($p1), $crate::t!($p2)).unwrap(),
			$crate::TsumoOrRon::Tsumo,
		)
	}};

	($m1:tt $m2:tt $m3:tt $m4:tt { $p1:tt $p2:tt ron }) => {{
		let m1 = $crate::make_scorable_hand!(@meld $m1);
		let m2 = $crate::make_scorable_hand!(@meld $m2);
		let m3 = $crate::make_scorable_hand!(@meld $m3);
		let m4 = $crate::make_scorable_hand!(@meldr4 $m4);
		$crate::ScorableHandRegular::new(
			m1, m2, m3, m4,
			$crate::ScorableHandPair::new($crate::t!($p1), $crate::t!($p2)).unwrap(),
			$crate::TsumoOrRon::Ron,
		)
	}};

	({ $t1:tt $t2:tt } { $t3:tt $t4:tt } { $t5:tt $t6:tt } { $t7:tt $t8:tt } { $t9:tt $t10:tt } { $t11:tt $t12:tt } { $t13:tt $t14:tt }) => {{
		let mut pairs = [
			$crate::ScorableHandPair::new($crate::t!($t1), $crate::t!($t2)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t3), $crate::t!($t4)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t5), $crate::t!($t6)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t7), $crate::t!($t8)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t9), $crate::t!($t10)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t11), $crate::t!($t12)).unwrap(),
		];
		pairs.sort_unstable();
		let p7 = $crate::ScorableHandPair::new($crate::t!($t13), $crate::t!($t14)).unwrap();
		$crate::ScorableHandChiitoi { pairs, p7, tsumo_or_ron: $crate::TsumoOrRon::Tsumo }
	}};

	({ $t1:tt $t2:tt } { $t3:tt $t4:tt } { $t5:tt $t6:tt } { $t7:tt $t8:tt } { $t9:tt $t10:tt } { $t11:tt $t12:tt } { $t13:tt $t14:tt ron }) => {{
		let mut pairs = [
			$crate::ScorableHandPair::new($crate::t!($t1), $crate::t!($t2)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t3), $crate::t!($t4)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t5), $crate::t!($t6)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t7), $crate::t!($t8)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t9), $crate::t!($t10)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($t11), $crate::t!($t12)).unwrap(),
		];
		pairs.sort_unstable();
		let p7 = $crate::ScorableHandPair::new($crate::t!($t13), $crate::t!($t14)).unwrap();
		$crate::ScorableHandChiitoi { pairs, p7, tsumo_or_ron: $crate::TsumoOrRon::Ron }
	}};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt) => {{
		let ts = $crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13].into()).unwrap();
		$crate::ScorableHandKokushiMusou::new(&ts, $crate::t!($t14), $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt ron) => {{
		let ts = $crate::Tile37CountedMultiSet::new(&$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13].into()).unwrap();
		$crate::ScorableHandKokushiMusou::new(&ts, $crate::t!($t14), $crate::TsumoOrRon::Ron).unwrap()
	}};
}

/// Constructs a [`Tile27Set`] containing the given tiles.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{tn, t27set};
/// #
/// let set = t27set![5m, 5p, 5s];
/// let tiles: Vec<_> = set.into_iter().collect();
/// assert_eq!(&tiles, &tn![5m, 5p, 5s]);
/// ```
#[macro_export]
macro_rules! t27set {
	($($t:tt),* $(,)?) => { const {
		#[allow(unused_mut)]
		let mut result = $crate::Tile27Set::new();
		$(
			result.insert($crate::tn!($t));
		)*
		result
	}};
}

/// Constructs a [`Tile34Set`] containing the given tiles.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{t, t34set};
/// #
/// let set = t34set![5m, 5p, 5s, E, Wh];
/// let tiles: Vec<_> = set.into_iter().collect();
/// assert_eq!(&tiles, &t![5m, 5p, 5s, E, Wh]);
/// ```
#[macro_export]
macro_rules! t34set {
	($($t:tt),* $(,)?) => { const {
		#[allow(unused_mut)]
		let mut result = $crate::Tile34Set::new();
		$(
			result.insert($crate::t!($t));
		)*
		result
	}};
}

/// Constructs a [`Tile37Set`] containing the given tiles.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{t, t37set};
/// #
/// let set = t37set![5m, 0m, 5p, 0p, 5s, 0s, E, Wh];
/// let tiles: Vec<_> = set.into_iter().collect();
/// assert_eq!(&tiles, &t![5m, 0m, 5p, 0p, 5s, 0s, E, Wh]);
/// ```
#[macro_export]
macro_rules! t37set {
	($($t:tt),* $(,)?) => { const {
		#[allow(unused_mut)]
		let mut result = $crate::Tile37Set::new();
		$(
			result.insert($crate::t!($t));
		)*
		result
	}};
}

/// Constructs a [`Tile27MultiSet`] containing the given tiles.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use std::num::NonZero;
/// # use riichi::{tn, t27multiset};
/// #
/// let set = t27multiset![5m, 5m, 5m, 5m, 5p, 5p, 5p, 5p, 5s, 5s, 5s, 5s];
/// let tiles: Vec<_> = set.into_iter().collect();
/// assert_eq!(&tiles, &[
///     (tn!(5m), NonZero::new(4).unwrap()),
///     (tn!(5p), NonZero::new(4).unwrap()),
///     (tn!(5s), NonZero::new(4).unwrap()),
/// ]);
/// ```
#[macro_export]
macro_rules! t27multiset {
	($($t:tt),* $(,)?) => { const {
		#[allow(unused_mut)]
		let mut result = $crate::Tile27MultiSet::new();
		$(
			result.insert($crate::tn!($t));
		)*
		result
	}};
}

/// Constructs a [`Tile34MultiSet`] containing the given tiles.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use std::num::NonZero;
/// # use riichi::{t, t34multiset};
/// #
/// let set = t34multiset![5m, 5m, 5m, 5m, 5p, 5p, 5p, 5p, 5s, 5s, 5s, 5s, E, E, E, E, Wh, Wh, Wh, Wh];
/// let tiles: Vec<_> = set.into_iter().collect();
/// assert_eq!(&tiles, &[
///     (t!(5m), NonZero::new(4).unwrap()),
///     (t!(5p), NonZero::new(4).unwrap()),
///     (t!(5s), NonZero::new(4).unwrap()),
///     (t!(E), NonZero::new(4).unwrap()),
///     (t!(Wh), NonZero::new(4).unwrap()),
/// ]);
/// ```
#[macro_export]
macro_rules! t34multiset {
	($($t:tt),* $(,)?) => { const {
		#[allow(unused_mut)]
		let mut result = $crate::Tile34MultiSet::new();
		$(
			result.insert($crate::t!($t));
		)*
		result
	}};
}

/// Constructs a [`Tile37MultiSet`] containing the given tiles.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use std::num::NonZero;
/// # use riichi::{t, t37multiset};
/// #
/// let set = t37multiset![5m, 5m, 5m, 0m, 5p, 5p, 5p, 0p, 5s, 5s, 5s, 0s, E, E, E, E, Wh, Wh, Wh, Wh];
/// let tiles: Vec<_> = set.into_iter().collect();
/// assert_eq!(&tiles, &[
///     (t!(5m), NonZero::new(3).unwrap()),
///     (t!(0m), NonZero::new(1).unwrap()),
///     (t!(5p), NonZero::new(3).unwrap()),
///     (t!(0p), NonZero::new(1).unwrap()),
///     (t!(5s), NonZero::new(3).unwrap()),
///     (t!(0s), NonZero::new(1).unwrap()),
///     (t!(E), NonZero::new(4).unwrap()),
///     (t!(Wh), NonZero::new(4).unwrap()),
/// ]);
/// ```
#[macro_export]
macro_rules! t37multiset {
	($($t:tt),* $(,)?) => { const {
		#[allow(unused_mut)]
		let mut result = $crate::Tile37MultiSet::new();
		$(
			result.insert($crate::t!($t));
		)*
		result
	}};
}

macro_rules! assert_size_of {
	($ty:ty, $size:expr) => { const _: () = if core::mem::size_of::<$ty>() != $size { let _: () = [][core::mem::size_of::<$ty>()]; }; };
}

mod array_vec;
pub use array_vec::{
	ArrayVec, ArrayVecIntoIter,
};

mod decompose;

mod hand;
pub use hand::{
	Ankans,
	Hand, HandAnkans, HandMeld, HandMinjuns, HandMinkous, HandScorableHands, HandShouminkans, HandStable, HandTentative,
	Hand4ScorableHands,
	Hand7ScorableHands,
	Hand10ScorableHands,
	Hand13ScorableHands,
	Hand14ScorableHands,
	Minjuns, Minkous,
	Shouminkans,
};

mod scorable_hand;
pub use scorable_hand::{
	KanWait, KouWait,
	ScorableHand,
	ScorableHandChiitoi,
	ScorableHandFourthMeld,
	ScorableHandKokushiMusou,
	ScorableHandMeld,
	ScorableHandPair,
	ScorableHandRegular, ScorableHandRegularPair, ScorableHandRegularPairTag,
	ShunWait,
};

mod score;
pub use score::{
	Fu,
	Han,
	Points, PointsAbsolute,
	Riichi, Rules, RulesDoubleWindPair, RulesRenhou,
	Score, ScoreAggregate, SeatRelative,
	WinningTileFrom,
	Yakuman,
};

mod tile;
pub use tile::{
	CmpIgnoreRed,
	DragonTile,
	KanKouToiTile,
	Number, NumberTileClassified, NumberSuit, NumberTile,
	ShunLowNumber, ShunLowTile, ShunTile,
	Tile,
	WindTile,
};

mod tile_multi_set;
pub use tile_multi_set::{
	Tile27MultiSet, Tile27MultiSetIntoIter,
	Tile34MultiSet, Tile34MultiSetIntoIter,
	Tile37MultiSet, Tile37MultiSetIntoIter,
	Tile37CountedMultiSet,
};

mod tile_set;
pub use tile_set::{
	Tile27Set, Tile27SetIntoIter,
	Tile34Set, Tile34SetIntoIter,
	Tile37Set, Tile37SetIntoIter,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GameType {
	/// Standard four-player game.
	Yonma,
	/// Three-player game without a North seat.
	Sanma,
}

/// Used to identify the type of a meld when parsing an MPSZ string.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HandMeldType {
	/// An ankan, indicated by `+`.
	Ankan,
	/// A shouiminkan, indicated by `=`.
	Shouminkan,
	/// A minjun or minkou or daiminkan, indicated by `-`.
	MinjunMinkouDaiminkan,
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

/// Optimized sorting for some specific types.
pub trait SortingNetwork {
	fn sort(&mut self);
}

// Micro-optimization: `arr.sort_unstable()` generates excessively verbose code as of Rust 1.91 and contemporary nightly,
// because the impl uses insertion sort for all array sizes between 2 and 20.
//
// Specifically, on both x86_64 and RV, the `sort_unstable` codegen ends up using stack space and has many branches,
// while this sorting network version fits entirely in registers, has no branches, and is shorter to boot (three / five `maxu; minu` pairs on RV).

impl<T> SortingNetwork for [T; 1] {
	fn sort(&mut self) {}
}

impl<T> SortingNetwork for [T; 2]
where
	T: Copy + Ord,
{
	fn sort(&mut self) {
		(self[0], self[1]) = (self[0].min(self[1]), self[0].max(self[1]));
	}
}

impl<T> SortingNetwork for [T; 3]
where
	T: Copy + Ord,
{
	fn sort(&mut self) {
		for (i, j) in [(0, 2), (0, 1), (1, 2)] {
			(self[i], self[j]) = (self[i].min(self[j]), self[i].max(self[j]));
		}
	}
}

impl<T> SortingNetwork for [T; 4]
where
	T: Copy + Ord,
{
	fn sort(&mut self) {
		for (i, j) in [(0, 2), (1, 3), (0, 1), (2, 3), (1, 2)] {
			(self[i], self[j]) = (self[i].min(self[j]), self[i].max(self[j]));
		}
	}
}

// TODO(rustup): Replace this with `uN::extract_bits` if it starts generating as efficient code as this.
macro_rules! make_extract_bits {
	($(fn $name:ident ($ty:ty) { $x86_64_intrinsic:path })*) => {
		$(
			#[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
			#[doc = concat!("Equivalent to [`", stringify!($ty), "::extract_bits`] but requires that the bits to be extracted are the `WIDTH` contiguous bits at indices")]
			/// `START`, `START + REPEAT`, `START + 2 * REPEAT`, ... `START + (N - 1) * REPEAT`, and all other bits are `0`.
			fn $name<const START: u8, const WIDTH: u8, const REPEAT: u8, const N: u8>(x: $ty) -> $ty {
				const { assert!(N == 0 || (WIDTH > 0 && WIDTH <= REPEAT && (START as u32) + (N as u32 - 1) * (REPEAT as u32) + (WIDTH as u32) <= <$ty>::BITS)); }

				if N == 0 {
					return x;
				}

				let mask: $ty = const {
					let group: $ty = if (WIDTH as u32) >= <$ty>::BITS { <$ty>::MAX } else { (0b1 << WIDTH) - 1 };
					let mut mask = 0;
					let mut i = 0;
					while i < N {
						mask |= group << (i * REPEAT);
						i += 1;
					}
					mask << START
				};

				unsafe { $x86_64_intrinsic(x, mask) }
			}

			#[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
			#[doc = concat!("Equivalent to [`", stringify!($ty), "::extract_bits`] but requires that the bits to be extracted are the `WIDTH` contiguous bits at indices")]
			/// `START`, `START + REPEAT`, `START + 2 * REPEAT`, ... `START + (N - 1) * REPEAT`, and all other bits are `0`.
			/// That assumption enables this method to generate more efficient code than the libcore method.
			const fn $name<const START: u8, const WIDTH: u8, const REPEAT: u8, const N: u8>(x: $ty) -> $ty {
				// After `let mut x = x >> START;` below, the bits to be extracted are groups of `WIDTH` contiguous bits at indices `i * REPEAT`.
				//
				// In each step, there are groups of `w * WIDTH` contiguous bits spaced `w * REPEAT` bits apart. Every second group is shifted down by `w * (REPEAT - WIDTH)` bits,
				// so that it merges into the previous group. This results in groups of `2 * w * WIDTH` contiguous bits spaced `2 * w * REPEAT` bits apart.
				// Then double `w` for the next step.
				//
				// If `2 * WIDTH <= REPEAT`, that means a block of `REPEAT` bits extracts fewer or same number of bits (`WIDTH`) than not (`REPEAT - WIDTH`).
				// This means the merge process can just shift `x` down, `|` the shifted `x` with the unshifted `x`, and apply a mask of `2 * WIDTH` groups to retain the merged groups.
				// The `|` is sure to operate on set bits in one operand and zero bits in the other so there will never be any interaction between set bits in both operands.
				//
				//    START = 0, WIDTH = 1, REPEAT = 3, N = 4
				//                                      x = 0b00a_00b_00c_00d
				//                               (x >> 2) = 0b000_0a0_0b0_0c0
				//                           x | (x >> 2) = 0b00a_0ab_0bc_0cd
				//     (x | (x >> 2)) & 0b000_011_000_011 = 0b000_0ab_000_0cd
				//
				// But if `2 * WIDTH > REPEAT`, that means the `|` would end up merging some set bits from both operands, which would produce garbage.
				// In this case we need to first mask the inputs to retain only the shifted bits in the shifted `x` and the unshifted bits in the unshifted `x`.
				//
				//    START = 0, WIDTH = 2, REPEAT = 3, N = 4
				//                                      x = 0b0ab_0cd_0ef_0gh
				//                         masked_shifted = (x & !0b000_011_000_011) >> 1 = 0b00a_b00_00e_f00
				//                       masked_unshifted = x & 0b000_011_000_011         = 0b000_0cd_000_0gh
				//      masked_shifted | masked_unshifted = 0b00a_bcd_00e_fgh

				const MAX_STEPS: usize = <$ty>::BITS.ilog2() as usize;

				const { assert!(N == 0 || (WIDTH > 0 && WIDTH <= REPEAT && (START as u32) + (N as u32 - 1) * (REPEAT as u32) + (WIDTH as u32) <= <$ty>::BITS)); }

				if N == 0 {
					return x;
				}

				let mut x = x >> START;

				// This is calculated separately from the loop that applies the operations to `x` so that it can be inside a `const` block,
				// which guarantees that it is computed at compile-time.
				let (mask_before_shifting, num_steps, masks) = const {
					let mask_before_shifting = 2 * WIDTH > REPEAT;

					let num_steps =
						if REPEAT > 1 {
							N.next_power_of_two().trailing_zeros() as usize
						}
						else {
							0
						};

					let mut masks: [$ty; _] = [0; MAX_STEPS];
					let mut i = 0;
					while i < num_steps {
						let w = 0b1_u32 << i;
						let group_width = if mask_before_shifting { 1 } else { 2 } * w * (WIDTH as u32);
						let group: $ty = (0b1 << group_width) - 1;
						let stride = 2 * w * (REPEAT as u32);
						let mut pos = 0;
						while pos < <$ty>::BITS {
							masks[i] |= group << pos;
							pos += stride;
						}
						i += 1;
					}

					(mask_before_shifting, num_steps, masks)
				};
				let mut i = 0;
				while i < num_steps {
					let shift = (0b1 << i) * (REPEAT - WIDTH);
					let mask = masks[i];
					x =
						if mask_before_shifting {
							(x & mask) | ((x & !mask) >> shift)
						}
						else {
							(x | (x >> shift)) & mask
						};
					i += 1;
				}

				x
			}
		)*
	};
}

make_extract_bits! {
	fn extract_bits32(u32) { core::arch::x86_64::_pext_u32 }
	fn extract_bits64(u64) { core::arch::x86_64::_pext_u64 }
}

// Used by `make_hand!` expansion.
pub use generic_array;
