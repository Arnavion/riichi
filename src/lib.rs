#![feature(
	array_into_iter_constructors,
	cmp_minmax,
	const_clone,
	const_cmp,
	const_convert,
	const_default,
	const_destruct,
	const_drop_in_place,
	const_index,
	const_ops,
	const_range,
	const_result_unwrap_unchecked,
	const_select_unpredictable,
	const_trait_impl,
	const_try,
	coverage_attribute,
	derive_const,
	generic_const_exprs,
	maybe_uninit_array_assume_init,
	maybe_uninit_fill,
	portable_simd,
	trusted_len,
)]
#![expect(
	incomplete_features, // For generic_const_exprs
)]

#![no_std]

//! # To simulate a round
//!
//! Make an initial [`Hand`] for each player with [`make_hand`] or using [`Hand`] directly. Wrap each in [`HandStable`] using `.into()`.
//!
//! Each time a tile is drawn from the wall or discarded or made into a shouminkan, every other player checks to see if
//! their `HandStable` can use that tile to end the round (see the process of "To score a hand" below) or to form
//! [a minjun](HandStable::find_minjuns) (chii on left player's discard) or [a minkou](HandStable::find_minkous) (pon) or [an ankan](HandStable::find_ankans)
//! or [a shouminkan](HandStable::find_shouminkans) or [a daiminkan](HandStable::find_daiminkan) (kan).
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
//! For each `ScorableHand`, call [`ScorableHand::score`] to get a [`Score`] for that hand
//! that breaks down all the fu / han / yakuman for that hand, if the hand can actually score.
//! You can also call [`.into()`](ScoreAggregate::from) on the `Score` to get a [`ScoreAggregate`] that aggregates
//! all the fu / han / yakuman for that hand.
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
//! See [`max_score`] for a function to do all that in one function, and `bin/score.rs` for a code example.
//!
//! # Examples
//!
//! ## Chinroutou
//!
//! ```rust
//! # #![feature(generic_const_exprs)]
//! # #![expect(incomplete_features)]
//! # #![deny(unused)]
//! #
//! # use riichi::{
//! #     Fu,
//! #     GameType,
//! #     Han,
//! #     Points,
//! #     Riichi,
//! #     Score, ScoreAggregate,
//! #     WinningTileFrom,
//! #     Yakuman,
//! #     make_hand, make_scorable_hand,
//! #     t, tw,
//! # };
//! #
//! # // Source: https://mahjongsoul.game.yo-star.com/?paipu=251210-b014a75f-d290-4337-80af-1b024410ded1_a913354171
//! #
//! // Hand containing 11m999p99s tiles and two minkous of 111s and 111p
//! let hand = make_hand!(1m 1m 9p 9p 9p 9s 9s { minkou 1s 1s 1s } { minkou 1p 1p 1p });
//! // Add a 9s to the hand using tsumo and check for scorable hands.
//! let winning_tile_from = WinningTileFrom::Tsumo;
//! let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(9s), winning_tile_from.into()).collect();
//! assert_eq!(hands.len(), 1);
//! let hand = hands.pop_first().unwrap();
//! assert_eq!(hand, make_scorable_hand!({ minkou 1p 1p 1p } { ankou 9p 9p 9p } { minkou 1s 1s 1s } { ankou 9s 9s 9s shanpon } { 1m 1m }));
//!
//! let game_type = GameType::Yonma;
//! let dead_wall = t![S,];
//! let doras = dead_wall.map(|t| t.indicates_dora(game_type));
//! let round_wind = tw!(E);
//! let seat_wind = tw!(N);
//! let score = hand.score(
//!     &doras,
//!     round_wind,
//!     seat_wind,
//!     0,
//!     Riichi::NotRiichi,
//!     winning_tile_from,
//! ).unwrap();
//! assert_eq!(score, Score {
//!     base: Fu(20),
//!     win_condition: Fu(2),
//!     meld1: Fu(4), // { minkou 1p 1p 1p }
//!     meld2: Fu(8), // { ankou 9p 9p 9p }
//!     meld3: Fu(4), // { minkou 1s 1s 1s }
//!     meld4: Fu(8), // { ankou 9s 9s 9s }
//!     rounding: Fu(4),
//!     toitoi: Han(2),
//!     chinroutou: Yakuman(1),
//!     ..Default::default()
//! });
//!
//! assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(50), han: Han(2), yakuman: Yakuman(1) });
//!
//! let score = score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, None);
//! assert_eq!(score, Points { shimocha: 16000, toimen: 8000, kamicha: 8000, ..Default::default() });
//!
//! let score = score.total();
//! assert_eq!(score, 32000);
//! ```
//!
//! ## Sanbaiman
//!
//! ```rust
//! # #![feature(generic_const_exprs)]
//! # #![expect(incomplete_features)]
//! # #![deny(unused)]
//! #
//! # use riichi::{
//! #     Fu,
//! #     GameType,
//! #     Han,
//! #     Points,
//! #     Riichi,
//! #     Score, ScoreAggregate, SeatRelative,
//! #     WinningTileFrom,
//! #     make_hand, make_scorable_hand,
//! #     t, tw,
//! # };
//! #
//! # // Source: https://mahjongsoul.game.yo-star.com/?paipu=251104-fbcdd597-8e44-4ad9-924b-607ffc64fb97_a913354171
//! #
//! // Hand containing 2334488s555z and an ankan of EEEE
//! let hand = make_hand!(2s 3s 3s 4s 4s 8s 8s Wh Wh Wh { ankan E E E E });
//! // Add a 2s to the hand using ron and check for scorable hands.
//! let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
//! let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(2s), winning_tile_from.into()).collect();
//! assert_eq!(hands.len(), 1);
//! let hand = hands.pop_first().unwrap();
//! assert_eq!(hand, make_scorable_hand!({ anjun 2s 3s 4s } { ankou Wh Wh Wh } { ankan E E E E } { minjun 2s 3s 4s ryanmen_low } { 8s 8s }));
//!
//! let game_type = GameType::Sanma;
//! let dead_wall = t![G, 5p, 5s, 6p, S, N];
//! let doras = dead_wall.map(|t| t.indicates_dora(game_type));
//! let round_wind = tw!(E);
//! let seat_wind = tw!(S);
//! let score = hand.score(
//!     &doras,
//!     round_wind,
//!     seat_wind,
//!     0,
//!     Riichi::Riichi { ippatsu: false, double: false },
//!     winning_tile_from,
//! ).unwrap();
//! assert_eq!(score, Score {
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
//! assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(70), han: Han(11), ..Default::default() });
//!
//! let score = score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, None);
//! assert_eq!(score, Points { shimocha: 24000, ..Default::default() });
//!
//! let score = score.total();
//! assert_eq!(score, 24000);
//! ```

// Refs:
//
// - https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
// - https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175

extern crate alloc;

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
/// assert_eq!(tile, Tile::Man4);
///
/// let tile = t!(5p);
/// assert_eq!(tile, Tile::Pin5);
///
/// let tile = t!(6s);
/// assert_eq!(tile, Tile::Sou6);
///
/// // Red fives are represented by the number 0.
/// let tile = t!(0s);
/// assert_eq!(tile, Tile::Sou0);
///
/// // Wind tiles are E, S, W, N or 1z, 2z, 3z, 4z.
/// let tile = t!(E);
/// assert_eq!(tile, Tile::Ton);
/// let tile = t!(2z);
/// assert_eq!(tile, Tile::Nan);
///
/// // Dragon tiles are Wh, G, R or 5z, 6z, 7z.
/// let tile = t!(Wh);
/// assert_eq!(tile, Tile::Haku);
/// let tile = t!(6z);
/// assert_eq!(tile, Tile::Hatsu);
///
/// // Array of tiles.
/// let tiles = t![1m, 9s, E, Wh];
/// assert_eq!(tiles, [Tile::Man1, Tile::Sou9, Tile::Ton, Tile::Haku]);
///
/// // Pattern of tiles.
/// assert!(matches!(tiles[0], t!(1m | 9s)));
/// ```
#[macro_export]
macro_rules! t {
	(1m) => { $crate::Tile::Man1 };
	(2m) => { $crate::Tile::Man2 };
	(3m) => { $crate::Tile::Man3 };
	(4m) => { $crate::Tile::Man4 };
	(5m) => { $crate::Tile::Man5 };
	(0m) => { $crate::Tile::Man0 };
	(6m) => { $crate::Tile::Man6 };
	(7m) => { $crate::Tile::Man7 };
	(8m) => { $crate::Tile::Man8 };
	(9m) => { $crate::Tile::Man9 };

	(1p) => { $crate::Tile::Pin1 };
	(2p) => { $crate::Tile::Pin2 };
	(3p) => { $crate::Tile::Pin3 };
	(4p) => { $crate::Tile::Pin4 };
	(5p) => { $crate::Tile::Pin5 };
	(0p) => { $crate::Tile::Pin0 };
	(6p) => { $crate::Tile::Pin6 };
	(7p) => { $crate::Tile::Pin7 };
	(8p) => { $crate::Tile::Pin8 };
	(9p) => { $crate::Tile::Pin9 };

	(1s) => { $crate::Tile::Sou1 };
	(2s) => { $crate::Tile::Sou2 };
	(3s) => { $crate::Tile::Sou3 };
	(4s) => { $crate::Tile::Sou4 };
	(5s) => { $crate::Tile::Sou5 };
	(0s) => { $crate::Tile::Sou0 };
	(6s) => { $crate::Tile::Sou6 };
	(7s) => { $crate::Tile::Sou7 };
	(8s) => { $crate::Tile::Sou8 };
	(9s) => { $crate::Tile::Sou9 };

	(E) => { $crate::Tile::Ton };
	(1z) => { $crate::Tile::Ton };
	(S) => { $crate::Tile::Nan };
	(2z) => { $crate::Tile::Nan };
	(W) => { $crate::Tile::Shaa };
	(3z) => { $crate::Tile::Shaa };
	(N) => { $crate::Tile::Pei };
	(4z) => { $crate::Tile::Pei };

	(Wh) => { $crate::Tile::Haku };
	(5z) => { $crate::Tile::Haku };
	(G) => { $crate::Tile::Hatsu };
	(6z) => { $crate::Tile::Hatsu };
	(R) => { $crate::Tile::Chun };
	(7z) => { $crate::Tile::Chun };

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
/// assert_eq!(tile, NumberTile::Man4);
///
/// let tile = tn!(5p);
/// assert_eq!(tile, NumberTile::Pin5);
///
/// let tile = tn!(6s);
/// assert_eq!(tile, NumberTile::Sou6);
///
/// // Red fives are represented by the number 0.
/// let tile = tn!(0s);
/// assert_eq!(tile, NumberTile::Sou0);
///
/// // Array of tiles.
/// let tiles = tn![1m, 2m, 3m, 4m];
/// assert_eq!(tiles, [NumberTile::Man1, NumberTile::Man2, NumberTile::Man3, NumberTile::Man4]);
///
/// // Pattern of tiles.
/// assert!(matches!(tiles[0], tn!(1m | 2m)));
/// ```
#[macro_export]
macro_rules! tn {
	(1m) => { $crate::NumberTile::Man1 };
	(2m) => { $crate::NumberTile::Man2 };
	(3m) => { $crate::NumberTile::Man3 };
	(4m) => { $crate::NumberTile::Man4 };
	(5m) => { $crate::NumberTile::Man5 };
	(0m) => { $crate::NumberTile::Man0 };
	(6m) => { $crate::NumberTile::Man6 };
	(7m) => { $crate::NumberTile::Man7 };
	(8m) => { $crate::NumberTile::Man8 };
	(9m) => { $crate::NumberTile::Man9 };

	(1p) => { $crate::NumberTile::Pin1 };
	(2p) => { $crate::NumberTile::Pin2 };
	(3p) => { $crate::NumberTile::Pin3 };
	(4p) => { $crate::NumberTile::Pin4 };
	(5p) => { $crate::NumberTile::Pin5 };
	(0p) => { $crate::NumberTile::Pin0 };
	(6p) => { $crate::NumberTile::Pin6 };
	(7p) => { $crate::NumberTile::Pin7 };
	(8p) => { $crate::NumberTile::Pin8 };
	(9p) => { $crate::NumberTile::Pin9 };

	(1s) => {$crate::NumberTile::Sou1 };
	(2s) => {$crate::NumberTile::Sou2 };
	(3s) => {$crate::NumberTile::Sou3 };
	(4s) => {$crate::NumberTile::Sou4 };
	(5s) => {$crate::NumberTile::Sou5 };
	(0s) => {$crate::NumberTile::Sou0 };
	(6s) => {$crate::NumberTile::Sou6 };
	(7s) => {$crate::NumberTile::Sou7 };
	(8s) => {$crate::NumberTile::Sou8 };
	(9s) => {$crate::NumberTile::Sou9 };

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
/// assert_eq!(tile, ShunLowTile::Man4);
///
/// let tile = tsl!(5p);
/// assert_eq!(tile, ShunLowTile::Pin5);
///
/// let tile = tsl!(6s);
/// assert_eq!(tile, ShunLowTile::Sou6);
///
/// // Red fives are represented by the number 0.
/// let tile = tsl!(0s);
/// assert_eq!(tile, ShunLowTile::Sou0);
///
/// // Array of tiles.
/// let tiles = tsl![1m, 2m, 3m, 4m];
/// assert_eq!(tiles, [ShunLowTile::Man1, ShunLowTile::Man2, ShunLowTile::Man3, ShunLowTile::Man4]);
///
/// // Pattern of tiles.
/// assert!(matches!(tiles[0], tsl!(1m | 2m)));
/// ```
#[macro_export]
macro_rules! tsl {
	(1m) => { $crate::ShunLowTile::Man1 };
	(2m) => { $crate::ShunLowTile::Man2 };
	(3m) => { $crate::ShunLowTile::Man3 };
	(4m) => { $crate::ShunLowTile::Man4 };
	(5m) => { $crate::ShunLowTile::Man5 };
	(0m) => { $crate::ShunLowTile::Man0 };
	(6m) => { $crate::ShunLowTile::Man6 };
	(7m) => { $crate::ShunLowTile::Man7 };

	(1p) => { $crate::ShunLowTile::Pin1 };
	(2p) => { $crate::ShunLowTile::Pin2 };
	(3p) => { $crate::ShunLowTile::Pin3 };
	(4p) => { $crate::ShunLowTile::Pin4 };
	(5p) => { $crate::ShunLowTile::Pin5 };
	(0p) => { $crate::ShunLowTile::Pin0 };
	(6p) => { $crate::ShunLowTile::Pin6 };
	(7p) => { $crate::ShunLowTile::Pin7 };

	(1s) => {$crate::ShunLowTile::Sou1 };
	(2s) => {$crate::ShunLowTile::Sou2 };
	(3s) => {$crate::ShunLowTile::Sou3 };
	(4s) => {$crate::ShunLowTile::Sou4 };
	(5s) => {$crate::ShunLowTile::Sou5 };
	(0s) => {$crate::ShunLowTile::Sou0 };
	(6s) => {$crate::ShunLowTile::Sou6 };
	(7s) => {$crate::ShunLowTile::Sou7 };

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
/// assert_eq!(tile, WindTile::Ton);
/// let tile = tw!(2z);
/// assert_eq!(tile, WindTile::Nan);
///
/// // Array of tiles.
/// let tiles = tw![E, S, W, N];
/// assert_eq!(tiles, [WindTile::Ton, WindTile::Nan, WindTile::Shaa, WindTile::Pei]);
///
/// // Pattern of tiles.
/// assert!(matches!(tiles[0], tw!(E | S)));
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
/// // Dragon tiles are Wh, G, R or 5z, 6z, 7z.
/// let tile = td!(Wh);
/// assert_eq!(tile, DragonTile::Haku);
/// let tile = td!(6z);
/// assert_eq!(tile, DragonTile::Hatsu);
///
/// // Array of tiles.
/// let tiles = td![Wh, G, R];
/// assert_eq!(tiles, [DragonTile::Haku, DragonTile::Hatsu, DragonTile::Chun]);
///
/// // Pattern of tiles.
/// assert!(matches!(tiles[0], td!(Wh | G)));
/// ```
#[macro_export]
macro_rules! td {
	(Wh) => { $crate::DragonTile::Haku };
	(5z) => { $crate::DragonTile::Haku };
	(G) => { $crate::DragonTile::Hatsu };
	(6z) => { $crate::DragonTile::Hatsu };
	(R) => { $crate::DragonTile::Chun };
	(7z) => { $crate::DragonTile::Chun };

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
/// # #![feature(generic_const_exprs)]
/// # #![expect(incomplete_features)]
/// # #![deny(unused)]
/// #
/// # use riichi::{Hand, HandMeld, make_hand, t};
/// #
/// // Hand containing 2334488s555z and an ankan of EEEE
/// let hand = make_hand!(2s 3s 3s 4s 4s 8s 8s Wh Wh Wh { ankan E E E E });
/// assert_eq!(hand, Hand(
///     t![2s, 3s, 3s, 4s, 4s, 8s, 8s, Wh, Wh, Wh],
///     [
///         HandMeld::ankan(t!(E), t!(E), t!(E), t!(E)).unwrap(),
///     ],
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
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::HandMeld::minjun(t1, tiles[1], tiles[2]).unwrap()
	}};

	($t1:tt $m1:tt $m2:tt $m3:tt $m4:tt) => {
		$crate::Hand::<1, 4>(
			$crate::t![$t1,],
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
			$crate::t![$t1, $t2, $t3, $t4],
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
				$crate::make_hand!(@meld $m3),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $m1:tt $m2:tt) => {
		$crate::Hand::<7, 2>(
			$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7],
			[
				$crate::make_hand!(@meld $m1),
				$crate::make_hand!(@meld $m2),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $m1:tt) => {
		$crate::Hand::<10, 1>(
			$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10],
			[
				$crate::make_hand!(@meld $m1),
			],
		)
	};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt) => {
		$crate::Hand::<13, 0>(
			$crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13],
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
/// - `ryanmen_low` indicates that the fourth meld had a ryanmen wait and the lowest number tile completed the hand.
/// - `ryanmen_high` indicates that the fourth meld had a ryanmen wait and the highest number tile completed the hand.
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
/// # #![deny(unused)]
/// #
/// # use riichi::{
/// #     ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
/// #     TsumoOrRon,
/// #     make_scorable_hand,
/// #     t, tn, tsl,
/// # };
/// #
/// let hand = make_scorable_hand!({ anjun 2s 3s 4s } { ankou Wh Wh Wh } { ankan E E E E } { minjun 2s 3s 4s ryanmen_low } { 8s 8s });
/// assert_eq!(hand, ScorableHand::Regular(ScorableHandRegular {
///     melds: (
///         [
///             ScorableHandMeld::anjun(tsl!(2s), tn!(3s), tn!(4s)).unwrap(),
///             ScorableHandMeld::ankan(t!(E), t!(E), t!(E), t!(E)).unwrap(),
///             ScorableHandMeld::ankou(t!(Wh), t!(Wh), t!(Wh)).unwrap(),
///         ],
///         ScorableHandFourthMeld::ryanmen_low(tsl!(2s), tn!(3s), tn!(4s), TsumoOrRon::Ron).unwrap(),
///     ),
///     pair: ScorableHandPair::new(t!(8s), t!(8s)).unwrap(),
/// }));
/// ```
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{ScorableHand, ScorableHandChiitoi, ScorableHandPair, make_scorable_hand, t};
/// #
/// let hand = make_scorable_hand!({ 1m 1m } { 3m 3m } { 4m 4m } { 5p 5p } { 2s 2s } { W W } { Wh Wh });
/// assert_eq!(hand, ScorableHand::Chiitoi(ScorableHandChiitoi([
///     ScorableHandPair::new(t!(1m), t!(1m)).unwrap(),
///     ScorableHandPair::new(t!(3m), t!(3m)).unwrap(),
///     ScorableHandPair::new(t!(4m), t!(4m)).unwrap(),
///     ScorableHandPair::new(t!(5p), t!(5p)).unwrap(),
///     ScorableHandPair::new(t!(2s), t!(2s)).unwrap(),
///     ScorableHandPair::new(t!(W), t!(W)).unwrap(),
///     ScorableHandPair::new(t!(Wh), t!(Wh)).unwrap(),
/// ])));
/// ```
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{ScorableHand, ScorableHandKokushiMusou, make_scorable_hand, t};
/// #
/// let hand = make_scorable_hand!(1m 9m 1p 9p 1s 1s 9s E S W N G R Wh);
/// assert_eq!(hand, ScorableHand::KokushiMusou(ScorableHandKokushiMusou {
///     duplicate: t!(1s),
///     was_juusanmen_wait: false,
/// }));
/// ```
#[macro_export]
macro_rules! make_scorable_hand {
	(@meld { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandMeld::ankan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap()
	};

	(@meldr4 { ankan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::ankan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap())
	};

	(@meld { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandMeld::minkan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap()
	};

	(@meldr4 { minkan $t1:tt $t2:tt $t3:tt $t4:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::minkan($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::t!($t4)).unwrap())
	};

	(@meld { ankou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandMeld::ankou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap()
	};

	(@meldr4 { ankou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::ankou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap())
	};

	(@meldr4 { ankou $t1:tt $t2:tt $t3:tt shanpon }) => {
		$crate::ScorableHandFourthMeld::shanpon($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::TsumoOrRon::Tsumo).unwrap()
	};

	(@meld { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandMeld::minkou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap()
	};

	(@meldr4 { minkou $t1:tt $t2:tt $t3:tt }) => {
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::minkou($crate::t!($t1), $crate::t!($t2), $crate::t!($t3)).unwrap())
	};

	(@meldr4 { minkou $t1:tt $t2:tt $t3:tt shanpon }) => {
		$crate::ScorableHandFourthMeld::shanpon($crate::t!($t1), $crate::t!($t2), $crate::t!($t3), $crate::TsumoOrRon::Ron).unwrap()
	};

	(@meld { anjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandMeld::anjun(t1, tiles[1], tiles[2]).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::anjun(t1, tiles[1], tiles[2]).unwrap())
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt kanchan }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::kanchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt penchan }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::penchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt ryanmen_low }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::ryanmen_low(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meldr4 { anjun $t1:tt $t2:tt $t3:tt ryanmen_high }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::ryanmen_high(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Tsumo).unwrap()
	}};

	(@meld { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandMeld::minjun(t1, tiles[1], tiles[2]).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::Tanki($crate::ScorableHandMeld::minjun(t1, tiles[1], tiles[2]).unwrap())
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt kanchan }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::kanchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt penchan }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::penchan(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt ryanmen_low }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::ryanmen_low(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	(@meldr4 { minjun $t1:tt $t2:tt $t3:tt ryanmen_high }) => {{
		let mut tiles = [$crate::NumberTile::from($crate::tsl!($t1)), $crate::tn!($t2), $crate::tn!($t3)];
		$crate::SortingNetwork::sort(&mut tiles);
		let t1 = tiles[0].try_into().unwrap(); // Guaranteed to be valid because it was run through `tsl!()` above.
		$crate::ScorableHandFourthMeld::ryanmen_high(t1, tiles[1], tiles[2], $crate::TsumoOrRon::Ron).unwrap()
	}};

	($m1:tt $m2:tt $m3:tt $m4:tt { $p1:tt $p2:tt }) => {{
		let m1 = $crate::make_scorable_hand!(@meld $m1);
		let m2 = $crate::make_scorable_hand!(@meld $m2);
		let m3 = $crate::make_scorable_hand!(@meld $m3);
		let m4 = $crate::make_scorable_hand!(@meldr4 $m4);
		$crate::ScorableHand::Regular($crate::ScorableHandRegular::new(
			m1, m2, m3, m4,
			$crate::ScorableHandPair::new($crate::t!($p1), $crate::t!($p2)).unwrap(),
		))
	}};

	({ $p1:tt $p2:tt } { $p3:tt $p4:tt } { $p5:tt $p6:tt } { $p7:tt $p8:tt } { $p9:tt $p10:tt } { $p11:tt $p12:tt } { $p13:tt $p14:tt }) => {{
		let mut pairs = [
			$crate::ScorableHandPair::new($crate::t!($p1), $crate::t!($p2)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($p3), $crate::t!($p4)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($p5), $crate::t!($p6)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($p7), $crate::t!($p8)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($p9), $crate::t!($p10)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($p11), $crate::t!($p12)).unwrap(),
			$crate::ScorableHandPair::new($crate::t!($p13), $crate::t!($p14)).unwrap(),
		];
		pairs.sort_unstable();
		$crate::ScorableHand::Chiitoi($crate::ScorableHandChiitoi(pairs))
	}};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt) => {{
		let mut ts = $crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13, $t14];
		ts.sort_unstable();
		let duplicate = ts.windows(2).find_map(|ts| (ts[0] == ts[1]).then_some(ts[0])).unwrap();
		$crate::ScorableHand::KokushiMusou($crate::ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: false })
	}};

	($t1:tt $t2:tt $t3:tt $t4:tt $t5:tt $t6:tt $t7:tt $t8:tt $t9:tt $t10:tt $t11:tt $t12:tt $t13:tt $t14:tt juusanmen) => {{
		let mut ts = $crate::t![$t1, $t2, $t3, $t4, $t5, $t6, $t7, $t8, $t9, $t10, $t11, $t12, $t13, $t14];
		ts.sort_unstable();
		let duplicate = ts.windows(2).find_map(|ts| (ts[0] == ts[1]).then_some(ts[0])).unwrap();
		$crate::ScorableHand::KokushiMusou($crate::ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: true })
	}};
}

#[macro_export]
macro_rules! t27set {
	($($t:tt),* $(,)?) => {{
		let mut result = $crate::Tile27Set::default();
		$(
			result.insert($crate::tn!($t));
		)*
		result
	}};
}

#[macro_export]
macro_rules! t34set {
	($($t:tt),* $(,)?) => {{
		let mut result = $crate::Tile34Set::default();
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
	ArrayVec,
};
use array_vec::ArrayVecIntoCombinations;

mod hand;
pub use hand::{
	Ankans,
	Hand, HandAnkans, HandMeld, HandMinjuns, HandMinkous, HandShouminkans, HandStable, HandTentative,
	Hand4ScorableHands, Hand7ScorableHands, Hand10ScorableHands, HandScorableHands,
	Minjuns, Minkous,
	Shouminkans,
};

mod scorable_hand;
pub use scorable_hand::{
	ScorableHand, ScorableHandChiitoi, ScorableHandKokushiMusou, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
};
use scorable_hand::ScorableHandMeldSortCriteria;

mod score;
pub use score::{
	Fu,
	Han,
	Points, PointsAbsolute,
	Riichi,
	Score, ScoreAggregate, SeatRelative,
	WinningTileFrom,
	Yakuman,
	max_score,
};

mod tile;
pub use tile::{
	CmpIgnoreRed,
	DragonTile,
	Number, NumberTileClassified, NumberSuit, NumberTile,
	ShunLowNumber, ShunLowTile, ShunLowTileAndHasFiveRed,
	Tile,
	WindTile,
};

mod tile_multi_set;
pub use tile_multi_set::{
	TileMultiSet, TileMultiSetIntoIter, Tile27MultiSet, Tile34MultiSet, Tile37MultiSet,
	TileMultiSetElement, Tile27MultiSetElement, Tile34MultiSetElement, Tile37MultiSetElement,
};

mod tile_set;
pub use tile_set::{
	TileSet, TileSetIntoIter, Tile27Set, Tile34Set,
	TileSetElement, Tile27SetElement, Tile34SetElement,
};

#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
pub enum GameType {
	/// Standard four-player game.
	Yonma,
	/// Three-player game without a North seat.
	Sanma,
}

/// Used to identify the type of a meld when parsing an MPSZ string.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
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
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
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
// while this three-swap version fits entirely in registers, has no branches, and is shorter to boot (three / five `maxu; minu` pairs on RV).

impl SortingNetwork for [u8; 3] {
	fn sort(&mut self) {
		for (i, j) in [(0, 2), (0, 1), (1, 2)] {
			let [a, b] = core::cmp::minmax(self[i], self[j]);
			self[i] = a;
			self[j] = b;
		}
	}
}

impl SortingNetwork for [u8; 4] {
	fn sort(&mut self) {
		for (i, j) in [(0, 2), (1, 3), (0, 1), (2, 3), (1, 2)] {
			let [a, b] = core::cmp::minmax(self[i], self[j]);
			self[i] = a;
			self[j] = b;
		}
	}
}
