use generic_array::{
	ArrayLength,
	GenericArray,
	sequence::{Concat as _, Remove},
	typenum::{
		Diff, Sum,
		U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14,
	},
};

use crate::{
	ArrayVec, ArrayVecIntoCombinations, ArrayVecIntoIter,
	CmpIgnoreRed,
	GameType,
	HandMeldType,
	KouWait,
	NumberTile,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandMeldSortCriteria, ScorableHandPair, ScorableHandRegular, ScorableHandRegularPair, ScorableHandRegularPairTag,
	ShunLowNumber, ShunLowTile, ShunLowTileAndHasFiveRed, ShunWait, SortingNetwork,
	Tile, Tile34MultiSet, Tile34MultiSetElement, Tile34Set, TileMultiSetIntoIter, TsumoOrRon,
};

/// A hand containing some number of tiles and melds.
///
/// This time is parameterized by the number of tiles `NT` and the number of melds `NM`.
/// Chii / pon / kan calls consume the type and return a new one with a different `NT` and `NM`.
/// If you want to hold all possible hands in a single type, use the [`HandStable`] and [`HandTentative`] enums.
///
/// It is possible to construct `Hand`s with arbitrary number of tiles and melds. However, operations like
/// [`find_minjuns`][Self::find_minjuns], [`discard`][Self::discard], [`to_scorable_hands`][Self::to_scorable_hands], etc
/// are only defined on specific instantiations of `Hand` that would appear in a game. See the implementations of `From`
/// for [`HandStable`] and [`HandTentative`].
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means:
///
/// - All [`HandMeld`]s are themselves consistent. See its docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Eq, PartialEq)]
pub struct Hand<NT, NM>(
	pub GenericArray<Tile, NT>,
	pub GenericArray<HandMeld, NM>,
) where
	NT: ArrayLength,
	NM: ArrayLength,
;

/// A single meld inside a [`Hand`].
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means:
///
/// - `Ankan` and `Minkan` really contain four of the same [`Tile`], except that if three of them are [`Number::Five`][crate::Number::Five]s
///   then the fourth may be a [`Number::FiveRed`][crate::Number::FiveRed].
///
/// - `Minkou` really contains three of the same [`Tile`], except that if two of them are [`Number::Five`][crate::Number::Five]s
///   then the third may be a [`Number::FiveRed`][crate::Number::FiveRed].
///
/// - `Minjun` really contains three [`NumberTile`]s that would form a valid sequence.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(C, u8, align(2))]
pub enum HandMeld {
	/// Closed quad formed by kan.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Ankan(Tile) = 0,

	/// Open quad formed by kan.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkan(Tile) = 1,

	/// Open triplet formed by pon.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkou(Tile) = 3,

	/// Open sequence formed by chii.
	Minjun(ShunLowTileAndHasFiveRed) = 5,
}

/// A hand containing some number of tiles and melds when it's not the player's turn.
///
/// This enum is a way to hold all possible stable hand types during a game.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HandStable {
	/// A hand containing 1 tile and 4 melds.
	One(Hand<U1, U4>),

	/// A hand containing 4 tiles and 3 melds.
	Four(Hand<U4, U3>),

	/// A hand containing 7 tiles and 2 melds.
	Seven(Hand<U7, U2>),

	/// A hand containing 10 tiles and 1 meld.
	Ten(Hand<U10, U1>),

	/// A hand containing 13 tiles.
	Thirteen(Hand<U13, U0>),
}

/// A hand containing some number of tiles and melds when it's the player's turn.
/// This has an extra tile that must be discarded using [`discard`][HandTentative::discard]
/// to return to a [`HandStable`].
///
/// This enum is a way to hold all possible tentative hand types during a game.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HandTentative {
	/// A hand containing 2 tiles and 4 melds.
	Two(Hand<U2, U4>),

	/// A hand containing 5 tiles and 3 melds.
	Five(Hand<U5, U3>),

	/// A hand containing 8 tiles and 2 melds.
	Eight(Hand<U8, U2>),

	/// A hand containing 11 tiles and 1 meld.
	Eleven(Hand<U11, U1>),

	/// A hand containing 14 tiles.
	Fourteen(Hand<U14, U0>),
}

assert_size_of!(Hand<U1, U4>, 10);
assert_size_of!(Hand<U2, U4>, 10);
assert_size_of!(Hand<U4, U3>, 10);
assert_size_of!(Hand<U5, U3>, 12);
assert_size_of!(Hand<U7, U2>, 12);
assert_size_of!(Hand<U8, U2>, 12);
assert_size_of!(Hand<U10, U1>, 12);
assert_size_of!(Hand<U11, U1>, 14);
assert_size_of!(Hand<U13, U0>, 14);
assert_size_of!(Hand<U14, U0>, 14);
assert_size_of!(HandMeld, 2);

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	NM: ArrayLength,
	HandStable: From<Self>,
{
	/// Draw the given tile into this stable hand to form a tentative hand.
	pub fn draw(self, new_tile: Tile) -> Hand<Sum<NT, U1>, NM> {
		let Self(ts, ms) = self;
		let ts = ts.concat([new_tile].into());
		Hand(ts, ms)
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>,
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Copy,
	HandStable: From<Self>,
{
	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NM + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<Diff<NT, U3>, Sum<NM, U1>>> {
		let Self(ts, ms) = self;
		find_daiminkan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, ms.concat([m_new].into())))
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	HandStable: From<Self>,
{
	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> Minkous<NT, NM> {
		Minkous::new(self, new_tile)
	}

	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> Minjuns<NT, NM> {
		Minjuns::new(self, new_tile)
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Remove<Tile, NT, Output = GenericArray<Tile, Diff<NT, U1>>>,
	NM: ArrayLength,
	HandTentative: From<Hand<NT, NM>>,
{
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile, and the discarded tile.
	///
	/// # Panics
	///
	/// Panics if the given index is not within bounds.
	pub fn discard(self, i: usize) -> (Hand<Diff<NT, U1>, NM>, Tile) {
		let Self(ts, ms) = self;
		let (t_discard, ts) = ts.remove(i);
		(Hand(ts, ms), t_discard)
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>,
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Copy,
	HandTentative: From<Self>,
{
	/// Find all possible ankans (quad via kan call on a quad held in the hand).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_ankans(self) -> Ankans<NT, NM> {
		Ankans::new(self)
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	HandTentative: From<Self>,
{
	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_shouminkans(self) -> Shouminkans<NT, NM> {
		Shouminkans::new(self)
	}
}

#[expect(clippy::expl_impl_clone_on_copy)]
impl<NT, NM> Clone for Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	fn clone(&self) -> Self {
		*self
	}
}

impl<NT, NM> Copy for Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{}

impl<NT, NM> core::fmt::Debug for Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: core::fmt::Display,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl<NT, NM> core::fmt::Display for Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self(ts, ms) = self;
		if let Some((t1, ts_rest)) = ts.split_first() {
			write!(f, "{t1}")?;
			for t in ts_rest {
				write!(f, " {t}")?;
			}
			for m in ms {
				write!(f, " {m}")?;
			}
		}
		else if let Some((m1, ms_rest)) = ms.split_first() {
			write!(f, "{m1}")?;
			for m in ms_rest {
				write!(f, " {m}")?;
			}
		}
		Ok(())
	}
}

impl Hand<U1, U4> {
	/// Add the given drawn / called tile to this hand and convert it into a [`ScorableHand`] if one exists.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Returns `None` if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hand(self, new_tile: Tile) -> Option<ScorableHand> {
		let Self(ts, ms) = self;
		let [t1] = ts.into();

		let pair = ScorableHandPair::new(t1, new_tile)?;
		let [ma, mb, mc, md] = <[HandMeld; _]>::from(ms).map(Into::into);
		Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, ScorableHandFourthMeld::tanki(md), pair)))
	}

	/// Returns the [`Tile`] that would complete this hand.
	pub fn tenpai(self) -> Tile {
		// A hand is considered to be in tenpai even if all extant copies of a tile are available in the hand, as long as those copies are not present solely in the unmelded tiles (`self.0`).
		//
		// Eg, if `self` is `(t![1m, 1m, 1m, 1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [])`, this requires a fifth `1m` to form a valid shape
		// `{ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there are already four copies of `1m` in `self.0`, `self` is not considered to be in tenpai for a 1m.
		//
		// If `self` is `(t![1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [make_hand!(@meld { minkou 1m 1m 1m })])`, this requires a fifth `1m` to form a valid shape
		// `{ minkou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there is only one copy of 1m in `self.0` (the other three are in `self.1`), `self` is considered to be in tenpai for a 1m.
		//
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.

		let Self(ts, _) = self;
		let [t1] = ts.into();
		t1.remove_red()
	}
}

impl Hand<U4, U3> {
	/// Add the given drawn / called tile to this hand and convert it into an `Iterator` of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	///
	/// If no scorable hand can be formed with the new tile, the iterator will be empty.
	///
	/// The iterator may contain multiple instances of the same hand. You may want to collect it into a `BTreeSet` or similar
	/// before doing further computation on it. Note again that the order of scorable hands in the set will not have anything to do with
	/// the scorable hands' scores.
	///
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akadora
	/// does not make any difference to the final score. For example a hand `233445550p567m88s` can form both `234p 345p 550p 567m 88s` and `234p 340p 555p 567m 88s`,
	/// but only one is guaranteed to be yielded.
	///
	/// Scorable hands that differ in the wait *are* considered distinct. For example a hand 23344450p567m88s + 3p can form the following scorable hands:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { anjun 3p 4p 0p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 2p 3p 4p kanchan } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Hand4ScorableHands {
		let Self(ts, ms) = self;

		let mut ts = ts.concat([new_tile].into());
		SortingNetwork::sort(&mut ts);
		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		let [ma, mb, mc] = <[HandMeld; _]>::from(ms).map(Into::into);

		Hand4ScorableHands { pairs, ma, mb, mc }
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> Hand4Tenpai {
		// A hand is considered to be in tenpai even if all extant copies of a tile are available in the hand, as long as those copies are not present solely in the unmelded tiles (`self.0`).
		//
		// Eg, if `self` is `(t![1m, 1m, 1m, 1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [])`, this requires a fifth `1m` to form a valid shape
		// `{ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there are already four copies of `1m` in `self.0`, `self` is not considered to be in tenpai for a 1m.
		//
		// If `self` is `(t![1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [make_hand!(@meld { minkou 1m 1m 1m })])`, this requires a fifth `1m` to form a valid shape
		// `{ minkou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there is only one copy of 1m in `self.0` (the other three are in `self.1`), `self` is considered to be in tenpai for a 1m.
		//
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.

		let tiles = Tile::each(game_type).iter();
		let Self(mut ts, _) = self;
		SortingNetwork::sort(&mut ts);
		Hand4Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand4ScorableHands {
	pairs: ScorableHandPairs<U5>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
	mc: ScorableHandMeld,
}

assert_size_of!(Hand4ScorableHands, 48);

impl Iterator for Hand4ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (pair, rest, new_tile_i) = self.pairs.next()?;
			let [t1, t2, t3] = rest.into();
			// SAFETY: `new_tile_i` is guaranteed to be `None` or `Some((0..=2, _))` by the implementation of `ScorableHandPairs`.
			let Some(md) = (unsafe { to_meld(t1, t2, t3, new_tile_i) }) else { continue; };
			break Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, self.mb, self.mc, md, pair)));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.pairs.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Hand4ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand4Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	ts: GenericArray<Tile, U4>,
}

assert_size_of!(Hand4Tenpai, 24);

impl Iterator for Hand4Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			let num_in_ts = self.ts.iter().filter(|t| t.eq_ignore_red(&new_tile)).count();
			if num_in_ts == 4 {
				continue;
			}
			let ts = insert_sorted(&self.ts, new_tile);
			let new_tile_i = ts.iter().position(|&t| t == new_tile);
			// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
			let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, TsumoOrRon::Tsumo);
			let pairs = ScorableHandPairs::new(ts, new_tile_i);
			for (_, rest, new_tile_i) in pairs {
				let [t1, t2, t3] = rest.into();
				// SAFETY: `new_tile_i` is guaranteed to be `None` or `Some((0..=2, _))` by the implementation of `ScorableHandPairs`.
				if (unsafe { to_meld(t1, t2, t3, new_tile_i) }).is_some() {
					return Some(new_tile);
				}
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Hand4Tenpai {}

impl Hand<U7, U2> {
	/// Add the given drawn / called tile to this hand and convert it into an `Iterator` of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	///
	/// If no scorable hand can be formed with the new tile, the iterator will be empty.
	///
	/// The iterator may contain multiple instances of the same hand. You may want to collect it into a `BTreeSet` or similar
	/// before doing further computation on it. Note again that the order of scorable hands in the set will not have anything to do with
	/// the scorable hands' scores.
	///
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akadora
	/// does not make any difference to the final score. For example a hand `233445550p567m88s` can form both `234p 345p 550p 567m 88s` and `234p 340p 555p 567m 88s`,
	/// but only one is guaranteed to be yielded.
	///
	/// Scorable hands that differ in the wait *are* considered distinct. For example a hand 23344450p567m88s + 3p can form the following scorable hands:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { anjun 3p 4p 0p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 2p 3p 4p kanchan } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Hand7ScorableHands {
		let Self(ts, ms) = self;

		let mut ts = ts.concat([new_tile].into());
		ts.sort_unstable();
		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		let [ma, mb] = <[HandMeld; _]>::from(ms).map(Into::into);

		Hand7ScorableHands {
			pair: None,
			mcds: Default::default(),
			pairs,
			ma,
			mb,
		}
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> Hand7Tenpai {
		// A hand is considered to be in tenpai even if all extant copies of a tile are available in the hand, as long as those copies are not present solely in the unmelded tiles (`self.0`).
		//
		// Eg, if `self` is `(t![1m, 1m, 1m, 1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [])`, this requires a fifth `1m` to form a valid shape
		// `{ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there are already four copies of `1m` in `self.0`, `self` is not considered to be in tenpai for a 1m.
		//
		// If `self` is `(t![1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [make_hand!(@meld { minkou 1m 1m 1m })])`, this requires a fifth `1m` to form a valid shape
		// `{ minkou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there is only one copy of 1m in `self.0` (the other three are in `self.1`), `self` is considered to be in tenpai for a 1m.
		//
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.

		let tiles = Tile::each(game_type).iter();
		let Self(mut ts, _) = self;
		ts.sort_unstable();
		Hand7Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand7ScorableHands {
	pair: Option<ScorableHandPair>,
	mcds: Dedup<Melds2>,
	pairs: ScorableHandPairs<U8>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
}

assert_size_of!(Hand7ScorableHands, 192);

impl Iterator for Hand7ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let pair =
				if let Some(pair) = self.pair {
					pair
				}
				else {
					let (pair, rest, new_tile_i) = self.pairs.next()?;
					self.mcds = Dedup::new(Melds2::new(rest, new_tile_i));
					*self.pair.insert(pair)
				};

			let Some((mc, md)) = self.mcds.next() else {
				self.pair = None;
				continue;
			};

			break Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, self.mb, mc, md, pair)));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.pairs.size_hint() == (0, Some(0)) {
			let (_, hi) = self.mcds.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl core::iter::FusedIterator for Hand7ScorableHands where Dedup<Melds2>: core::iter::FusedIterator {}

#[derive(Clone, Debug)]
pub struct Hand7Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	ts: GenericArray<Tile, U7>,
}

assert_size_of!(Hand7Tenpai, 24);

impl Iterator for Hand7Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			let num_in_ts = self.ts.iter().filter(|t| t.eq_ignore_red(&new_tile)).count();
			if num_in_ts == 4 {
				continue;
			}
			let ts = insert_sorted(&self.ts, new_tile);
			let new_tile_i = ts.iter().position(|&t| t == new_tile);
			// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
			let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, TsumoOrRon::Tsumo);
			for (_, rest, new_tile_i) in ScorableHandPairs::new(ts, new_tile_i) {
				if Melds2::new(rest, new_tile_i).next().is_some() {
					return Some(new_tile);
				}
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Hand7Tenpai {}

impl Hand<U10, U1> {
	/// Add the given drawn / called tile to this hand and convert it into an `Iterator` of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	///
	/// If no scorable hand can be formed with the new tile, the iterator will be empty.
	///
	/// The iterator may contain multiple instances of the same hand. You may want to collect it into a `BTreeSet` or similar
	/// before doing further computation on it. Note again that the order of scorable hands in the set will not have anything to do with
	/// the scorable hands' scores.
	///
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akadora
	/// does not make any difference to the final score. For example a hand `233445550p567m88s` can form both `234p 345p 550p 567m 88s` and `234p 340p 555p 567m 88s`,
	/// but only one is guaranteed to be yielded.
	///
	/// Scorable hands that differ in the wait *are* considered distinct. For example a hand 23344450p567m88s + 3p can form the following scorable hands:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { anjun 3p 4p 0p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 2p 3p 4p kanchan } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Hand10ScorableHands {
		let Self(ts, ms) = self;

		let mut ts = ts.concat([new_tile].into());
		ts.sort_unstable();
		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		let [ma] = <[HandMeld; _]>::from(ms).map(Into::into);

		Hand10ScorableHands {
			pair: None,
			mbcds: Default::default(),
			pairs,
			ma,
		}
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> Hand10Tenpai {
		// A hand is considered to be in tenpai even if all extant copies of a tile are available in the hand, as long as those copies are not present solely in the unmelded tiles (`self.0`).
		//
		// Eg, if `self` is `(t![1m, 1m, 1m, 1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [])`, this requires a fifth `1m` to form a valid shape
		// `{ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there are already four copies of `1m` in `self.0`, `self` is not considered to be in tenpai for a 1m.
		//
		// If `self` is `(t![1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [make_hand!(@meld { minkou 1m 1m 1m })])`, this requires a fifth `1m` to form a valid shape
		// `{ minkou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there is only one copy of 1m in `self.0` (the other three are in `self.1`), `self` is considered to be in tenpai for a 1m.
		//
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.

		let tiles = Tile::each(game_type).iter();
		let Self(mut ts, _) = self;
		ts.sort_unstable();
		Hand10Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand10ScorableHands {
	pair: Option<ScorableHandPair>,
	mbcds: Dedup<Melds3>,
	pairs: ScorableHandPairs<U11>,
	ma: ScorableHandMeld,
}

assert_size_of!(Hand10ScorableHands, 392);

impl Iterator for Hand10ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let pair =
				if let Some(pair) = self.pair {
					pair
				}
				else {
					let (pair, rest, new_tile_i) = self.pairs.next()?;
					self.mbcds = Dedup::new(Melds3::new(rest, new_tile_i));
					*self.pair.insert(pair)
				};

			let Some(([mb, mc], md)) = self.mbcds.next() else {
				self.pair = None;
				continue;
			};

			break Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, mb, mc, md, pair)));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.pairs.size_hint() == (0, Some(0)) {
			let (_, hi) = self.mbcds.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl core::iter::FusedIterator for Hand10ScorableHands where Dedup<Melds3>: core::iter::FusedIterator {}

#[derive(Clone, Debug)]
pub struct Hand10Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	ts: GenericArray<Tile, U10>,
}

assert_size_of!(Hand10Tenpai, 32);

impl Iterator for Hand10Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			let num_in_ts = self.ts.iter().filter(|t| t.eq_ignore_red(&new_tile)).count();
			if num_in_ts == 4 {
				continue;
			}
			let ts = insert_sorted(&self.ts, new_tile);
			let new_tile_i = ts.iter().position(|&t| t == new_tile);
			// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
			let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, TsumoOrRon::Tsumo);
			for (_, rest, new_tile_i) in ScorableHandPairs::new(ts, new_tile_i) {
				if Melds3::new(rest, new_tile_i).next().is_some() {
					return Some(new_tile);
				}
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Hand10Tenpai {}

impl Hand<U13, U0> {
	/// Add the given drawn / called tile to this hand and convert it into an `Iterator` of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	///
	/// If no scorable hand can be formed with the new tile, the iterator will be empty.
	///
	/// The iterator may contain multiple instances of the same hand. You may want to collect it into a `BTreeSet` or similar
	/// before doing further computation on it. Note again that the order of scorable hands in the set will not have anything to do with
	/// the scorable hands' scores.
	///
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akadora
	/// does not make any difference to the final score. For example a hand `233445550p567m88s` can form both `234p 345p 550p 567m 88s` and `234p 340p 555p 567m 88s`,
	/// but only one is guaranteed to be yielded.
	///
	/// Scorable hands that differ in the wait *are* considered distinct. For example a hand 23344450p567m88s + 3p can form the following scorable hands:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { anjun 3p 4p 0p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 2p 3p 4p kanchan } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Hand13ScorableHands {
		let Self(ts, ms) = self;

		let [] = ms.into();

		let kokushi_musou = ToKokushiMusou::new(ts.as_ref()).with_new_tile(new_tile);

		let mut ts = ts.concat([new_tile].into());
		ts.sort_unstable();

		let chiitoi = to_chiitoi(ts.as_ref());

		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		Hand13ScorableHands {
			pair: None,
			mabcds: Default::default(),
			pairs,
			kokushi_musou,
			chiitoi,
		}
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> Hand13Tenpai {
		// A hand is considered to be in tenpai even if all extant copies of a tile are available in the hand, as long as those copies are not present solely in the unmelded tiles (`self.0`).
		//
		// Eg, if `self` is `(t![1m, 1m, 1m, 1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [])`, this requires a fifth `1m` to form a valid shape
		// `{ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there are already four copies of `1m` in `self.0`, `self` is not considered to be in tenpai for a 1m.
		//
		// If `self` is `(t![1m, 3m, 4m, 5m, 3p, 4p, 5p, 3s, 4s, 5s], [make_hand!(@meld { minkou 1m 1m 1m })])`, this requires a fifth `1m` to form a valid shape
		// `{ minkou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 3p 4p 5p } { anjun 3s 4s 5s } { 1m 1m }`.
		// Since there is only one copy of 1m in `self.0` (the other three are in `self.1`), `self` is considered to be in tenpai for a 1m.
		//
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.

		let tiles = Tile::each(game_type).iter();
		let Self(mut ts, _) = self;
		let kokushi_musou = ToKokushiMusou::new(ts.as_ref());
		ts.sort_unstable();
		Hand13Tenpai { tiles, kokushi_musou, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand13ScorableHands {
	pair: Option<ScorableHandPair>,
	mabcds: Dedup<Melds4>,
	pairs: ScorableHandPairs<U14>,
	kokushi_musou: Option<ScorableHand>,
	chiitoi: Option<ScorableHand>,
}

assert_size_of!(Hand13ScorableHands, 608);

impl Iterator for Hand13ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou.take() {
			return Some(h);
		}

		if let Some(h) = self.chiitoi.take() {
			return Some(h);
		}

		loop {
			let pair =
				if let Some(pair) = self.pair {
					pair
				}
				else {
					let (pair, rest, new_tile_i) = self.pairs.next()?;
					self.mabcds = Dedup::new(Melds4::new(rest, new_tile_i));
					*self.pair.insert(pair)
				};

			let Some(([m1, m2, m3], m4)) = self.mabcds.next() else {
				self.pair = None;
				continue;
			};

			break Some(ScorableHand::Regular(ScorableHandRegular { m1, m2, m3, m4, pair: ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Pair, inner: pair } }));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let lo = usize::from(self.kokushi_musou.is_some()) + usize::from(self.chiitoi.is_some());
		if self.pairs.size_hint() == (0, Some(0)) {
			let (_, hi) = self.mabcds.size_hint();
			(lo, hi)
		}
		else {
			(lo, None)
		}
	}
}

impl core::iter::FusedIterator for Hand13ScorableHands where Dedup<Melds4>: core::iter::FusedIterator {}

#[derive(Clone, Debug)]
pub struct Hand13Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	kokushi_musou: ToKokushiMusou,
	ts: GenericArray<Tile, U13>,
}

assert_size_of!(Hand13Tenpai, 32);

impl Iterator for Hand13Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;

			if self.kokushi_musou.with_new_tile(new_tile).is_some() {
				return Some(new_tile);
			}

			let num_in_ts = self.ts.iter().filter(|t| t.eq_ignore_red(&new_tile)).count();
			if num_in_ts == 4 {
				continue;
			}
			let ts = insert_sorted(&self.ts, new_tile);

			if to_chiitoi(ts.as_ref()).is_some() {
				return Some(new_tile);
			}

			let new_tile_i = ts.iter().position(|&t| t == new_tile);
			// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
			let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, TsumoOrRon::Tsumo);

			for (_, rest, new_tile_i) in ScorableHandPairs::new(ts, new_tile_i) {
				if Melds4::new(rest, new_tile_i).next().is_some() {
					return Some(new_tile);
				}
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Hand13Tenpai {}

impl Hand<U14, U0> {
	/// Convert this hand into an `Iterator` of [`ScorableHand`]s by considering each tile as a new tile.
	///
	/// This is used for rulesets where tenhou can be won by considering any tile of the starting hand as the new tile.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	///
	/// If no scorable hand can be formed with the new tile, the iterator will be empty.
	///
	/// The iterator may contain multiple instances of the same hand. You may want to collect it into a `BTreeSet` or similar
	/// before doing further computation on it. Note again that the order of scorable hands in the set will not have anything to do with
	/// the scorable hands' scores.
	///
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akadora
	/// does not make any difference to the final score. For example a hand `233445550p567m88s` can form both `234p 345p 550p 567m 88s` and `234p 340p 555p 567m 88s`,
	/// but only one is guaranteed to be yielded.
	///
	/// Scorable hands that differ in the wait *are* considered distinct. For example a hand 23344450p567m88s + 3p can form the following scorable hands:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { anjun 3p 4p 0p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 2p 3p 4p kanchan } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self) -> impl Iterator<Item = ScorableHand> {
		let Self(mut ts, ms) = self;
		let [] = ms.into();

		let kokushi_musou = ToKokushiMusou::tenhou(ts.as_ref());

		ts.sort_unstable();

		kokushi_musou.into_iter()
			.chain(to_chiitoi(ts.as_ref()))
			.chain(ts.into_iter().enumerate().flat_map(move |(i, _)| {
				let mut pairs = ScorableHandPairs::new(ts, (i, TsumoOrRon::Tsumo));
				let mut pair = None;
				let mut mabcds = Default::default();

				core::iter::from_fn(move || loop {
					let pair_ =
						if let Some(pair) = pair {
							pair
						}
						else {
							let (pair_, rest, new_tile_i) = pairs.next()?;
							mabcds = Dedup::new(Melds4::new(rest, new_tile_i));
							*pair.insert(pair_)
						};

					let Some(([m1, m2, m3], m4)) = mabcds.next() else {
						pair = None;
						continue;
					};

					break Some(ScorableHand::Regular(ScorableHandRegular { m1, m2, m3, m4, pair: ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Pair, inner: pair_ } }));
				})
			}))
	}
}

impl HandMeld {
	/// Construct a `HandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Ankan(t))
	}

	/// Construct a `HandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub unsafe fn ankan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let t = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Ankan(t)
	}

	/// Construct a `HandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Minkan(t))
	}

	/// Construct a `HandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub unsafe fn minkan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let t = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Minkan(t)
	}

	/// Construct a `HandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Minkou(t))
	}

	/// Construct a `HandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn minkou_unchecked(t1: Tile, t2: Tile, t3: Tile) -> Self {
		let t = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Minkou(t)
	}

	/// Construct a `HandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Minjun(t))
	}

	/// Construct a `HandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn minjun_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::Minjun(t)
	}

	/// Parses a meld from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
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
	pub fn parse_until(s: &[u8], end: Option<u8>) -> Result<(Self, &[u8]), ()> {
		let (ts, ty, s) = Tile::parse_run_until::<U4>(s, end)?;
		let ty = ty.ok_or(())?;
		Ok((match ts[..] {
			[t1, t2, t3, t4] => {
				let t = Tile::kan_representative(t1, t2, t3, t4).ok_or(())?;
				match ty {
					HandMeldType::Ankan => Self::Ankan(t),
					HandMeldType::Shouminkan |
					HandMeldType::MinjunMinkouDaiminkan => Self::Minkan(t),
				}
			},

			[t1, t2, t3] if matches!(ty, HandMeldType::MinjunMinkouDaiminkan) =>
				if let Some(m) = Self::minkou(t1, t2, t3) {
					m
				}
				else {
					let t1 = NumberTile::try_from(t1)?;
					let t2 = NumberTile::try_from(t2)?;
					let t3 = NumberTile::try_from(t3)?;
					let mut ts = [t1, t2, t3];
					SortingNetwork::sort(&mut ts);
					let t1 = ShunLowTile::try_from(ts[0])?;
					Self::minjun(t1, ts[1], ts[2]).ok_or(())?
				},

			_ => return Err(()),
		}, s))
	}
}

impl core::fmt::Debug for HandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for HandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			Self::Ankan(t1) => {
				let t_rest = t1.remove_red();
				write!(f, "{{ ankan {t_rest} {t_rest} {t_rest} {t1} }}")
			},
			Self::Minkan(t1) => {
				let t_rest = t1.remove_red();
				write!(f, "{{ minkan {t_rest} {t_rest} {t_rest} {t1} }}")
			},
			Self::Minkou(t1) => {
				let t_rest = t1.remove_red();
				write!(f, "{{ minkou {t_rest} {t_rest} {t1} }}")
			},
			Self::Minjun(t) => {
				let (t1, t2, t3) = t.shun();
				write!(f, "{{ minjun {t1} {t2} {t3} }}")
			},
		}
	}
}

/// Parses a `HandMeld` from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
///
/// Ref: <https://note.com/yuarasino/n/n1ba95bf3b618>
///
/// Note that `HandMeld` does not retain information about which tile was called or which player it was called from.
/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
/// but the specific position of the marker within the meld (which identifies the tile that was called)
/// and the order of the tiles (which identifies the player who the tile was called from) are ignored.
impl core::str::FromStr for HandMeld {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (result, _) = Self::parse_until(s.as_ref(), None)?;
		Ok(result)
	}
}

impl HandStable {
	/// Draw the given tile into this stable hand to form a tentative hand.
	pub fn draw(self, new_tile: Tile) -> HandTentative {
		match self {
			Self::One(h) => h.draw(new_tile).into(),
			Self::Four(h) => h.draw(new_tile).into(),
			Self::Seven(h) => h.draw(new_tile).into(),
			Self::Ten(h) => h.draw(new_tile).into(),
			Self::Thirteen(h) => h.draw(new_tile).into(),
		}
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Self> {
		match self {
			Self::One(_) => None,
			Self::Four(h) => h.find_daiminkan(new_tile).map(Self::One),
			Self::Seven(h) => h.find_daiminkan(new_tile).map(Self::Four),
			Self::Ten(h) => h.find_daiminkan(new_tile).map(Self::Seven),
			Self::Thirteen(h) => h.find_daiminkan(new_tile).map(Self::Ten),
		}
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> HandMinkous {
		match self {
			Self::One(_) => HandMinkous::One,
			Self::Four(h) => HandMinkous::Four(h.find_minkous(new_tile)),
			Self::Seven(h) => HandMinkous::Seven(h.find_minkous(new_tile)),
			Self::Ten(h) => HandMinkous::Ten(h.find_minkous(new_tile)),
			Self::Thirteen(h) => HandMinkous::Thirteen(h.find_minkous(new_tile)),
		}
	}

	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> HandMinjuns {
		match self {
			Self::One(_) => HandMinjuns::One,
			Self::Four(h) => HandMinjuns::Four(h.find_minjuns(new_tile)),
			Self::Seven(h) => HandMinjuns::Seven(h.find_minjuns(new_tile)),
			Self::Ten(h) => HandMinjuns::Ten(h.find_minjuns(new_tile)),
			Self::Thirteen(h) => HandMinjuns::Thirteen(h.find_minjuns(new_tile)),
		}
	}

	/// Add the given drawn / called tile to this hand and convert it into an `Iterator` of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	///
	/// If no scorable hand can be formed with the new tile, the iterator will be empty.
	///
	/// The iterator may contain multiple instances of the same hand. You may want to collect it into a `BTreeSet` or similar
	/// before doing further computation on it. Note again that the order of scorable hands in the set will not have anything to do with
	/// the scorable hands' scores.
	///
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akadora
	/// does not make any difference to the final score. For example a hand `233445550p567m88s` can form both `234p 345p 550p 567m 88s` and `234p 340p 555p 567m 88s`,
	/// but only one is guaranteed to be yielded.
	///
	/// Scorable hands that differ in the wait *are* considered distinct. For example a hand 23344450p567m88s + 3p can form the following scorable hands:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { anjun 3p 4p 0p ryanmen_low } { 8s 8s }`
	/// - `{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { anjun 2p 3p 4p kanchan } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> HandScorableHands {
		match self {
			Self::One(h) => HandScorableHands::One(h.to_scorable_hand(new_tile).into_iter()),
			Self::Four(h) => HandScorableHands::Four(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Seven(h) => HandScorableHands::Seven(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Ten(h) => HandScorableHands::Ten(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Thirteen(h) => HandScorableHands::Thirteen(h.to_scorable_hands(new_tile, tsumo_or_ron)),
		}
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> HandTenpai {
		match self {
			Self::One(h) => {
				let wait = h.tenpai();
				HandTenpai::One(core::iter::once(wait).chain(wait.make_red()))
			},
			Self::Four(h) => HandTenpai::Four(h.tenpai(game_type)),
			Self::Seven(h) => HandTenpai::Seven(h.tenpai(game_type)),
			Self::Ten(h) => HandTenpai::Ten(h.tenpai(game_type)),
			Self::Thirteen(h) => HandTenpai::Thirteen(h.tenpai(game_type)),
		}
	}
}

impl core::fmt::Display for HandStable {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			Self::One(h) => h.fmt(f),
			Self::Four(h) => h.fmt(f),
			Self::Seven(h) => h.fmt(f),
			Self::Ten(h) => h.fmt(f),
			Self::Thirteen(h) => h.fmt(f),
		}
	}
}

/// Parses a `HandStable` from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
///
/// Ref: <https://note.com/yuarasino/n/n1ba95bf3b618>
///
/// Note that [`HandMeld`] does not retain information about which tile was called or which player it was called from.
/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
/// but the specific position of the marker within the meld (which identifies the tile that was called)
/// and the order of the tiles (which identifies the player who the tile was called from) are ignored.
///
/// Also, since the result of this parse is a `HandStable`, the input string should not include the newly drawn tile.
/// For example, in a hand that has not made any calls, the input string should specify 13 tiles, not 14.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{
/// #     HandStable,
/// #     make_hand,
/// # };
/// #
/// // chii, chii
/// let h: HandStable = "4477m1p11z 7-68m 5-46s".parse().unwrap();
/// assert_eq!(h, HandStable::Seven(make_hand!(4m 4m 7m 7m 1p E E { minjun 6m 7m 8m } { minjun 4s 5s 6s })));
///
/// // pon
/// let h: HandStable = "35m3378p3467s 2-22m".parse().unwrap();
/// assert_eq!(h, HandStable::Ten(make_hand!(3m 5m 3p 3p 7p 8p 3s 4s 6s 7s { minkou 2m 2m 2m })));
///
/// // chii, shouminkan
/// let h: HandStable = "3377p678s 2-34s 2=222m".parse().unwrap();
/// assert_eq!(h, HandStable::Seven(make_hand!(3p 3p 7p 7p 6s 7s 8s { minjun 2s 3s 4s } { minkan 2m 2m 2m 2m })));
///
/// // daiminkan, chii
/// let h: HandStable = "1309p789s 5555-z 5-46p".parse().unwrap();
/// assert_eq!(h, HandStable::Seven(make_hand!(1p 3p 0p 9p 7s 8s 9s { minkan Wh Wh Wh Wh } { minjun 4p 5p 6p })));
/// ```
impl core::str::FromStr for HandStable {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (ts, ts_type, s) = Tile::parse_run_until::<U13>(s.as_ref(), Some(b' '))?;
		if ts_type.is_some() {
			return Err(());
		}

		Ok(match ts[..] {
			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] => {
				if !s.is_empty() {
					return Err(());
				}
				Hand(
					[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into(),
					[].into(),
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] => {
				let (m1, _) = HandMeld::parse_until(s, None)?;
				Hand(
					[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into(),
					[m1].into(),
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, _) = HandMeld::parse_until(s, None)?;
				Hand(
					[t1, t2, t3, t4, t5, t6, t7].into(),
					[m1, m2].into(),
				).into()
			},

			[t1, t2, t3, t4] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, _) = HandMeld::parse_until(s, None)?;
				Hand(
					[t1, t2, t3, t4].into(),
					[m1, m2, m3].into(),
				).into()
			},

			[t1] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m4, _) = HandMeld::parse_until(s, None)?;
				Hand(
					[t1].into(),
					[m1, m2, m3, m4].into(),
				).into()
			},

			_ => return Err(()),
		})
	}
}

impl HandTentative {
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the hand resulting from the discard of that tile, and the discarded tile.
	///
	/// # Panics
	///
	/// Panics if the given index is not within bounds.
	pub fn discard(self, i: usize) -> (HandStable, Tile) {
		match self {
			Self::Two(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Five(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Eight(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Eleven(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Fourteen(h) => { let (h, t) = h.discard(i); (h.into(), t) },
		}
	}

	/// Finds all possible ankans (quad via kan call on a quad in the hand).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_ankans(self) -> HandAnkans {
		match self {
			Self::Two(_) => HandAnkans::Two,
			Self::Five(h) => HandAnkans::Five(h.find_ankans()),
			Self::Eight(h) => HandAnkans::Eight(h.find_ankans()),
			Self::Eleven(h) => HandAnkans::Eleven(h.find_ankans()),
			Self::Fourteen(h) => HandAnkans::Fourteen(h.find_ankans()),
		}
	}

	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_shouminkans(self) -> HandShouminkans {
		match self {
			Self::Two(h) => HandShouminkans::Two(h.find_shouminkans()),
			Self::Five(h) => HandShouminkans::Five(h.find_shouminkans()),
			Self::Eight(h) => HandShouminkans::Eight(h.find_shouminkans()),
			Self::Eleven(h) => HandShouminkans::Eleven(h.find_shouminkans()),
			Self::Fourteen(_) => HandShouminkans::Fourteen,
		}
	}
}

impl core::fmt::Display for HandTentative {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			Self::Two(h) => h.fmt(f),
			Self::Five(h) => h.fmt(f),
			Self::Eight(h) => h.fmt(f),
			Self::Eleven(h) => h.fmt(f),
			Self::Fourteen(h) => h.fmt(f),
		}
	}
}

macro_rules! hand_enum_from {
	($($nt:ty, $nm:ty => $ty:tt :: $variant:ident ,)*) => {
		$(
			impl From<Hand<$nt, $nm>> for $ty {
				fn from(h: Hand<$nt, $nm>) -> Self {
					Self::$variant(h)
				}
			}
		)*
	};
}

hand_enum_from! {
	U1, U4 => HandStable::One,
	U2, U4 => HandTentative::Two,
	U4, U3 => HandStable::Four,
	U5, U3 => HandTentative::Five,
	U7, U2 => HandStable::Seven,
	U8, U2 => HandTentative::Eight,
	U10, U1 => HandStable::Ten,
	U11, U1 => HandTentative::Eleven,
	U13, U0 => HandStable::Thirteen,
	U14, U0 => HandTentative::Fourteen,
}

/// [`Iterator`] of [`Hand<{ NT - 4 }, { NM + 1 }>`](Hand) values formed by creating an ankan in the given hand.
pub struct Ankans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	tiles: TileMultiSetIntoIter<Tile34MultiSetElement>,
}

impl<NT, NM> Ankans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>) -> Self {
		let tiles: Tile34MultiSet = hand.0.into_iter().map(|t| (t, 1)).collect();
		Self {
			hand,
			tiles: tiles.into_iter(),
		}
	}
}

impl<NT, NM> Clone for Ankans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: Clone,
	TileMultiSetIntoIter<Tile34MultiSetElement>: Clone,
{
	fn clone(&self) -> Self {
		Self {
			hand: self.hand.clone(),
			tiles: self.tiles.clone(),
		}
	}
}

impl<NT, NM> core::fmt::Debug for Ankans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Ankans")
			.field("hand", &self.hand)
			.field("tiles", &self.tiles)
			.finish()
	}
}

impl<NT, NM> Iterator for Ankans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U4, Output: ArrayLength>,
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = Hand<Diff<NT, U4>, Sum<NM, U1>>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (t_kan, count) = self.tiles.next()?;
			if count.get() != 4 { continue; }

			let Hand(ts, ms) = self.hand;

			// SAFETY: `count` has been checked above to ensure that there are at most four tiles that match `t`.
			// Thus exactly 4 elements will be pushed into `ts_kan`, and exactly NT - 4 elements will be pushed into `ts_rest`.
			let mut ts_rest = ArrayVec::<_, Diff<NT, U4>>::new();
			let mut ts_kan = ArrayVec::<_, U4>::new();
			for t in ts {
				if t.eq_ignore_red(&t_kan) {
					unsafe { ts_kan.push_unchecked(t); }
				}
				else {
					unsafe { ts_rest.push_unchecked(t); }
				}
			}
			let ts_rest = ts_rest.try_into();
			let ts_rest = unsafe { ts_rest.unwrap_unchecked() };
			let ts_kan = ts_kan.try_into();
			let ts_kan: GenericArray<_, U4> = unsafe { ts_kan.unwrap_unchecked() };
			let [t1, t2, t3, t4] = ts_kan.into();
			// SAFETY: `ts_kan` is guaranteed to contain tiles that form a valid kan.
			break Some(Hand(ts_rest, ms.concat([unsafe { HandMeld::ankan_unchecked(t1, t2, t3, t4) }].into())));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl<NT, NM> core::iter::FusedIterator for Ankans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U4, Output: ArrayLength>,
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{}

/// [`Iterator`] of [`HandStable`] values formed by creating an ankan in the given hand.
#[derive(Clone, Debug)]
pub enum HandAnkans {
	Two,
	Five(Ankans<U5, U3>),
	Eight(Ankans<U8, U2>),
	Eleven(Ankans<U11, U1>),
	Fourteen(Ankans<U14, U0>),
}

impl Iterator for HandAnkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::Two => None,
			Self::Five(inner) => inner.next().map(Into::into),
			Self::Eight(inner) => inner.next().map(Into::into),
			Self::Eleven(inner) => inner.next().map(Into::into),
			Self::Fourteen(inner) => inner.next().map(Into::into),
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::Two => (0, Some(0)),
			Self::Five(inner) => inner.size_hint(),
			Self::Eight(inner) => inner.size_hint(),
			Self::Eleven(inner) => inner.size_hint(),
			Self::Fourteen(inner) => inner.size_hint(),
		}
	}
}

impl core::iter::FusedIterator for HandAnkans {}

fn find_daiminkan<N>(
	ts: GenericArray<Tile, N>,
	new_tile: Tile,
) -> Option<(GenericArray<Tile, Diff<N, U3>>, HandMeld)>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>,
	GenericArray<Tile, N>: Copy,
{
	let mut existing = ts.into_iter().enumerate().filter(|&(_, t)| t.eq_ignore_red(&new_tile));
	let (i1, t1) = existing.next()?;
	let (i2, t2) = existing.next()?;
	let (i3, t3) = existing.next()?;
	// SAFETY: `i*` are guaranteed to be in ascending order and within the bounds of `ts` by the definition of `.into_iter().enumerate()`.
	let ts = unsafe { except(&ts, [i1, i2, i3].into()) };
	// SAFETY: `existing` only yields tiles which equal `new_tile`, so all four must form a valid kan.
	let m = unsafe { HandMeld::minkan_unchecked(t1, t2, t3, new_tile) };
	Some((ts, m))
}

/// [`Iterator`] of [`Hand<{ NT - 1 }, NM>`](Hand) values formed by creating a shouminkan in the given hand.
pub struct Shouminkans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	i: core::ops::Range<usize>,
}

impl<NT, NM> Shouminkans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>) -> Self {
		let i = 0..hand.0.len();
		Self { hand, i }
	}
}

impl<NT, NM> Shouminkans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U1, Output: ArrayLength>,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy + Remove<Tile, NT, Output = GenericArray<Tile, Diff<NT, U1>>>,
	GenericArray<HandMeld, NM>: Copy,
{
	fn next_inner(&self, i: usize) -> Option<Hand<Diff<NT, U1>, NM>> {
		// SAFETY: `self.i` yields only indices which are valid for `self.hand.0` because that was how it was constructed in `new()`.
		unsafe { core::hint::assert_unchecked(i < self.hand.0.len()); }
		let tile = self.hand.0[i];
		// Note: This modifies the meld in a copy of `self.hand`, not `self.hand` itself,
		// because every Iterator element should be a modification on top of the original hand.
		let mut melds = self.hand.1;
		for m in &mut melds {
			if let HandMeld::Minkou(t) = *m && t.eq_ignore_red(&tile) {
				// SAFETY: Three tiles of a kou with a fourth tile that is equal to the kou's tiles necessarily form a valid kan.
				*m = unsafe { HandMeld::minkan_unchecked(t, t, t, tile) };
				let (_, ts) = self.hand.0.remove(i);
				return Some(Hand(ts, melds));
			}
		}
		None
	}
}

impl<NT, NM> Clone for Shouminkans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: Clone,
	TileMultiSetIntoIter<Tile34MultiSetElement>: Clone,
{
	fn clone(&self) -> Self {
		Self {
			hand: self.hand.clone(),
			i: self.i.clone(),
		}
	}
}

impl<NT, NM> core::fmt::Debug for Shouminkans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Shouminkans")
			.field("hand", &self.hand)
			.field("i", &self.i)
			.finish()
	}
}

impl<NT, NM> Iterator for Shouminkans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U1, Output: ArrayLength>,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy + Remove<Tile, NT, Output = GenericArray<Tile, Diff<NT, U1>>>,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = Hand<Diff<NT, U1>, NM>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let i = self.i.next()?;
			if let Some(h) = self.next_inner(i) {
				break Some(h);
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.i.size_hint();
		(0, hi)
	}
}

impl<NT, NM> DoubleEndedIterator for Shouminkans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U1, Output: ArrayLength>,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy + Remove<Tile, NT, Output = GenericArray<Tile, Diff<NT, U1>>>,
	GenericArray<HandMeld, NM>: Copy,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		loop {
			let i = self.i.next_back()?;
			if let Some(h) = self.next_inner(i) {
				break Some(h);
			}
		}
	}
}

impl<NT, NM> core::iter::FusedIterator for Shouminkans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U1, Output: ArrayLength>,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy + Remove<Tile, NT, Output = GenericArray<Tile, Diff<NT, U1>>>,
	GenericArray<HandMeld, NM>: Copy,
{}

/// [`Iterator`] of [`HandStable`] values formed by creating an shouminkan in the given hand.
#[derive(Clone, Debug)]
pub enum HandShouminkans {
	Two(Shouminkans<U2, U4>),
	Five(Shouminkans<U5, U3>),
	Eight(Shouminkans<U8, U2>),
	Eleven(Shouminkans<U11, U1>),
	Fourteen,
}

impl Iterator for HandShouminkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::Two(inner) => inner.next().map(Into::into),
			Self::Five(inner) => inner.next().map(Into::into),
			Self::Eight(inner) => inner.next().map(Into::into),
			Self::Eleven(inner) => inner.next().map(Into::into),
			Self::Fourteen => None,
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::Two(inner) => inner.size_hint(),
			Self::Five(inner) => inner.size_hint(),
			Self::Eight(inner) => inner.size_hint(),
			Self::Eleven(inner) => inner.size_hint(),
			Self::Fourteen => (0, Some(0)),
		}
	}
}

impl DoubleEndedIterator for HandShouminkans {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self {
			Self::Two(inner) => inner.next_back().map(Into::into),
			Self::Five(inner) => inner.next_back().map(Into::into),
			Self::Eight(inner) => inner.next_back().map(Into::into),
			Self::Eleven(inner) => inner.next_back().map(Into::into),
			Self::Fourteen => None,
		}
	}
}

impl core::iter::FusedIterator for HandShouminkans {}

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minkou in the given hand using the given new tile.
/// Along with the `Hand`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae-nashi.
pub struct Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	new_tile: Tile,
	combinations: ArrayVecIntoCombinations<(usize, Tile), U4>,
}

impl<NT, NM> Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>, new_tile: Tile) -> Self {
		let ts_consider: ArrayVec<_, _> = hand.0.into_iter().enumerate().filter(|&(_, t)| t.eq_ignore_red(&new_tile)).collect();
		Self {
			hand,
			new_tile,
			combinations: ts_consider.into_combinations(),
		}
	}
}

impl<NT, NM> Clone for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: Clone,
	GenericArray<core::mem::MaybeUninit<(usize, Tile)>, NT>: Clone,
{
	fn clone(&self) -> Self {
		Self {
			hand: self.hand.clone(),
			new_tile: self.new_tile,
			combinations: self.combinations.clone(),
		}
	}
}

impl<NT, NM> core::fmt::Debug for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Minkous")
			.field("hand", &self.hand)
			.field("new_tile", &self.new_tile)
			.field("combinations", &self.combinations)
			.finish()
	}
}

impl<NT, NM> Iterator for Minkous<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U2, Output: ArrayLength>,
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = (Hand<Diff<NT, U2>, Sum<NM, U1>>, ArrayVec<usize, Diff<NT, U2>>);

	fn next(&mut self) -> Option<Self::Item> {
		let ((i1, t1), (i2, t2)) = self.combinations.next()?;
		// SAFETY: `self.combinations` only yields tiles which equal `new_tile`, so all three must form a valid kou.
		let m = unsafe { HandMeld::minkou_unchecked(t1, t2, self.new_tile) };
		// SAFETY: `i*` are guaranteed to be within the bounds of `self.hand.0` by the implementation of `.into_iter().enumerate()`
		// and to be in ascending order `ArrayVecIntoCombinations`.
		let ts = unsafe { except(&self.hand.0, [i1, i2].into()) };
		let allowed_discards: ArrayVec<_, _> =
			ts.iter().enumerate()
			.filter_map(|(i, &t)| t.ne_ignore_red(&self.new_tile).then_some(i))
			.collect();
		(!allowed_discards.is_empty()).then(|| (Hand(ts, self.hand.1.concat([m].into())), allowed_discards))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.combinations.size_hint();
		(0, hi)
	}
}

impl<NT, NM> core::iter::FusedIterator for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Self: Iterator,
{}

/// [`Iterator`] of [`HandTentative`] values formed by creating a minkou in the given hand using the given new tile.
/// Along with the `HandTentative`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae-nashi.
#[derive(Clone, Debug)]
pub enum HandMinkous {
	One,
	Four(Minkous<U4, U3>),
	Seven(Minkous<U7, U2>),
	Ten(Minkous<U10, U1>),
	Thirteen(Minkous<U13, U0>),
}

impl Iterator for HandMinkous {
	type Item = (HandTentative, ArrayVec<usize, U11>);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards.into_iter().collect())),
			Self::Seven(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards.into_iter().collect())),
			Self::Ten(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards.into_iter().collect())),
			Self::Thirteen(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::One => (0, Some(0)),
			Self::Four(inner) => inner.size_hint(),
			Self::Seven(inner) => inner.size_hint(),
			Self::Ten(inner) => inner.size_hint(),
			Self::Thirteen(inner) => inner.size_hint(),
		}
	}
}

impl core::iter::FusedIterator for HandMinkous {}

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minjun in the given hand using the given new tile.
/// Along with the `Hand`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae-nashi.
pub struct Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	new_tile: NumberTile,
	combinations: ArrayVecIntoCombinations<(usize, NumberTile), U8>,
}

impl<NT, NM> Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>, new_tile: NumberTile) -> Self {
		let ts_consider: ArrayVec<_, _> =
			hand.0.into_iter()
			.enumerate()
			.filter_map(|(i, t)| {
				let t = NumberTile::try_from(t).ok()?;
				(t.suit() == new_tile.suit() && (1..=2).contains(&t.number().value().abs_diff(new_tile.number().value()))).then_some((i, t))
			})
			.collect();
		Self {
			hand,
			new_tile,
			combinations: ts_consider.into_combinations(),
		}
	}
}

impl<NT, NM> Clone for Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: Clone,
	GenericArray<core::mem::MaybeUninit<(usize, NumberTile)>, NT>: Clone,
{
	fn clone(&self) -> Self {
		Self {
			hand: self.hand.clone(),
			new_tile: self.new_tile,
			combinations: self.combinations.clone(),
		}
	}
}

impl<NT, NM> core::fmt::Debug for Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Minjuns")
			.field("hand", &self.hand)
			.field("new_tile", &self.new_tile)
			.field("combinations", &self.combinations)
			.finish()
	}
}

impl<NT, NM> Iterator for Minjuns<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<U2, Output: ArrayLength>,
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = (Hand<Diff<NT, U2>, Sum<NM, U1>>, ArrayVec<usize, Diff<NT, U2>>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ((i1, t1), (i2, t2)) = self.combinations.next()?;
			let [t1, t2, t3] = {
				let mut ts = [t1, t2, self.new_tile];
				SortingNetwork::sort(&mut ts);
				ts
			};

			let Ok(tsl1) = ShunLowTile::try_from(t1) else { continue; };
			let Some(t) = ShunLowTileAndHasFiveRed::new(tsl1, t2, t3) else { continue; };
			let m = HandMeld::Minjun(t);

			// SAFETY: `i*` are guaranteed to be within the bounds of `self.hand.0` by the implementation of `.into_iter().enumerate()`
			// and to be in ascending order `ArrayVecIntoCombinations`.
			let ts = unsafe { except(&self.hand.0, [i1, i2].into()) };

			let cannot_discard_new = Tile::from(self.new_tile);
			let cannot_discard_low = if t3.eq_ignore_red(&self.new_tile) { t1.previous_in_sequence().map(Tile::from) } else { None };
			let cannot_discard_high = if t1.eq_ignore_red(&self.new_tile) { t3.next_in_sequence().map(Tile::from) } else { None };
			let allowed_discards: ArrayVec<_, _> =
				ts.iter().enumerate()
				.filter_map(|(i, &t)| (t != cannot_discard_new && Some(t) != cannot_discard_low && Some(t) != cannot_discard_high).then_some(i))
				.collect();

			if !allowed_discards.is_empty() {
				return Some((Hand(ts, self.hand.1.concat([m].into())), allowed_discards));
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.combinations.size_hint();
		(0, hi)
	}
}

impl<NT, NM> core::iter::FusedIterator for Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Self: Iterator,
{}

/// [`Iterator`] of [`HandTentative`] values formed by creating a minjun in the given hand using the given new tile.
/// Along with the `HandTentative`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae-nashi.
#[derive(Clone, Debug)]
pub enum HandMinjuns {
	One,
	Four(Minjuns<U4, U3>),
	Seven(Minjuns<U7, U2>),
	Ten(Minjuns<U10, U1>),
	Thirteen(Minjuns<U13, U0>),
}

impl Iterator for HandMinjuns {
	type Item = (HandTentative, ArrayVec<usize, U11>);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards.into_iter().collect())),
			Self::Seven(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards.into_iter().collect())),
			Self::Ten(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards.into_iter().collect())),
			Self::Thirteen(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::One => (0, Some(0)),
			Self::Four(inner) => inner.size_hint(),
			Self::Seven(inner) => inner.size_hint(),
			Self::Ten(inner) => inner.size_hint(),
			Self::Thirteen(inner) => inner.size_hint(),
		}
	}
}

impl core::iter::FusedIterator for HandMinjuns {}

#[derive(Clone, Debug)]
#[expect(clippy::large_enum_variant)]
pub enum HandScorableHands {
	One(core::option::IntoIter<ScorableHand>),
	Four(Hand4ScorableHands),
	Seven(Hand7ScorableHands),
	Ten(Hand10ScorableHands),
	Thirteen(Hand13ScorableHands),
}

impl Iterator for HandScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One(inner) => inner.next(),
			Self::Four(inner) => inner.next(),
			Self::Seven(inner) => inner.next(),
			Self::Ten(inner) => inner.next(),
			Self::Thirteen(inner) => inner.next(),
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::One(inner) => inner.size_hint(),
			Self::Four(inner) => inner.size_hint(),
			Self::Seven(inner) => inner.size_hint(),
			Self::Ten(inner) => inner.size_hint(),
			Self::Thirteen(inner) => inner.size_hint(),
		}
	}
}

impl core::iter::FusedIterator for HandScorableHands {}

#[derive(Clone, Debug)]
pub enum HandTenpai {
	One(core::iter::Chain<core::iter::Once<Tile>, core::option::IntoIter<Tile>>),
	Four(Hand4Tenpai),
	Seven(Hand7Tenpai),
	Ten(Hand10Tenpai),
	Thirteen(Hand13Tenpai),
}

impl Iterator for HandTenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One(inner) => inner.next(),
			Self::Four(inner) => inner.next(),
			Self::Seven(inner) => inner.next(),
			Self::Ten(inner) => inner.next(),
			Self::Thirteen(inner) => inner.next(),
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::One(inner) => inner.size_hint(),
			Self::Four(inner) => inner.size_hint(),
			Self::Seven(inner) => inner.size_hint(),
			Self::Ten(inner) => inner.size_hint(),
			Self::Thirteen(inner) => inner.size_hint(),
		}
	}
}

impl core::iter::FusedIterator for HandTenpai {}

/// # Safety
///
/// Every element of `i_discard` must be distinct, in sort order, and within the bounds of `ts`.
unsafe fn except<T, N, DN>(
	ts: &GenericArray<T, N>,
	i_discard: GenericArray<usize, DN>,
) -> GenericArray<T, Diff<N, DN>>
where
	T: Clone,
	N: ArrayLength + core::ops::Sub<DN, Output: ArrayLength>,
	DN: ArrayLength,
{
	let mut result = GenericArray::uninit();

	let mut i_start = 0;
	let mut result_start = 0;
	for i_end in i_discard {
		unsafe { core::hint::assert_unchecked(i_start <= i_end); }
		unsafe { core::hint::assert_unchecked(i_end < ts.len()); }

		let result_end = result_start + (i_end - i_start);
		unsafe { core::hint::assert_unchecked(result_end <= result.len()); }

		result[result_start..result_end].write_clone_of_slice(&ts[i_start..i_end]);

		i_start = i_end + 1;
		result_start = result_end;
	}

	unsafe { core::hint::assert_unchecked(result.len() - result_start == ts.len() - i_start); }
	result[result_start..].write_clone_of_slice(&ts[i_start..]);

	unsafe { GenericArray::assume_init(result) }
}

#[derive(Debug)]
struct ScorableHandPairs<N> where N: ArrayLength {
	arr: GenericArray<Tile, N>,
	new_tile_i: (usize, TsumoOrRon),
	i: core::ops::Range<usize>,
}

impl<N> ScorableHandPairs<N>
where
	N: ArrayLength,
{
	fn new(arr: GenericArray<Tile, N>, new_tile_i: (usize, TsumoOrRon)) -> Self {
		let i = 0..(arr.len().saturating_sub(1));
		Self { arr, new_tile_i, i }
	}
}

impl<N> ScorableHandPairs<N>
where
	N: ArrayLength + core::ops::Sub<U2, Output: ArrayLength>,
	GenericArray<Tile, N>: Copy,
{
	// # Safety
	//
	// Requires `i < self.arr.len() - 1`.
	unsafe fn next_inner(&mut self, i: usize) -> Option<(ScorableHandPair, GenericArray<Tile, Diff<N, U2>>, Option<(usize, TsumoOrRon)>)> {
		unsafe { core::hint::assert_unchecked(i < self.arr.len() - 1) };

		let pt1 = self.arr[i];
		let pt2 = self.arr[i + 1];
		let pair = ScorableHandPair::new(pt1, pt2)?;

		let rest = unsafe { except(&self.arr, [i, i + 1].into()) };

		let new_tile_i =
			if self.new_tile_i.0 < i { Some(self.new_tile_i) }
			else if self.new_tile_i.0 > i + 1 { Some((self.new_tile_i.0 - 2, self.new_tile_i.1)) }
			else { None };

		Some((pair, rest, new_tile_i))
	}
}

impl<N> Clone for ScorableHandPairs<N>
where
	N: ArrayLength,
	GenericArray<Tile, N>: Clone,
{
	fn clone(&self) -> Self {
		Self {
			arr: self.arr.clone(),
			new_tile_i: self.new_tile_i,
			i: self.i.clone(),
		}
	}
}

impl<N> Iterator for ScorableHandPairs<N>
where
	N: ArrayLength + core::ops::Sub<U2, Output: ArrayLength>,
	GenericArray<Tile, N>: Copy,
{
	type Item = (ScorableHandPair, GenericArray<Tile, Diff<N, U2>>, Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		// SAFETY: `self.i` was constructed this way in `new()`.
		unsafe { core::hint::assert_unchecked(self.i.start <= self.i.end) };

		loop {
			let i = self.i.next()?;
			// SAFETY: `self.i` was constructed in `new()` to only yield values less than `self.arr.len() - 1`.
			if let Some(result) = unsafe { self.next_inner(i) } {
				break Some(result);
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.i.size_hint();
		(0, hi)
	}
}

impl<N> DoubleEndedIterator for ScorableHandPairs<N>
where
	N: ArrayLength + core::ops::Sub<U2, Output: ArrayLength>,
	GenericArray<Tile, N>: Copy,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		// SAFETY: `self.i` was constructed this way in `new()`.
		unsafe { core::hint::assert_unchecked(self.i.start <= self.i.end) };

		loop {
			let i = self.i.next_back()?;
			// SAFETY: `self.i` was constructed in `new()` to only yield values less than `self.arr.len() - 1`.
			if let Some(result) = unsafe { self.next_inner(i) } {
				break Some(result);
			}
		}
	}
}

impl<N> ExactSizeIterator for ScorableHandPairs<N> where N: ArrayLength, Self: Iterator {}

impl<N> core::iter::FusedIterator for ScorableHandPairs<N> where N: ArrayLength, Self: Iterator {}

fn insert_sorted<T, N>(s: &GenericArray<T, N>, value: T) -> GenericArray<T, Sum<N, U1>>
where
	T: Clone + Ord,
	N: ArrayLength + core::ops::Add<U1, Output: ArrayLength>,
{
	/// SAFETY: Requires `dst.len() == s.len() + 1`.
	unsafe fn insert_sorted_inner<T>(dst: &mut [core::mem::MaybeUninit<T>], s: &[T], value: T) where T: Clone + Ord {
		unsafe { core::hint::assert_unchecked(dst.len() == s.len() + 1); }

		let (Ok(i) | Err(i)) = s.binary_search(&value);
		dst[..i].write_clone_of_slice(&s[..i]);
		dst[i].write(value);
		dst[i + 1..].write_clone_of_slice(&s[i..]);
	}

	let mut result = GenericArray::uninit();
	unsafe { insert_sorted_inner(&mut result, s, value); }
	// SAFETY: `insert_sorted_inner` initializes all elements.
	unsafe { GenericArray::assume_init(result) }
}

fn to_kou(tile: Tile, new_tile_i: Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld {
	if let Some((_, tsumo_or_ron)) = new_tile_i {
		ScorableHandFourthMeld::kou(tile, tsumo_or_ron, KouWait::Shanpon)
	}
	else {
		ScorableHandFourthMeld::tanki(ScorableHandMeld::Ankou(tile))
	}
}

// SAFETY: `new_tile_i` must be `None` or `Some((0..=2, _))`.
unsafe fn to_shun(tile: ShunLowTileAndHasFiveRed, new_tile_i: Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld {
	match new_tile_i {
		None => ScorableHandFourthMeld::tanki(ScorableHandMeld::Anjun(tile)),
		Some((0, tsumo_or_ron)) => {
			let wait = if tile.remove_red().number() == ShunLowNumber::Seven { ShunWait::Penchan } else { ShunWait::RyanmenLow };
			ScorableHandFourthMeld::shun(tile, tsumo_or_ron, wait)
		},
		Some((1, tsumo_or_ron)) => ScorableHandFourthMeld::shun(tile, tsumo_or_ron, ShunWait::Kanchan),
		Some((2, tsumo_or_ron)) => {
			let wait = if tile.remove_red().number() == ShunLowNumber::One { ShunWait::Penchan } else { ShunWait::RyanmenHigh };
			ScorableHandFourthMeld::shun(tile, tsumo_or_ron, wait)
		},
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

// SAFETY: `new_tile_i` must be `None` or `Some((0..=2, _))`.
unsafe fn to_meld(t1: Tile, t2: Tile, t3: Tile, new_tile_i: Option<(usize, TsumoOrRon)>) -> Option<ScorableHandFourthMeld> {
	if let Some(tile) = Tile::kou_representative(t1, t2, t3) {
		Some(to_kou(tile, new_tile_i))
	}
	else if
		let Ok(t1) = ShunLowTile::try_from(t1) &&
		let Ok(t2) = NumberTile::try_from(t2) &&
		let Ok(t3) = NumberTile::try_from(t3) &&
		let Some(tile) = ShunLowTileAndHasFiveRed::new(t1, t2, t3)
	{
		Some(unsafe { to_shun(tile, new_tile_i) })
	}
	else {
		None
	}
}

/// Finds a meld from the given tiles.
///
/// When `N == 3`, using `to_meld` is more efficient.
type Melds1AndRest<N> = ArrayVecIntoIter<(ScorableHandFourthMeld, GenericArray<Tile, Diff<N, U3>>, Option<(usize, TsumoOrRon)>), U4>;

fn to_meld_and_rest<N>(ts: GenericArray<Tile, N>, new_tile_i: Option<(usize, TsumoOrRon)>) -> Melds1AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>,
	GenericArray<Tile, N>: Copy,
{
	fn to_meld_and_rest_inner<N, TRest>(
		ts: GenericArray<Tile, N>,
		new_tile_i: Option<(usize, TsumoOrRon)>,
		t1_is_new: bool,
		t2_expected: TRest,
		t3_expected: TRest,
		t_rest_f: impl Fn(Tile) -> Result<TRest, ()>,
		mut meld_f: impl FnMut(TRest, TRest, Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld,
		meld_and_rests: &mut ArrayVec<(ScorableHandFourthMeld, GenericArray<Tile, Diff<N, U3>>, Option<(usize, TsumoOrRon)>), U4>,
	)
	where
		N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>,
		TRest: CmpIgnoreRed + Copy,
		GenericArray<Tile, N>: Copy,
	{
		let mut found_non_tanki = false;
		let mut found_tanki = t1_is_new;

		let mut find_t2 = find_tile_f(new_tile_i, t1_is_new, t2_expected, &t_rest_f, 1);
		for (i2, &t2) in ts[1..(N::USIZE - 1)].iter().enumerate() {
			match find_t2(i2, t2) {
				FindTile::Found(i2, t2, t2_is_new) => {
					let mut find_t3 = find_tile_f(new_tile_i, t1_is_new || t2_is_new, t3_expected, &t_rest_f, 1 + i2);
					for (i3, &t3) in ts[(1 + i2)..].iter().enumerate() {
						match find_t3(i3, t3) {
							FindTile::Found(i3, t3, _) => {
								let (new_tile_i_this, new_tile_i_rest) = extract_new_tile_i(new_tile_i, i2, i3);
								let meld = meld_f(t2, t3, new_tile_i_this);
								let result = if meld.is_tanki() { &mut found_tanki } else { &mut found_non_tanki };
								if !core::mem::replace(result, true) {
									let rest = unsafe { except(&ts, [0, i2, i3].into()) };
									unsafe { meld_and_rests.push_unchecked((meld, rest, new_tile_i_rest)); }
									if found_tanki && found_non_tanki {
										return;
									}
								}
							},

							FindTile::Continue => (),

							FindTile::Done => break,
						}
					}
				},

				FindTile::Continue => (),

				FindTile::Done => break,
			}
		}
	}

	enum FindTile<TRest> {
		Found(usize, TRest, bool),
		Continue,
		Done,
	}

	// TODO(rustup): Would be nice to do this with `.scan()`, but that generates more verbose and slower code.
	fn find_tile_f<TRest>(
		new_tile_i: Option<(usize, TsumoOrRon)>,
		already_have_new_tile: bool,
		t_next_expected: TRest,
		t_rest_f: impl Fn(Tile) -> Result<TRest, ()>,
		i_offset: usize,
	) -> impl FnMut(usize, Tile) -> FindTile<TRest>
	where
		TRest: CmpIgnoreRed,
	{
		let mut found_t_next_old = false;
		let mut found_t_next_new = already_have_new_tile;

		move |i_next, t_next| {
			let Ok(t_next) = t_rest_f(t_next) else { return FindTile::Continue; };
			match t_next.cmp_ignore_red(&t_next_expected) {
				core::cmp::Ordering::Less => return FindTile::Continue,
				core::cmp::Ordering::Equal => (),
				core::cmp::Ordering::Greater => return FindTile::Done,
			}

			let i_next = i_next + i_offset;
			if matches!(new_tile_i, Some((i, _)) if i == i_next) {
				if !core::mem::replace(&mut found_t_next_new, true) {
					return FindTile::Found(i_next, t_next, true);
				}
			}
			else if !core::mem::replace(&mut found_t_next_old, true) {
				return FindTile::Found(i_next, t_next, false);
			}

			// If we already have a new tile, then we only need to find one tile that is an old tile.
			// If we don't already have a new tile, we need to find one tile that is an old tile and one tile that is a new tile.
			if found_t_next_old && found_t_next_new {
				FindTile::Done
			}
			else {
				FindTile::Continue
			}
		}
	}

	fn extract_new_tile_i(
		new_tile_i: Option<(usize, TsumoOrRon)>,
		i2: usize,
		i3: usize,
	) -> (Option<(usize, TsumoOrRon)>, Option<(usize, TsumoOrRon)>) {
		let Some((i, tsumo_or_ron)) = new_tile_i else { return (None, None); };

		// Micro-optimization: Doing it this way generates only one branch for the above check.
		// The implementation of the rest of the function below is branchless and uses no stack.
		//
		// These alternatives were tested and rejected:
		//
		// - `match 0.cmp(&i) { Less => match i2.cmp(&i) { Less => match i3.cmp(i) { ...` -
		//   `match` tree, generates many branches
		//
		// - `if i == 0 { ... } else if i == i2 { ... } else if i == i3 { ... } else { i - usize::from(i > 0) - usize::from(i > i2) - usize::from(i > i3) }` -
		//   if-ladder, generates many branches
		//
		// - `match [0, i2, i3].iter().position(|&i_| i_ == i) { Some(i) => i, None => i - usize::from(i > 0) - usize::from(i > i2) - usize::from(i > i3) }` -
		//   linear search, generates branches
		//
		// - `match [0, i2, i3].into_iter().enumerate().find_map(|(i, curr)| match curr.cmp(&i) { Less => None, Equal => Some(Ok(i)) | Greater => Some(Err(i)) }) { Ok(i) => i, Err(i) => new_tile - i }` -
		//   linear search that short-circuits, generates many branches
		//
		// - `match [0, i2, i3].binary_search(&i) { Ok(i) => i, Err(i) => new_tile - i }` -
		//   binary search, generates a branch, and uses stack space because of internal `core::hint::select_unpredictable`

		// Although each `cmp()` returns one of three values, not all 27 combinations are possible, because we know that 0 < i2 < i3.
		// Only six combinations are possible, and the sum of the `cmp()` values (after incrementing each by 1 to make it non-negative) ends up being unique.
		//
		//             | i.cmp(0) | i.cmp(i2) | i.cmp(i3) | sum           | new_tile_i_this | new_tile_i_rest
		// ============+==========+===========+===========+===============+=================+=================
		// i == 0      | Equal    | Less      | Less      | 1 + 0 + 0 = 1 | Some(0)         | None
		// 0 < i < i2  | Greater  | Less      | Less      | 2 + 0 + 0 = 2 | None            | Some(i - 1)
		// i == i2     | Greater  | Equal     | Less      | 2 + 1 + 0 = 3 | Some(1)         | None
		// i2 < i < i3 | Greater  | Greater   | Less      | 2 + 2 + 0 = 4 | None            | Some(i - 2)
		// i == i3     | Greater  | Greater   | Equal     | 2 + 2 + 1 = 5 | Some(2)         | None
		// i3 < i      | Greater  | Greater   | Greater   | 2 + 2 + 2 = 6 | None            | Some(i - 3)
		let sum = (i.cmp(&0) as isize + 1 + i.cmp(&i2) as isize + 1 + i.cmp(&i3) as isize + 1).cast_unsigned();
		// Doing `if sum.is_multiple_of(2) { ... } else { ... }` generates a branch. Doing `core::hint::select_unpredictable(sum.is_multiple_of(2), ..., ...)` uses stack space.
		// This `.then_some()` approach generates no branches and uses no stack.
		let new_tile_i_this = (!sum.is_multiple_of(2)).then_some((sum >> 1, tsumo_or_ron));
		let new_tile_i_rest = sum.is_multiple_of(2).then_some((i - (sum >> 1), tsumo_or_ron));
		(new_tile_i_this, new_tile_i_rest)
	}

	let mut result = ArrayVec::new();

	let t1 = ts[0];
	let t1_is_new = matches!(new_tile_i, Some((0, _)));

	// There are at most two unique kous:
	//
	// - Any kous that use the new tile will be formed as `ScorableHandFourthMeld::Shanpon`, and we only need one of them.
	//
	// - Any kous that don't use the new tile will be formed as `ScorableHandFourthMeld::Tanki`, and we only need one of them.
	//
	// If t1 is the new tile, then only the `ScorableHandFourthMeld::Shanpon` will be found so we don't need to look for the `ScorableHandFourthMeld::Tanki`.
	to_meld_and_rest_inner(
		ts, new_tile_i, t1_is_new, t1, t1, Ok,
		|t2, t3, new_tile_i| {
			let tile = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
			to_kou(tile, new_tile_i)
		},
		&mut result,
	);

	// There are at most two unique shuns.
	//
	// - Any shuns that use the new tile will be formed as `ScorableHandFourthMeld::{Kanchan | Penchan | RyanmenLow | RyanmenHigh}`, and we only need one of them.
	//   It doesn't matter which one we pick, since the ones we didn't pick will be found when the caller searches for melds in the `Tanki` result's `rest` tiles.
	//
	//   Eg if the tiles are 2334556s + 4s, the search will produce these:
	//
	//   [2334556s + 4s]
	//   -> { anjun 2s 3s 4s ryanmen_high }, [344556s]
	//       -> { anjun 2s 3s 4s ryanmen_high }, { anjun 3s 4s 5s }, [456s]
	//           -> { anjun 2s 3s 4s ryanmen_high }, { anjun 3s 4s 5s }, { anjun 4s 5s 6s }
	//   -> { anjun 2s 3s 4s }, [34556s + 4s]
	//       -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s kanchan }, [456s]
	//           -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s kanchan }, { anjun 4s 5s 6s }
	//       -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s }, [56s + 4s]
	//           -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s }, { anjun 4s 5s 6s ryanmen_low }
	//
	//   ... which are indeed all the sets of melds that can be formed from the given tiles.
	//
	// - Any shuns that don't use the new tile will be formed as `ScorableHandFourthMeld::Tanki`, and we only need one of them.
	//
	// If t1 is the new tile, then only the `ScorableHandFourthMeld::{Kanchan | Penchan | RyanmenLow | RyanmenHigh}` will be found so we don't need to look for the `ScorableHandFourthMeld::Tanki`.
	if let Ok(t1) = ShunLowTile::try_from(t1) {
		let (t2_expected, t3_expected) = t1.shun_rest();
		to_meld_and_rest_inner(
			ts, new_tile_i, t1_is_new, t2_expected, t3_expected, NumberTile::try_from,
			|t2, t3, new_tile_i| {
				let tile = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
				// SAFETY: `new_tile_i` is guaranteed to be `None` or `Some((0..=2, _))` by the implementation of `to_meld_and_rest_inner`.
				unsafe { to_shun(tile, new_tile_i) }
			},
			&mut result,
		);
	}

	result.into_iter()
}

/// Finds two melds from the given six tiles.
#[derive(Clone, Debug, Default)]
struct Melds2 {
	mas: Dedup<Melds1AndRest<U6>>,
}

impl Melds2 {
	fn new(ts: GenericArray<Tile, U6>, new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mas = Dedup::new(to_meld_and_rest(ts, new_tile_i));
		Self { mas }
	}
}

impl Iterator for Melds2 {
	type Item = (ScorableHandMeld, ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, ts, new_tile_i) = self.mas.next()?;
			let [t1, t2, t3] = ts.into();
			// SAFETY: `new_tile_i` is guaranteed to be `None` or `Some((0..=2, _))` by the implementation of `Melds1AndRest`.
			let Some(mb) = (unsafe { to_meld(t1, t2, t3, new_tile_i) }) else { continue; };
			let (m3, m4) = sort_melds2(ma, mb);
			break Some((m3, m4));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.mas.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Melds2 where Dedup<Melds1AndRest<U6>>: core::iter::FusedIterator {}

/// Finds two melds from the given tiles.
///
/// When `N == 6`, using `Melds2` is more efficient.
#[derive(Default)]
struct Melds2AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>,
{
	ma: Option<ScorableHandFourthMeld>,
	mbs: Melds1AndRest<Diff<N, U3>>,
	mas: Dedup<Melds1AndRest<N>>,
}

impl<N> Melds2AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>,
	GenericArray<Tile, N>: Copy,
{
	fn new(ts: GenericArray<Tile, N>, new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mas = Dedup::new(to_meld_and_rest(ts, new_tile_i));
		Self {
			ma: None,
			mbs: Default::default(),
			mas,
		}
	}
}

impl<N> Clone for Melds2AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>,
{
	fn clone(&self) -> Self {
		Self {
			ma: self.ma,
			mbs: self.mbs.clone(),
			mas: self.mas.clone(),
		}
	}
}

impl<N> core::fmt::Debug for Melds2AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Melds2AndRest")
			.field("ma", &self.ma)
			.field("mbs", &self.mbs)
			.field("mas", &self.mas)
			.finish()
	}
}

impl<N> Iterator for Melds2AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>,
	GenericArray<Tile, Diff<N, U3>>: Copy,
{
	type Item = (ScorableHandMeld, ScorableHandFourthMeld, GenericArray<Tile, Diff<Diff<N, U3>, U3>>, Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ma =
				if let Some(ma) = self.ma {
					ma
				}
				else {
					let (ma, ts, new_tile_i) = self.mas.next()?;
					self.mbs = to_meld_and_rest(ts, new_tile_i);
					*self.ma.insert(ma)
				};

			let Some((mb, ts, new_tile_i)) = self.mbs.next() else {
				self.ma = None;
				continue;
			};

			let (ma, mb) = sort_melds2(ma, mb);
			break Some((ma, mb, ts, new_tile_i));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.mas.size_hint() == (0, Some(0)) {
			let (_, hi) = self.mbs.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl<N> core::iter::FusedIterator for Melds2AndRest<N>
where
	Self: Iterator,
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>,
	Dedup<Melds1AndRest<N>>: core::iter::FusedIterator,
	Melds1AndRest<Diff<N, U3>>: core::iter::FusedIterator,
{}

/// Finds three melds from the given nine tiles.
#[derive(Clone, Debug, Default)]
struct Melds3 {
	mabs: Dedup<Melds2AndRest<U9>>,
}

impl Melds3 {
	fn new(ts: GenericArray<Tile, U9>, new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabs = Dedup::new(Melds2AndRest::new(ts, new_tile_i));
		Self { mabs }
	}
}

impl Iterator for Melds3 {
	type Item = ([ScorableHandMeld; 2], ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, mb, ts, new_tile_i) = self.mabs.next()?;
			let [t1, t2, t3] = ts.into();
			// SAFETY: `new_tile_i` is guaranteed to be `None` or `Some((0..=2, _))` by the implementation of `Melds2AndRest`.
			let Some(mc) = (unsafe { to_meld(t1, t2, t3, new_tile_i) }) else { continue; };
			let (m23, m4) = sort_melds3(ma, mb, mc);
			break Some((m23, m4));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.mabs.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Melds3 where Dedup<Melds2AndRest<U9>>: core::iter::FusedIterator {}

/// Finds three melds from the given tiles.
///
/// When `N == 9`, using `Melds3` is more efficient.
#[derive(Default)]
struct Melds3AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>>,
	GenericArray<Tile, Diff<N, U3>>: Copy,
{
	mab: Option<(ScorableHandMeld, ScorableHandFourthMeld)>,
	mcs: Melds1AndRest<Diff<Diff<N, U3>, U3>>,
	mabs: Dedup<Melds2AndRest<N>>,
}

impl<N> Melds3AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>>,
	GenericArray<Tile, N>: Copy,
	GenericArray<Tile, Diff<N, U3>>: Copy,
{
	fn new(ts: GenericArray<Tile, N>, new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabs = Dedup::new(Melds2AndRest::new(ts, new_tile_i));
		Self {
			mab: None,
			mcs: Default::default(),
			mabs,
		}
	}
}

impl<N> Clone for Melds3AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>>,
	GenericArray<Tile, Diff<N, U3>>: Copy,
{
	fn clone(&self) -> Self {
		Self {
			mab: self.mab,
			mcs: self.mcs.clone(),
			mabs: self.mabs.clone(),
		}
	}
}

impl<N> core::fmt::Debug for Melds3AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>>,
	GenericArray<Tile, Diff<N, U3>>: Copy,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Melds2AndRest")
			.field("mab", &self.mab)
			.field("mcs", &self.mcs)
			.field("mabs", &self.mabs)
			.finish()
	}
}

impl<N> Iterator for Melds3AndRest<N>
where
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>>,
	GenericArray<Tile, Diff<N, U3>>: Copy,
	GenericArray<Tile, Diff<Diff<N, U3>, U3>>: Copy,
{
	type Item = ([ScorableHandMeld; 2], ScorableHandFourthMeld, GenericArray<Tile, Diff<Diff<Diff<N, U3>, U3>, U3>>, Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, mb) =
				if let Some(mab) = self.mab {
					mab
				}
				else {
					let (ma, mb, ts, new_tile_i) = self.mabs.next()?;
					self.mcs = to_meld_and_rest(ts, new_tile_i);
					*self.mab.insert((ma, mb))
				};

			let Some((mc, ts, new_tile_i)) = self.mcs.next() else {
				self.mab = None;
				continue;
			};

			let (mab, mc) = sort_melds3(ma, mb, mc);
			break Some((mab, mc, ts, new_tile_i));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.mabs.size_hint() == (0, Some(0)) {
			let (_, hi) = self.mcs.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl<N> core::iter::FusedIterator for Melds3AndRest<N>
where
	Self: Iterator,
	N: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength + core::ops::Sub<U3, Output: ArrayLength>>>,
	GenericArray<Tile, Diff<N, U3>>: Copy,
	Dedup<Melds2AndRest<N>>: core::iter::FusedIterator,
	Melds1AndRest<Diff<Diff<N, U3>, U3>>: core::iter::FusedIterator,
{}

/// Finds four melds from the given twelve tiles.
#[derive(Clone, Debug, Default)]
struct Melds4 {
	mabcs: Dedup<Melds3AndRest<U12>>,
}

impl Melds4 {
	fn new(ts: GenericArray<Tile, U12>, new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabcs = Dedup::new(Melds3AndRest::new(ts, new_tile_i));
		Self { mabcs }
	}
}

impl Iterator for Melds4 {
	type Item = ([ScorableHandMeld; 3], ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ([ma, mb], mc, ts, new_tile_i) = self.mabcs.next()?;
			let [t1, t2, t3] = ts.into();
			// SAFETY: `new_tile_i` is guaranteed to be `None` or `Some((0..=2, _))` by the implementation of `Melds3AndRest`.
			let Some(md) = (unsafe { to_meld(t1, t2, t3, new_tile_i) }) else { continue; };
			let (m123, m4) = sort_melds4(ma, mb, mc, md);
			break Some((m123, m4));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.mabcs.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Melds4 where Dedup<Melds3AndRest<U12>>: core::iter::FusedIterator {}

fn sort_melds2(ma: ScorableHandFourthMeld, mb: ScorableHandFourthMeld) -> (ScorableHandMeld, ScorableHandFourthMeld) {
	match (ma.to_tanki(), mb.to_tanki()) {
		(Some(ma), Some(mb)) => {
			let (ma, mb) = if ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb) { (ma, mb) } else { (mb, ma) };
			(ma, ScorableHandFourthMeld::tanki(mb))
		},

		(Some(ma), None) => (ma, mb),
		(None, Some(mb)) => (mb, ma),

		// At most one meld can be non-tanki
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn sort_melds3(ma: ScorableHandMeld, mb: ScorableHandFourthMeld, mc: ScorableHandFourthMeld) -> ([ScorableHandMeld; 2], ScorableHandFourthMeld) {
	match (mb.to_tanki(), mc.to_tanki()) {
		(Some(mb), Some(mc)) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb));

			let (mb, mc) = if ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&mc) { (mb, mc) } else { (mc, mb) };
			let mab = if ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb) { [ma, mb] } else { [mb, ma] };
			(mab, ScorableHandFourthMeld::tanki(mc))
		},

		(Some(mb), None) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb));

			([ma, mb], mc)
		},

		(None, Some(mc)) => {
			let mab = if ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mc) { [ma, mc] } else { [mc, ma] };
			(mab, mb)
		},

		// At most one meld can be non-tanki
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn sort_melds4(ma: ScorableHandMeld, mb: ScorableHandMeld, mc: ScorableHandFourthMeld, md: ScorableHandFourthMeld) -> ([ScorableHandMeld; 3], ScorableHandFourthMeld) {
	debug_assert!(ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb));

	match (mc.to_tanki(), md.to_tanki()) {
		(Some(mc), Some(md)) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&mc));

			let (mc, md) = if ScorableHandMeldSortCriteria::new(&mc) <= ScorableHandMeldSortCriteria::new(&md) { (mc, md) } else { (md, mc) };
			let (mb, mc) = if ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&mc) { (mb, mc) } else { (mc, mb) };
			let (ma, mb) = if ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb) { (ma, mb) } else { (mb, ma) };
			([ma, mb, mc], ScorableHandFourthMeld::tanki(md))
		},

		(Some(mc), None) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&mc));

			([ma, mb, mc], md)
		},

		(None, Some(md)) => {
			let (mb, md) = if ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&md) { (mb, md) } else { (md, mb) };
			let (ma, mb) = if ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb) { (ma, mb) } else { (mb, ma) };
			([ma, mb, md], mc)
		},

		// At most one meld can be non-tanki
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

#[derive(Clone, Debug)]
struct Dedup<I> where I: Iterator {
	inner: I,
	prev: Option<I::Item>,
}

impl<I> Dedup<I> where I: Iterator {
	const fn new(inner: I) -> Self {
		Self { inner, prev: None }
	}
}

impl<I> Default for Dedup<I> where I: Default + Iterator {
	fn default() -> Self {
		Self {
			inner: Default::default(),
			prev: None,
		}
	}
}

impl<I> Iterator for Dedup<I> where I: Iterator, I::Item: PartialEq {
	type Item = I::Item;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some(item) = self.inner.next() else { return self.prev.take(); };
			let Some(prev) = self.prev.take() else { self.prev = Some(item); continue; };
			if item == prev {
				self.prev = Some(prev);
			}
			else {
				self.prev = Some(item);
				return Some(prev);
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (lo, hi) = self.inner.size_hint();
		let lo = lo.saturating_add(self.prev.is_some().into()).min(1);
		let hi = hi.and_then(|hi| hi.checked_add(self.prev.is_some().into()));
		(lo, hi)
	}
}

impl<I> core::iter::FusedIterator for Dedup<I> where Self: Iterator, I: core::iter::FusedIterator {}

#[derive(Clone, Copy, Debug)]
enum ToKokushiMusou {
	Invalid,
	Single { wait: Tile, duplicate: Tile },
	Any,
}

impl ToKokushiMusou {
	fn new(ts: &[Tile; 13]) -> Self {
		let Some((duplicate, remaining)) = Self::new_inner(ts) else { return Self::Invalid; };

		let mut remaining = remaining.into_iter();
		let wait = remaining.next();
		if remaining.next().is_some() { return Self::Invalid; }
		match wait {
			Some(wait) => {
				// SAFETY: Pigeonhole principle. To get here, twelve elements were removed from `waits`,
				// and the thirteenth tile in `ts` was one of those twelve and thus written to `duplicate`.
				let duplicate = unsafe { duplicate.assume_init() };
				Self::Single { wait, duplicate }
			},
			None => Self::Any,
		}
	}

	fn with_new_tile(self, new_tile: Tile) -> Option<ScorableHand> {
		match self {
			Self::Invalid => None,
			Self::Single { wait, duplicate } => (wait == new_tile).then_some(ScorableHand::KokushiMusou(ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: false })),
			Self::Any => Tile34Set::KOKUSHI_MUSOU_VALID.contains(new_tile).then_some(ScorableHand::KokushiMusou(ScorableHandKokushiMusou { duplicate: new_tile, was_juusanmen_wait: true })),
		}
	}

	fn tenhou(ts: &[Tile; 14]) -> Option<ScorableHand> {
		let (duplicate, remaining) = Self::new_inner(ts)?;
		remaining.is_empty().then(|| {
			// SAFETY: Pigeonhole principle. To get here, thirteen elements were removed from `waits`,
			// and the fourteenth tile in `ts` was one of those thirteen and thus written to `duplicate`.
			let duplicate = unsafe { duplicate.assume_init() };
			ScorableHand::KokushiMusou(ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: true })
		})
	}

	fn new_inner(ts: &[Tile]) -> Option<(core::mem::MaybeUninit<Tile>, Tile34Set)> {
		let mut waits = Tile34Set::KOKUSHI_MUSOU_VALID;
		let mut duplicate = core::mem::MaybeUninit::uninit();
		for &t in ts {
			if !Tile34Set::KOKUSHI_MUSOU_VALID.contains(t) { return None; }
			if !waits.remove(t) {
				duplicate.write(t);
			}
		}
		Some((duplicate, waits))
	}
}

fn to_chiitoi(ts: &[Tile; 14]) -> Option<ScorableHand> {
	// Ref: https://rust.godbolt.org/z/9d9qYxrW9

	let (is_valid, pairs) = cfg_select! {
		all(target_arch = "riscv64", target_feature = "v") => {{
			// The scalar impl below this one does auto-vectorize on RV+v but very badly - it generates a large amount of code that does ops with
			// `vl = 4` instead of `vl = 14`.
			//
			// So we do it manually with inline asm.

			let pairs: u64;
			let adjacents_are_eq: u64;
			unsafe {
				core::arch::asm!(
					// let ts = unsafe { &*<*const [Tile; 14]>::cast::<[u8; 14]>(ts) };
					// let ts /* : v8:v8 */ = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 14, e8, m1, ta, ma",
					"vle8.v v8, ({ts})",

					// let ts_shifted /* : v9:v9 */ = ts.extract::<1, 13>();
					// let ts = ts.extract::<0, 13>();
					"vsetivli zero, 13, e8, m1, ta, ma",
					"vslidedown.vi v9, v8, 1",

					// let adjacents_are_eq /* : v10 */ = ts ^ ts_shifted;
					"vxor.vv v10, v8, v9",
					// let adjacents_are_eq /* : v10 */ = core::simd::cmp::SimdPartialOrd::simd_le(adjacents_are_eq, core::simd::Simd::splat(1));
					"vmsleu.vi v10, v10, 1",

					// let pairs /* : v8:v8 */ = ts | ts_shifted;
					"vor.vv v8, v8, v9",
					// let pairs = pairs.resize::<14>(0);
					// let pairs = unsafe { core::mem::transmute::<core::simd::Simd<u8, 14>, core::simd::Simd<u16, 7>>(pairs) };
					// let pairs /* : v8:v8 */ = core::simd::num::SimdUint::cast::<u8>(pairs);
					"vsetivli zero, 7, e8, m1, ta, ma",
					// Note: Per the ISA spec, the canonical way to do this would be `vncvt.x.x.w v8, v8`, ie `vnsrl.wx v8, v8, zero`,
					// But compilers prefer to do it with zero immediate instead of zero integer register to avoid cross-register file interaction.
					//
					// Ref: https://inbox.sourceware.org/gcc-patches/20250207162212.66994-1-vineetg@rivosinc.com/T/
					// Ref: https://inbox.sourceware.org/gcc-patches/20250208043433.86154-1-vineetg@rivosinc.com/T/
					// Ref: https://reviews.llvm.org/D132041
					"vnsrl.wi v8, v8, 0",

					// let adjacents_are_eq = adjacents_are_eq.to_bitmask();
					"vsetvli zero, zero, e64, m1, ta, ma",
					"vmv.x.s {adjacents_are_eq}, v10",
					// let pairs = pairs.to_array();
					"vmv.x.s {pairs}, v8",

					ts = in(reg) ts.as_ptr(),
					out("v8") _,
					out("v9") _,
					out("v10") _,
					pairs = lateout(reg) pairs,
					adjacents_are_eq = lateout(reg) adjacents_are_eq,
					options(nostack),
				);
			}
			let pairs = pairs.to_le_bytes();
			let pairs = [pairs[0], pairs[1], pairs[2], pairs[3], pairs[4], pairs[5], pairs[6]];
			(adjacents_are_eq & 0x1FFF == 0x1555, pairs)
		}},

		_ => {{
			// Scalar impl is optimal on RV-v.

			let mut pairs = [0_u8; 7];
			let mut is_valid = true;
			for (i, &[a, b]) in ts.as_chunks().0.iter().enumerate() {
				pairs[i] = a as u8 | b as u8;
				is_valid &= a.eq_ignore_red(&b);
			}
			for &[a, b] in ts[1..].as_chunks().0 {
				is_valid &= a.ne_ignore_red(&b);
			}
			(is_valid, pairs)
		}},
	};

	is_valid.then(|| {
		// SAFETY: All `u8`s in `Result` are guaranteed to be valid `Tile` values, since every `a` and `b` that went into them were either identical
		// or one was a `Five` and the other was a `FiveRed`. Thus transmuting each `u8` to `Tile` is guaranteed to produce a valid `Tile`.
		let pairs = unsafe { core::mem::transmute::<[u8; 7], [Tile; 7]>(pairs) };
		let pairs = pairs.map(ScorableHandPair);
		ScorableHand::Chiitoi(ScorableHandChiitoi(pairs))
	})
}

#[cfg(test)]
mod tests {
	extern crate std;

	use crate::Tile37Set;
	use super::*;

	fn melds() -> [ScorableHandMeld; 16] {
		[
			make_scorable_hand!(@meld { ankou 1s 1s 1s }),
			make_scorable_hand!(@meld { ankou 2s 2s 2s }),
			make_scorable_hand!(@meld { ankou 3s 3s 3s }),
			make_scorable_hand!(@meld { ankou 4s 4s 4s }),
			make_scorable_hand!(@meld { ankou 5s 5s 5s }),
			make_scorable_hand!(@meld { ankou 6s 6s 6s }),
			make_scorable_hand!(@meld { ankou 7s 7s 7s }),
			make_scorable_hand!(@meld { ankou 8s 8s 8s }),
			make_scorable_hand!(@meld { ankou 9s 9s 9s }),
			make_scorable_hand!(@meld { anjun 1s 2s 3s }),
			make_scorable_hand!(@meld { anjun 2s 3s 4s }),
			make_scorable_hand!(@meld { anjun 3s 4s 5s }),
			make_scorable_hand!(@meld { anjun 4s 5s 6s }),
			make_scorable_hand!(@meld { anjun 5s 6s 7s }),
			make_scorable_hand!(@meld { anjun 6s 7s 8s }),
			make_scorable_hand!(@meld { anjun 7s 8s 9s }),
		]
	}

	fn melds_last() -> [ScorableHandFourthMeld; 30] {
		[
			make_scorable_hand!(@meldr4 { ankou 1s 1s 1s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 2s 2s 2s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 3s 3s 3s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 4s 4s 4s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 5s 5s 5s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 6s 6s 6s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 7s 7s 7s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 8s 8s 8s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 9s 9s 9s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s penchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s penchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s ryanmen_high }),
		]
	}

	fn to_ttrs(meld: ScorableHandFourthMeld) -> [(Tile, Option<TsumoOrRon>); 3] {
		let tsumo_or_ron = match meld {
			ScorableHandFourthMeld::Ankan(..) |
			ScorableHandFourthMeld::Minkan(..) |
			ScorableHandFourthMeld::Ankou(..) |
			ScorableHandFourthMeld::Minkou(_, KouWait::Tanki) |
			ScorableHandFourthMeld::Anjun(..) |
			ScorableHandFourthMeld::Minjun(_, ShunWait::Tanki)
				=> TsumoOrRon::Tsumo,

			ScorableHandFourthMeld::Minkou(_, KouWait::Shanpon) |
			ScorableHandFourthMeld::Minjun(_, ShunWait::Kanchan | ShunWait::Penchan | ShunWait::RyanmenLow | ShunWait::RyanmenHigh)
				=> TsumoOrRon::Ron,
		};

		match meld {
			ScorableHandFourthMeld::Ankou(t, KouWait::Tanki) => [(t, None), (t, None), (t, None)],

			ScorableHandFourthMeld::Anjun(t, ShunWait::Tanki) => {
				let (t1, t2, t3) = t.shun();
				[(t1.into(), None), (t2.into(), None), (t3.into(), None)]
			},

			ScorableHandFourthMeld::Ankou(t, KouWait::Shanpon) |
			ScorableHandFourthMeld::Minkou(t, KouWait::Shanpon) => [(t, None), (t, None), (t, Some(tsumo_or_ron))],

			ScorableHandFourthMeld::Anjun(t, ShunWait::Kanchan) |
			ScorableHandFourthMeld::Minjun(t, ShunWait::Kanchan) => {
				let (t1, t2, t3) = t.shun();
				[(t1.into(), None), (t2.into(), Some(tsumo_or_ron)), (t3.into(), None)]
			},

			ScorableHandFourthMeld::Anjun(t, ShunWait::Penchan) |
			ScorableHandFourthMeld::Minjun(t, ShunWait::Penchan) => {
				let (t1, t2, t3) = t.shun();
				[(t1.into(), matches!(t1, tn!(7m | 7p | 7s)).then_some(tsumo_or_ron)), (t2.into(), None), (t3.into(), matches!(t3, tn!(3m | 3p | 3s)).then_some(tsumo_or_ron))]
			},

			ScorableHandFourthMeld::Anjun(t, ShunWait::RyanmenLow) |
			ScorableHandFourthMeld::Minjun(t, ShunWait::RyanmenLow) => {
				let (t1, t2, t3) = t.shun();
				[(t1.into(), Some(tsumo_or_ron)), (t2.into(), None), (t3.into(), None)]
			},

			ScorableHandFourthMeld::Anjun(t, ShunWait::RyanmenHigh) |
			ScorableHandFourthMeld::Minjun(t, ShunWait::RyanmenHigh) => {
				let (t1, t2, t3) = t.shun();
				[(t1.into(), None), (t2.into(), None), (t3.into(), Some(tsumo_or_ron))]
			},

			_ => unreachable!(),
		}
	}

	#[test]
	fn to_meld() {
		for expected in melds_last() {
			let [(t1, t1tr), (t2, t2tr), (t3, t3tr)] = to_ttrs(expected);

			let mut ts = [(t1, t1tr), (t2, t2tr), (t3, t3tr)];
			ts.sort_unstable();
			let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));
			let [t1, t2, t3] = ts.map(|(t, _)| t);

			let actual = unsafe { super::to_meld(t1, t2, t3, new_tile_i) };
			assert_eq!(actual, Some(expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
		}

		// 124 -> X
		assert_eq!(unsafe { super::to_meld(t!(1s), t!(2s), t!(4s), None) }, None);
	}

	#[test]
	fn to_melds_2() {
		let melds = melds();
		let melds_last = melds_last();

		for ma in melds {
			let [t1, t2, t3] = match ma {
				ScorableHandMeld::Ankou(t) => [t, t, t],
				ScorableHandMeld::Anjun(t) => {
					let (t1, t2, t3) = t.shun();
					[t1, t2, t3].map(Into::into)
				},
				_ => unreachable!(),
			};
			let mut used = Tile34MultiSet::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}
			for mb in melds.into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last) {
				let [(t4, t4tr), (t5, t5tr), (t6, t6tr)] = to_ttrs(mb);

				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				let expected =
					if let Some(mb) = mb.to_tanki() {
						let mut ms = [ma, mb];
						ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
						let [m3, m4] = ms;
						(m3, ScorableHandFourthMeld::tanki(m4))
					}
					else {
						(ma, mb)
					};

				let mut ts = [(t1, None), (t2, None), (t3, None), (t4, t4tr), (t5, t5tr), (t6, t6tr)];
				ts.sort_unstable();
				let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));

				let actual: std::vec::Vec<_> = Dedup::new(Melds2::new(ts.map(|(t, _)| t).into(), new_tile_i)).collect();
				assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
			}
		}
	}

	#[test]
	fn to_melds_3() {
		let melds = melds();
		let melds_last = melds_last();

		for ma in melds {
			let [t1, t2, t3] = match ma {
				ScorableHandMeld::Ankou(t) => [t, t, t],
				ScorableHandMeld::Anjun(t) => {
					let (t1, t2, t3) = t.shun();
					[t1, t2, t3].map(Into::into)
				},
				_ => unreachable!(),
			};
			let mut used = Tile34MultiSet::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}

			for mb in melds {
				let [t4, t5, t6] = match mb {
					ScorableHandMeld::Ankou(t) => [t, t, t],
					ScorableHandMeld::Anjun(t) => {
						let (t4, t5, t6) = t.shun();
						[t4, t5, t6].map(Into::into)
					},
					_ => unreachable!(),
				};
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				for mc in melds.into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last) {
					let [(t7, t7tr), (t8, t8tr), (t9, t9tr)] = to_ttrs(mc);

					let mut used = used.clone();
					if used.try_extend([t7, t8, t9]).is_err() {
						continue;
					}

					let expected =
						if let Some(mc) = mc.to_tanki() {
							let mut ms = [ma, mb, mc];
							ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
							let [m2, m3, m4] = ms;
							([m2, m3], ScorableHandFourthMeld::tanki(m4))
						}
						else {
							let mut ms = [ma, mb];
							ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
							let [m2, m3] = ms;
							([m2, m3], mc)
						};

					let mut ts = [(t1, None), (t2, None), (t3, None), (t4, None), (t5, None), (t6, None), (t7, t7tr), (t8, t8tr), (t9, t9tr)];
					ts.sort_unstable();
					let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));

					let actual: std::vec::Vec<_> = Dedup::new(Melds3::new(ts.map(|(t, _)| t).into(), new_tile_i)).collect();
					assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
				}
			}
		}
	}

	#[test]
	fn to_melds_4() {
		let melds = melds();
		let melds_last = melds_last();

		for ma in melds {
			let [t1, t2, t3] = match ma {
				ScorableHandMeld::Ankou(t) => [t, t, t,],
				ScorableHandMeld::Anjun(t) => {
					let (t1, t2, t3) = t.shun();
					[t1, t2, t3].map(Into::into)
				},
				_ => unreachable!(),
			};
			let mut used =Tile34MultiSet::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}

			for mb in melds {
				let [t4, t5, t6] = match mb {
					ScorableHandMeld::Ankou(t) => [t, t, t,],
					ScorableHandMeld::Anjun(t) => {
						let (t4, t5, t6) = t.shun();
						[t4, t5, t6].map(Into::into)
					},
					_ => unreachable!(),
				};
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				for mc in melds {
					let [t7, t8, t9] = match mc {
						ScorableHandMeld::Ankou(t) => [t, t, t,],
						ScorableHandMeld::Anjun(t) => {
							let (t7, t8, t9) = t.shun();
							[t7, t8, t9].map(Into::into)
						},
						_ => unreachable!(),
					};
					let mut used = used.clone();
					if used.try_extend([t7, t8, t9]).is_err() {
						continue;
					}

					for md in melds.into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last) {
						let [(t10, t10tr), (t11, t11tr), (t12, t12tr)] = to_ttrs(md);

						let mut used = used.clone();
						if used.try_extend([t10, t11, t12]).is_err() {
							continue;
						}

						let expected =
							if let Some(md) = md.to_tanki() {
								let mut ms = [ma, mb, mc, md];
								ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
								let [m1, m2, m3, m4] = ms;
								([m1, m2, m3], ScorableHandFourthMeld::tanki(m4))
							}
							else {
								let mut ms = [ma, mb, mc];
								ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
								let [m1, m2, m3] = ms;
								([m1, m2, m3], md)
							};

						let mut ts = [(t1, None), (t2, None), (t3, None), (t4, None), (t5, None), (t6, None), (t7, None), (t8, None), (t9, None), (t10, t10tr), (t11, t11tr), (t12, t12tr)];
						ts.sort_unstable();
						let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));

						let actual: std::vec::Vec<_> = Dedup::new(Melds4::new(ts.map(|(t, _)| t).into(), new_tile_i)).collect();
						assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
					}
				}
			}
		}
	}

	#[test]
	fn find_ankans() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		let mut ankans = h.draw(t!(E)).find_ankans();
		assert_eq!(ankans.next().unwrap(), make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { ankan E E E E }));
		assert_eq!(ankans.next(), None);
	}

	#[test]
	fn find_daiminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		let h = h.find_daiminkan(t!(E)).unwrap();
		assert_eq!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E }));
	}

	#[test]
	fn find_shouminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkou E E E });
		let mut shouminkans = h.draw(t!(E)).find_shouminkans();
		assert_eq!(shouminkans.next().unwrap(), make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E }));
		assert_eq!(shouminkans.next(), None);
	}

	#[test]
	fn find_minkous1() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(2m));
		// 22m => 2C2 = 1
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 3m 3m 3m 4m 4m 4m 5m 5m { minkou 2m 2m 2m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous2() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(5m));
		// 55m => 2C2 = 1
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 5m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous3() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(0m));
		// 55m => 2C2 = 1
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous4() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 0m);
		let mut minkous = h.find_minkous(t!(5m));
		// 50m => 2C2 = 1
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous5() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m 5m 5m);
		let mut minkous = h.find_minkous(t!(0m));
		// 555m => 3C2 = 3
		assert_eq!(minkous.size_hint(), (0, Some(3)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
		assert_eq!(minkous.size_hint(), (0, Some(2)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous6() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m 5m 0m);
		let mut minkous = h.find_minkous(t!(5m));
		// 550m => 3C2 = 3
		assert_eq!(minkous.size_hint(), (0, Some(3)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 0m { minkou 5m 5m 5m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
		assert_eq!(minkous.size_hint(), (0, Some(2)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if h == make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let mut minjuns = h.find_minjuns(tn!(4m));
		// 23506m => 5C2 = 10
		assert_eq!(minjuns.size_hint(), (0, Some(10)));
		core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if h == make_hand!(1m 5m 0m 6m 7m 8m E E E G G { minjun 2m 3m 4m }) && allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minjuns.size_hint(), (0, Some(9)));
		core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if h == make_hand!(1m 2m 0m 6m 7m 8m E E E G G { minjun 3m 4m 5m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minjuns.size_hint(), (0, Some(5)));
		core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if h == make_hand!(1m 2m 5m 6m 7m 8m E E E G G { minjun 3m 4m 0m }) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minjuns.size_hint(), (0, Some(4)));
		core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if h == make_hand!(1m 2m 3m 0m 7m 8m E E E G G { minjun 4m 5m 6m }) && allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minjuns.size_hint(), (0, Some(1)));
		core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if h == make_hand!(1m 2m 3m 5m 7m 8m E E E G G { minjun 4m 0m 6m }) && allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]);
		assert_eq!(minjuns.size_hint(), (0, Some(0)));
		core::assert_matches!(minjuns.next(), None);
		assert_eq!(minjuns.size_hint(), (0, Some(0)));
	}

	#[test]
	fn kuikae() {
		{
			let h = make_hand!(1m 1m 1m E E E S S S W W W N);
			let mut minkous = h.find_minkous(t!(1m));
			core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m E E E S S S W W W N { minkou 1m 1m 1m }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m E E E S S S W W W N { minkou 1m 1m 1m }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minkous.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m E E E S S S W W W N { minkou 1m 1m 1m }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minkous.next(), None);
		}

		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(2p));
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(2p E E E S S S W W W N { minjun 1p 2p 3p }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(4m));
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m E E E S S S W W W N { minjun 2m 3m 4m }) &&
				allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1p 2p 3p 4p { minkou E E E } { minkou S S S } { minkou W W W });
			let mut minjuns = h.find_minjuns(tn!(1p));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let mut minjuns = h.find_minjuns(tn!(4m));
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m 4m 5m 6m E E E S S S W { minjun 2m 3m 4m }) &&
				allowed_discards == [2, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m 2m 4m 6m E E E S S S W { minjun 3m 4m 5m }) &&
				allowed_discards == [0, 1, 3, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m 2m 3m 4m E E E S S S W { minjun 4m 5m 6m }) &&
				allowed_discards == [0, 1, 2, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let mut minjuns = h.find_minjuns(tn!(7m));
			core::assert_matches!(minjuns.next(), Some((h, allowed_discards)) if
				h == make_hand!(1m 2m 3m 4m E E E S S S W { minjun 5m 6m 7m }) &&
				allowed_discards == [0, 1, 2, 4, 5, 6, 7, 8, 9, 10],
			);
			core::assert_matches!(minjuns.next(), None);
		}
	}

	#[test]
	fn tenpai() {
		{
			let h = make_hand!(5p 6p 0s 6s 7s 8s 8s Wh Wh Wh { minkou R R R });
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 4p, 7p });
		}

		{
			let h = make_hand!(4m 5m 6p 7p 8p 1s 2s 3s 4s 5s 6s 8s 8s);
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 3m, 6m });
		}

		{
			let h = make_hand!(1m 1m 4p 4p { minkou N N N } { minkou 3p 3p 3p } { minkou R R R });
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 1m, 4p });
		}

		{
			let h = make_hand!(1m 1m 4m 5m 6m 3p 4p 4p 0p 6p 1s 2s 3s);
			// TODO: Should not yield second 0p.
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 2p, 5p, 0p });
		}

		{
			let h = make_hand!(4m 4m 1p 2p 3p 0p 5p 1s 2s 3s { minjun 1m 2m 3m });
			// TODO: Should not yield second 0p.
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 4m, 5p, 0p });
		}

		{
			let h = make_hand!(3p 3p 4p 4p 0p 5p 7p 8p 8p 8p 9p G G);
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 8p, G });
		}

		{
			let h = make_hand!(4m 0m 6m 7m 7m 4s 0s 6s 7s 8s { minjun 4p 5p 6p });
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 3s, 6s, 9s });
		}

		{
			let h = make_hand!(1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m);
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m });
		}

		{
			let h = make_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R);
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R });
		}

		{
			let h = make_hand!(1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh);
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { S, });
		}

		// Red five
		{
			let h = make_hand!(1m 1m 2m 2m 2m 3m 3m 3m 4p 5p 5p 5p 6p);
			// TODO: Should not yield fourth 5p.
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 1m, 4m, 5p, 0p });
		}

		// Red five
		{
			let h = make_hand!(5m 5m 0m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			// TODO: Should not yield second 0m.
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 5m, 0m, 6m, 7m, 8m });
		}

		// Red five
		{
			let h = make_hand!(5m 5m 5m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			// TODO: Should not yield fourth 5m.
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 5m, 0m, 6m, 7m, 8m });
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand. Not considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 1m 1m 1m 3m 4m 5m 3p 4p 5p 3s 4s 5s);
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! {});
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand, but only 1x 1m in unmelded tiles. Considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 3m 4m 5m 3p 4p 5p 3s 4s 5s { minkou 1m 1m 1m });
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 1m, });
		}

		// Karaten nuance: waiting for 8p but already have 4x 8p in hand, but none in unmelded tiles. Considered to be in tenpai for fifth 8p.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447
		{
			let h = make_hand!(1p 2p 3p 4p 4p 5p 5p 5p 7p 9p { minkan 8p 8p 8p 8p });
			assert_eq!(h.tenpai(GameType::Yonma).collect::<Tile37Set>(), t37set! { 8p, });
		}
	}
}
