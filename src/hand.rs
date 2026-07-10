use generic_array::{
	ArrayLength,
	GenericArray,
	sequence::{Concat as _, Remove},
	typenum::{
		Diff,
		Sum,
		B1, U0, U1, U2, U3, U4, U5, U7, U8, U10, U11, U13, U14,
	},
};

use crate::{
	ArrayVec, ArrayVecIntoCombinations,
	CmpIgnoreRed,
	except,
	HandMeldType,
	NumberTile,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
	ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile, TileMultiSetIntoIter,
	Tile34MultiSet, Tile34MultiSetElement, Tile34Set,
	Tile37SetIntoIter,
	TsumoOrRon,
	decompose::{Lookup, LookupForNewTile, Tile37SuitedMultiSet},
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
	NT: ArrayLength + core::ops::Sub<B1, Output: ArrayLength>,
	GenericArray<Tile, NT>: Remove<Tile, NT, Output = GenericArray<Tile, Diff<NT, B1>>>,
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
	pub fn discard(self, i: usize) -> (Hand<Diff<NT, B1>, NM>, Tile) {
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
		let lookup = Lookup::new(&Tile37SuitedMultiSet::new(&ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);
		let [ma, mb, mc] = <[HandMeld; _]>::from(ms).map(Into::into);
		Hand4ScorableHands { lookup, ma, mb, mc }
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self) -> Hand4Tenpai {
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
		let ts = Tile37SuitedMultiSet::new(&ts);
		let tiles = ts.tenpai().into_iter();
		Hand4Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand4ScorableHands {
	lookup: LookupForNewTile<U0>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
	mc: ScorableHandMeld,
}

assert_size_of!(Hand4ScorableHands, 112);

impl Iterator for Hand4ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		let (ms, md, pair) = self.lookup.next()?;
		let [] = ms.into();
		Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, self.mb, self.mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.lookup.size_hint()
	}
}

impl core::iter::FusedIterator for Hand4ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand4Tenpai {
	tiles: Tile37SetIntoIter,
	ts: Tile37SuitedMultiSet<U4>,
}

assert_size_of!(Hand4Tenpai, 32);

impl Iterator for Hand4Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = self.tiles.next()?;
			if Lookup::<U1>::new(&self.ts.push(new_tile)).next().is_some() {
				return Some(new_tile);
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
		let lookup = Lookup::new(&Tile37SuitedMultiSet::new(&ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);
		let [ma, mb] = <[HandMeld; _]>::from(ms).map(Into::into);
		Hand7ScorableHands { lookup, ma, mb }
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self) -> Hand7Tenpai {
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
		let ts = Tile37SuitedMultiSet::new(&ts);
		let tiles = ts.tenpai().into_iter();
		Hand7Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand7ScorableHands {
	lookup: LookupForNewTile<U1>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
}

assert_size_of!(Hand7ScorableHands, 120);

impl Iterator for Hand7ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		let (ms, md, pair) = self.lookup.next()?;
		let [mc] = ms.into();
		Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, self.mb, mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.lookup.size_hint()
	}
}

impl core::iter::FusedIterator for Hand7ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand7Tenpai {
	tiles: Tile37SetIntoIter,
	ts: Tile37SuitedMultiSet<U7>,
}

assert_size_of!(Hand7Tenpai, 32);

impl Iterator for Hand7Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = self.tiles.next()?;
			if Lookup::<U2>::new(&self.ts.push(new_tile)).next().is_some() {
				return Some(new_tile);
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
		let lookup = Lookup::new(&Tile37SuitedMultiSet::new(&ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);
		let [ma] = <[HandMeld; _]>::from(ms).map(Into::into);
		Hand10ScorableHands { lookup, ma }
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self) -> Hand10Tenpai {
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
		let ts = Tile37SuitedMultiSet::new(&ts);
		let tiles = ts.tenpai().into_iter();
		Hand10Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand10ScorableHands {
	lookup: LookupForNewTile<U2>,
	ma: ScorableHandMeld,
}

assert_size_of!(Hand10ScorableHands, 144);

impl Iterator for Hand10ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		let (ms, md, pair) = self.lookup.next()?;
		let [mb, mc] = ms.into();
		Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, mb, mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.lookup.size_hint()
	}
}

impl core::iter::FusedIterator for Hand10ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand10Tenpai {
	tiles: Tile37SetIntoIter,
	ts: Tile37SuitedMultiSet<U10>,
}

assert_size_of!(Hand10Tenpai, 32);

impl Iterator for Hand10Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = self.tiles.next()?;
			if Lookup::<U3>::new(&self.ts.push(new_tile)).next().is_some() {
				return Some(new_tile);
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
		let lookup = Lookup::new(&Tile37SuitedMultiSet::new(&ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);

		let kokushi_musou = ToKokushiMusou::new(ts.as_ref()).with_new_tile(new_tile);

		let chiitoi = match to_chiitoi_with_pairs(ts.as_ref()) {
			Some((ps, wait)) =>
				if let Some(p7) = ScorableHandPair::new(wait, new_tile) {
					let Err(i) = ps.binary_search(&p7) else {
						// SAFETY: `to_chiitoi_with_pairs` is guaranteed to return a `t` that would not form the same pair as any of `ps`.
						unsafe { core::hint::unreachable_unchecked(); }
					};
					let mut pairs = [const { core::mem::MaybeUninit::uninit() }; 7];
					pairs[..i].write_copy_of_slice(&ps[..i]);
					pairs[i].write(p7);
					pairs[i + 1..].write_copy_of_slice(&ps[i..]);
					// TODO(rustup): Use `MaybeUninit::array_assume_init` when that is stabilized.
					// SAFETY: Inserting an element into a `[; 6]` initializes all elements of the resulting `[; 7]`.
					let pairs = unsafe { core::mem::transmute::<[core::mem::MaybeUninit<ScorableHandPair>; 7], [ScorableHandPair; 7]>(pairs) };
					Some(ScorableHand::Chiitoi(ScorableHandChiitoi(pairs)))
				}
				else {
					None
				},

			_ => None,
		};

		Hand13ScorableHands { lookup, kokushi_musou, chiitoi }
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self) -> Hand13Tenpai {
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
		let kokushi_musou = ToKokushiMusou::new(ts.as_ref());
		let chiitoi = to_chiitoi(ts.as_ref());
		let ts = Tile37SuitedMultiSet::new(&ts);

		let mut tiles = ts.tenpai();
		match kokushi_musou {
			ToKokushiMusou::Invalid => (),
			ToKokushiMusou::Single { wait, .. } => {
				tiles.insert(wait);
			},
			ToKokushiMusou::Any => {
				tiles.insert(t!(1m));
				tiles.insert(t!(9m));
				tiles.insert(t!(1p));
				tiles.insert(t!(9p));
				tiles.insert(t!(1s));
				tiles.insert(t!(9s));
				tiles.insert(t!(E));
				tiles.insert(t!(S));
				tiles.insert(t!(W));
				tiles.insert(t!(N));
				tiles.insert(t!(Wh));
				tiles.insert(t!(G));
				tiles.insert(t!(R));
			},
		}
		if let Some(wait) = chiitoi {
			tiles.insert(wait);
			if let Some(wait) = wait.make_red() {
				tiles.insert(wait);
			}
		}
		let tiles = tiles.into_iter();

		Hand13Tenpai { tiles, kokushi_musou, chiitoi, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand13ScorableHands {
	lookup: LookupForNewTile<U3>,
	kokushi_musou: Option<ScorableHand>,
	chiitoi: Option<ScorableHand>,
}

assert_size_of!(Hand13ScorableHands, 176);

impl Iterator for Hand13ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou.take() {
			return Some(h);
		}

		if let Some(h) = self.chiitoi.take() {
			return Some(h);
		}

		let (ms, md, pair) = self.lookup.next()?;
		let [ma, mb, mc] = ms.into();
		Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let extra = usize::from(self.kokushi_musou.is_some()) + usize::from(self.chiitoi.is_some());
		let (lo, hi) = self.lookup.size_hint();
		(lo + extra, hi.map(|hi| hi + extra))
	}
}

impl core::iter::FusedIterator for Hand13ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand13Tenpai {
	tiles: Tile37SetIntoIter,
	kokushi_musou: ToKokushiMusou,
	chiitoi: Option<Tile>,
	ts: Tile37SuitedMultiSet<U13>,
}

assert_size_of!(Hand13Tenpai, 32);

impl Iterator for Hand13Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = self.tiles.next()?;

			if self.kokushi_musou.with_new_tile(new_tile).is_some() {
				return Some(new_tile);
			}

			if let Some(t) = self.chiitoi && t.eq_ignore_red(&new_tile) {
				return Some(new_tile);
			}

			if Lookup::<U4>::new(&self.ts.push(new_tile)).next().is_some() {
				return Some(new_tile);
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
		let Self(ts, ms) = self;
		let [] = ms.into();
		let lookup = Lookup::new(&Tile37SuitedMultiSet::new(&ts));

		ToKokushiMusou::tenhou(ts.as_ref()).into_iter()
			.chain(tenhou_to_chiitoi(ts.as_ref()))
			.chain(ts.into_iter().flat_map(move |new_tile| LookupForNewTile::new(lookup.clone(), new_tile, TsumoOrRon::Tsumo).map(|(ms, md, pair)| {
				let [ma, mb, mc] = ms.into();
				ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, md, pair))
			})))
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
	pub fn tenpai(self) -> HandTenpai {
		match self {
			Self::One(h) => {
				let wait = h.tenpai();
				HandTenpai::One(core::iter::once(wait).chain(wait.make_red()))
			},
			Self::Four(h) => HandTenpai::Four(h.tenpai()),
			Self::Seven(h) => HandTenpai::Seven(h.tenpai()),
			Self::Ten(h) => HandTenpai::Ten(h.tenpai()),
			Self::Thirteen(h) => HandTenpai::Thirteen(h.tenpai()),
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
				let (_, ts) = unsafe { self.hand.0.remove_unchecked(i) };
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

fn to_chiitoi(ts: &[Tile; 13]) -> Option<Tile> {
	let (is_valid, wait) = cfg_select! {
		all(target_arch = "riscv64", target_feature = "v") => {{
			let wait: isize;
			let num_pairs: u64;

			unsafe {
				core::arch::asm!(
					// let ts /* : v20:v20 */ = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 13, e8, m1, ta, ma",
					"vle8.v v20, ({ts})",

					// let offsets /* : v16:v16 */ = ts >> 1;
					"vsrl.vi v16, v20, 1",

					// let offsets /* : v8:v15 */ = core::simd::num::SimdUint::cast::<u64>(offsets);
					"vsetivli zero, 13, e64, m{e64x13_lmul}, ta, ma",
					"vzext.vf8 v8, v16",
					// let ones /* : v0:v7 */ = core::simd::Simd::splat(1);
					"vmv.v.i v0, 1",
					// let masks /* : v0:v7 */ = ones << offsets;
					"vsll.vv v0, v0, v8",

					// For each mask, we want to update a `u8x64` histogram. We can take advantage of scalable vectors
					// by processing multiple such histograms in parallel and then merge them all at the end.
					// We don't know how many such histograms we can handle, but since VLEN is always a power of two and
					// greater than 128b = 16B, we know that an m8 will always be able to hold multiples of 64B,
					// so we don't need to worry about the last histogram being split across two iterations.
					//
					// A full `u8x64x13` would have 64 * 13 = 832 elements.
					//
					// TODO(rustup): There is (currently?) no way to express this with `core::simd`.
					// The `core::simd` code in the comments below is partially pseudocode.

					// let num_u8s_that_can_be_processed = __riscv_vsetvl_e8m8(64 * 13);
					// let mut counts /* : v8:v15 */ = core::simd::Simd::<u8, { num_u8s_that_can_be_processed }>::splat(0);
					"li {remaining}, 832",
					"vsetvli {processed}, {remaining}, e8, m{e8x832_lmul}, ta, ma",
					"vmv.v.i v8, 0",

					// The first batch of histograms just maps each mask bit to `0_u8` or `1_u8`.

					// let mask /* : v0:v8 */ = masks.extract::<0, _>();
					// let counts_plus_one = core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask, counts_plus_one, counts);
					"vmerge.vim v8, v8, 1, v0",

					"sub {remaining}, {remaining}, {processed}",
					"beqz {remaining}, 2f",

					// The remaining histograms map each mask bit to `0_u8` or `1_u8` and are added to the first batch.
					"1:",
					// let masks /* : v0:v8 */ = masks.extract::<processed / 64, remaining / 64>();
					"srli {scratch}, {remaining}, 6",
					"vsetvli zero, {scratch}, e64, m{e64x13_lmul}, ta, ma",
					"srli {scratch}, {processed}, 6",
					"vslidedown.vx v0, v0, {scratch}",

					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask, counts_plus_one, counts);
					"vsetvli {processed}, {remaining}, e8, m{e8x832_lmul}, tu, mu",
					"vadd.vi v8, v8, 1, v0.t",

					"sub {remaining}, {remaining}, {processed}",
					"bnez {remaining}, 1b",

					// Now we have to merge the histograms. Depending on VLEN, we might have:
					// - u8x64x13 for 1024b <= VLEN
					// - u8x64x8 for 512b <= VLEN < 1024b
					// - u8x64x4 for 256b <= VLEN < 512b
					// - u8x64x2 for 128b <= VLEN < 256b
					// - u8x64 for 64b <= VLEN < 128b, though we require V which requires Zvl128b so this case won't happen.
					//
					// Each of the first four cases can do one halving addition and then delegate to the next case.
					// We know which case to start from using `vsetvli`.

					"2:",
					// let mut num_u8s_that_can_be_processed = __riscv_vsetvl_e8m8(64 * 13);
					"li {scratch}, 832",
					"vsetvli {remaining}, {scratch}, e8, m{e8x832_lmul}, ta, ma",

					// u8x64x13 -> u8x64x8
					//
					// if num_u8s_that_can_be_processed == 64 * 13 {
					//     counts = counts.extract::<0, 8 * 64>() + counts.extract::<8 * 64, 5 * 64>().resize(0);
					//     num_u8s_that_can_be_processed = 64 * 8;
					// }
					"bltu {remaining}, {scratch}, 3f",
					"li {remaining}, 512",
					"li {scratch}, 320",
					"vsetvli zero, {scratch}, e8, m{e8x832_lmul}, ta, ma",
					"vslidedown.vx v16, v8, {remaining}",
					"vsetvli zero, {scratch}, e8, m{e8x512_lmul}, tu, ma",
					"vadd.vv v8, v8, v16",

					// u8x64x8 -> u8x64x4
					//
					// if num_u8s_that_can_be_processed == 64 * 8 {
					//     counts = counts.extract::<0, 4 * 64>() + counts.extract::<4 * 64, 4 * 64>();
					//     num_u8s_that_can_be_processed = 64 * 4;
					// }
					"3:",
					"li {scratch}, 512",
					"bltu {remaining}, {scratch}, 4f",
					"li {remaining}, 256",
					"vsetvli zero, {remaining}, e8, m{e8x512_lmul}, ta, ma",
					"vslidedown.vx v16, v8, {remaining}",
					"vadd.vv v8, v8, v16",

					// u8x64x4 -> u8x64x2
					//
					// if num_u8s_that_can_be_processed == 64 * 4 {
					//     counts = counts.extract::<0, 2 * 64>() + counts.extract::<2 * 64, 2 * 64>();
					//     num_u8s_that_can_be_processed = 64 * 2;
					// }
					"4:",
					"li {scratch}, 256",
					"bltu {remaining}, {scratch}, 5f",
					"li {remaining}, 128",
					"vsetvli zero, {remaining}, e8, m{e8x256_lmul}, ta, ma",
					"vslidedown.vx v16, v8, {remaining}",
					"vadd.vv v8, v8, v16",

					// u8x64x2 -> u8x64
					//
					// counts = counts.extract::<0, 1 * 64>() + counts.extract::<1 * 64, 1 * 64>();
					"5:",
					"li {remaining}, 64",
					"vsetvli zero, {remaining}, e8, m{e8x128_lmul}, ta, ma",
					"vslidedown.vx v16, v8, {remaining}",
					"vadd.vv v8, v8, v16",

					// let single_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(1));
					"vmseq.vi v0, v8, 1",
					// let wait = single_is.first_set().unwrap();
					"vfirst.m {processed}, v0",

					// let pair_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));
					"vmseq.vi v0, v8, 2",
					// let num_pairs = pair_is.to_bitmask().count_ones();
					"vcpop.m {scratch}, v0",

					out("v0") _,
					out("v1") _,
					out("v2") _,
					out("v3") _,
					out("v4") _,
					out("v5") _,
					out("v6") _,
					out("v7") _,
					out("v8") _,
					out("v9") _,
					out("v10") _,
					out("v11") _,
					out("v12") _,
					out("v13") _,
					out("v14") _,
					out("v15") _,
					out("v16") _,
					out("v20") _,

					e8x128_lmul = const cfg_select! {
						target_feature = "zvl1024b" => 1,
						target_feature = "zvl512b" => 2,
						target_feature = "zvl256b" => 4,
						_ => 8,
					},
					e8x256_lmul = const cfg_select! {
						target_feature = "zvl2048b" => 1,
						target_feature = "zvl1024b" => 2,
						target_feature = "zvl512b" => 4,
						_ => 8,
					},
					e8x512_lmul = const cfg_select! {
						target_feature = "zvl4096b" => 1,
						target_feature = "zvl2048b" => 2,
						target_feature = "zvl1024b" => 4,
						_ => 8,
					},
					e8x832_lmul = const cfg_select! {
						target_feature = "zvl8192b" => 1,
						target_feature = "zvl4096b" => 2,
						target_feature = "zvl2048b" => 4,
						_ => 8,
					},
					e64x13_lmul = const cfg_select! {
						target_feature = "zvl1024b" => 1,
						target_feature = "zvl512b" => 2,
						target_feature = "zvl256b" => 4,
						_ => 8,
					},
					ts = in(reg) ts.as_ptr(),
					remaining = lateout(reg) _,
					processed = lateout(reg) wait,
					scratch = lateout(reg) num_pairs,
					options(nostack),
				);
			}

			(num_pairs == 6, wait)
		}},

		_ => {{
			let mut first = 0_u64;
			let mut second = 0_u64;
			let mut invalid = 0_u64;
			for &t in ts {
				let t = t as u8;
				let offset = t >> 1;
				let mask = 0b1 << offset;
				let first_mask = first & mask;
				let second_mask = second & mask;
				first |= mask;
				second |= first_mask;
				invalid |= second_mask;
			}

			let diff = first ^ second;
			let wait = diff.trailing_zeros();
			let remaining = diff & !(0b1_u64.wrapping_shl(wait));

			(invalid | remaining == 0, wait)
		}},
	};

	is_valid.then(|| {
		#[expect(clippy::cast_possible_truncation)]
		let wait = (wait as u8) << 1;
		// SAFETY: Since `is_valid` is true, `ts` is guaranteed to have contained six pairs and one unpaired tile,
		// and `wait` is guaranteed to be that tile.
		unsafe { core::mem::transmute::<u8, Tile>(wait) }
	})
}

fn to_chiitoi_with_pairs(ts: &[Tile; 13]) -> Option<([ScorableHandPair; 6], Tile)> {
	let (ps, wait) = cfg_select! {
		// TODO(rustup): The `core::simd` version has a couple of inefficiences compared to the manual impl:
		//
		// - It uses `vmerge.vim v0; vadd.vv` instead of `vadd.vi v0.t` for the `counts` vector.
		//   LLIR that does `add; select` does generate `vadd.vi v0.t` so it's not clear why the `core::simd` version doesn't.
		//
		// - Instead of using `vor.vv v0.t` for the `pair_representatives` vector, it generates extremely silly code
		//   that uses so many registers that it has to repeatedly spill the register file to the stack and load it back.
		//
		// - `core::simd` does not provide register-to-register compress API (or even compressed store API), needed to extract the pair representatives.
		//
		//   Ref: https://github.com/rust-lang/portable-simd/issues/240
		all(target_arch = "riscv64", target_feature = "v") => {{
			let wait: isize;
			let num_pairs: u64;
			let pair_representatives: u64;

			unsafe {
				core::arch::asm!(
					// let ts /* : v20:v20 */ = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 13, e8, m1, ta, ma",
					"vle8.v v20, ({ts})",

					// let offsets /* : v16:v16 */ = ts >> 1;
					"vsrl.vi v16, v20, 1",

					// let offsets /* : v8:v15 */ = core::simd::num::SimdUint::cast::<u64>(offsets);
					"vsetivli zero, 13, e64, m{e64x13_lmul}, ta, ma",
					"vzext.vf8 v8, v16",
					// let ones /* : v0:v7 */ = core::simd::Simd::splat(1);
					"vmv.v.i v0, 1",
					// let masks /* : v0:v7 */ = ones << offsets;
					"vsll.vv v0, v0, v8",

					// let mut counts /* : v8:v11 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, ma",
					"vmv.v.i v8, 0",
					// let mut pair_representatives /* : v12:v15 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vmv.v.i v12, 0",

					// For each iteration, do a masked add for the histogram and a masked OR for the pair representatives,
					// except the very first iteration can use a merge directly.
					//
					// At the end of each iteration, we want to slide the masks list down by 1. However sliding the whole list
					// would require using a large LMUL for each slide. We can optimize by using smaller slides
					// with tail-undisturbed policy.

					// Masks: 0 1 2 3 4 5 6 7 8 9 10 11 12

					// let mask0 = masks[0];
					// let counts_plus_one = core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask0, counts_plus_one, counts);
					"vmerge.vim v8, v8, 1, v0",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[0]);
					"vrgather.vi v16, v20, 0",
					// let pair_representatives_or_t = t;
					// pair_representatives = core::simd::Select::select(mask0, pair_representatives_or_t, pair_representatives);
					"vmerge.vvm v12, v12, v16, v0",

					// let mask1 = masks[1];
					"vsetivli zero, 1, e64, m1, tu, ma",
					// Masks: 1 ? 2 3 4 5 6 7 8 9 10 11 12
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask1, counts_plus_one, counts);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[1]);
					"vrgather.vi v16, v20, 1",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask1, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks23 = masks.extract::<2, 2>();
					// Masks: 2 3 2 3 4 5 6 7 8 9 10 11 12
					"vsetivli zero, 2, e64, m{e64x4_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 2",
					// let mask2 = masks23[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask2, counts_plus_one, counts);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[2]);
					"vrgather.vi v16, v20, 2",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask2, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask3 = masks23[1];
					"vsetivli zero, 1, e64, m1, tu, ma",
					// Masks: 3 ? 2 3 4 5 6 7 8 9 10 11 12
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask3, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[3]);
					"vrgather.vi v16, v20, 3",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask3, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks4567 = masks.extract::<4, 4>();
					// Masks: 4 5 6 7 4 5 6 7 8 9 10 11 12
					"vsetivli zero, 4, e64, m{e64x8_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 4",
					// let mask4 = masks4567[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask4, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[4]);
					"vrgather.vi v16, v20, 4",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask4, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask5 = masks4567[1];
					// Masks: 5 ? 6 7 4 5 6 7 8 9 10 11 12
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask5, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[5]);
					"vrgather.vi v16, v20, 5",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask5, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks67 = masks4567.extract::<2, 2>();
					// Masks: 6 7 ? ? 4 5 6 7 8 9 10 11 12
					"vsetivli zero, 2, e64, m{e64x4_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 2",
					// let mask6 = masks67[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask6, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[6]);
					"vrgather.vi v16, v20, 6",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask6, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask7 = masks67[1];
					// Masks: 7 ? ? ? 4 5 6 7 8 9 10 11 12
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask7, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[7]);
					"vrgather.vi v16, v20, 7",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask7, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks = masks.extract::<8, 5>();
					// Masks: 8 9 10 11 12 ? ? ? ? ? ? ? ?
					"vsetivli zero, 5, e64, m{e64x13_lmul}, ta, ma",
					"vslidedown.vi v0, v0, 8",
					// let mask8 = masks[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask8, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[8]);
					"vrgather.vi v16, v20, 8",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask8, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask9 = masks[1];
					// Masks: 9 ? 10 11 12 ? ? ? ? ? ? ? ?
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask9, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[9]);
					"vrgather.vi v16, v20, 9",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask9, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks1011 = masks.extract::<2, 2>();
					// Masks: 10 11 10 11 12 ? ? ? ? ? ? ? ?
					"vsetivli zero, 2, e64, m{e64x4_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 2",
					// let mask10 = masks1011[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask10, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[10]);
					"vrgather.vi v16, v20, 10",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask10, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask11 = masks1011[1];
					// Masks: 11 ? 10 11 12 ? ? ? ? ? ? ? ?
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask11, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[11]);
					"vrgather.vi v16, v20, 11",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask11, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks = masks.extract::<4, 1>();
					// Masks: 12 ? ? ? ? ? ? ? ? ? ? ? ?
					"vsetivli zero, 1, e64, m{e64x8_lmul}, ta, ma",
					"vslidedown.vi v0, v0, 4",
					// let mask12 = masks[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask12, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[12]);
					"vrgather.vi v16, v20, 12",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask12, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let single_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(1));
					"vmseq.vi v0, v8, 1",
					// let wait = single_is.first_set().unwrap();
					"vfirst.m {wait}, v0",

					// let pair_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));
					"vmseq.vi v0, v8, 2",
					// let num_pairs = pair_is.to_bitmask().count_ones();
					"vcpop.m {num_pairs}, v0",

					// let pair_representatives /* : v20:v23 */ = __riscv_vcompress_vm_u8m4(pair_representatives, pair_is, 34);
					"vcompress.vm v8, v12, v0",
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vmv.x.s {pair_representatives}, v8",

					out("v0") _,
					out("v1") _,
					out("v2") _,
					out("v3") _,
					out("v4") _,
					out("v5") _,
					out("v6") _,
					out("v7") _,
					out("v8") _,
					out("v9") _,
					out("v10") _,
					out("v11") _,
					out("v12") _,
					out("v13") _,
					out("v14") _,
					out("v15") _,
					out("v16") _,
					out("v17") _,
					out("v18") _,
					out("v19") _,
					out("v20") _,

					thirty_four = in(reg) 34_usize,
					e8x34_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					e64x4_lmul = const cfg_select! {
						target_feature = "zvl256b" => 1,
						_ => 2,
					},
					e64x8_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					e64x13_lmul = const cfg_select! {
						target_feature = "zvl1024b" => 1,
						target_feature = "zvl512b" => 2,
						target_feature = "zvl256b" => 4,
						_ => 8,
					},
					ts = in(reg) ts.as_ptr(),
					wait = lateout(reg) wait,
					num_pairs = lateout(reg) num_pairs,
					pair_representatives = lateout(reg) pair_representatives,
					options(nostack),
				);
			}

			if num_pairs != 6 {
				return None;
			}

			let ps = pair_representatives.to_le_bytes();
			let ps = [ps[0], ps[1], ps[2], ps[3], ps[4], ps[5]];
			// SAFETY: The pairs are guaranteed to be valid tiles themselves since they were formed by ORing tiles
			// that were equal to each other (after ignoring the "red" bit).
			let ps = unsafe { core::mem::transmute::<[u8; 6], [Tile; 6]>(ps) };
			let ps = ps.map(ScorableHandPair);

			(ps, wait)
		}},

		_ => {{
			let mut first = 0_u64;
			let mut second = 0_u64;
			let mut invalid = 0_u64;
			let mut pair_representatives = [0_u8; 34];

			for &t in ts {
				let t = t as u8;
				let offset = t >> 1;
				pair_representatives[usize::from(offset)] |= t;
				let mask = 0b1 << offset;
				let first_mask = first & mask;
				let second_mask = second & mask;
				first |= mask;
				second |= first_mask;
				invalid |= second_mask;
			}

			let diff = first ^ second;
			let wait = diff.trailing_zeros();
			let remaining = diff & !(0b1_u64.wrapping_shl(wait));

			if invalid | remaining != 0 {
				return None;
			}

			let mut ps = [const { core::mem::MaybeUninit::uninit() }; 6];
			chiitoi_extract_pair_representatives(&mut ps, &pair_representatives, second);
			// TODO(rustup): Use `MaybeUninit::array_assume_init` when that is stabilized.
			let ps = unsafe { core::mem::transmute::<[core::mem::MaybeUninit<ScorableHandPair>; 6], [ScorableHandPair; 6]>(ps) };

			(ps, wait)
		}},
	};

	#[expect(clippy::cast_possible_truncation)]
	let wait = (wait as u8) << 1;
	// SAFETY: At this point after the above comparisons, `ts` is guaranteed to have contained six pairs and one unpaired tile,
	// and `wait` is guaranteed to be that tile.
	let wait = unsafe { core::mem::transmute::<u8, Tile>(wait) };

	Some((ps, wait))
}

fn tenhou_to_chiitoi(ts: &[Tile; 14]) -> Option<ScorableHand> {
	let ps = cfg_select! {
		// TODO(rustup): The `core::simd` version has a couple of inefficiences compared to the manual impl:
		//
		// - It uses `vmerge.vim v0; vadd.vv` instead of `vadd.vi v0.t` for the `counts` vector.
		//   LLIR that does `add; select` does generate `vadd.vi v0.t` so it's not clear why the `core::simd` version doesn't.
		//
		// - Instead of using `vor.vv v0.t` for the `pair_representatives` vector, it generates extremely silly code
		//   that uses so many registers that it has to repeatedly spill the register file to the stack and load it back.
		//
		// - `core::simd` does not provide register-to-register compress API (or even compressed store API), needed to extract the pair representatives.
		//
		//   Ref: https://github.com/rust-lang/portable-simd/issues/240
		all(target_arch = "riscv64", target_feature = "v") => {{
			let num_pairs: u64;
			let pair_representatives: u64;

			unsafe {
				core::arch::asm!(
					// let ts /* : v20:v20 */ = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 14, e8, m1, ta, ma",
					"vle8.v v20, ({ts})",

					// let offsets /* : v16:v16 */ = ts >> 1;
					"vsrl.vi v16, v20, 1",

					// let offsets /* : v8:v15 */ = core::simd::num::SimdUint::cast::<u64>(offsets);
					"vsetivli zero, 14, e64, m{e64x14_lmul}, ta, ma",
					"vzext.vf8 v8, v16",
					// let ones /* : v0:v7 */ = core::simd::Simd::splat(1);
					"vmv.v.i v0, 1",
					// let masks /* : v0:v7 */ = ones << offsets;
					"vsll.vv v0, v0, v8",

					// let mut counts /* : v8:v11 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, ma",
					"vmv.v.i v8, 0",
					// let mut pair_representatives /* : v12:v15 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vmv.v.i v12, 0",

					// For each iteration, do a masked add for the histogram and a masked OR for the pair representatives,
					// except the very first iteration can use a merge directly.
					//
					// At the end of each iteration, we want to slide the masks list down by 1. However sliding the whole list
					// would require using a large LMUL for each slide. We can optimize by using smaller slides
					// with tail-undisturbed policy.

					// Masks: 0 1 2 3 4 5 6 7 8 9 10 11 12 13

					// let mask0 = masks[0];
					// let counts_plus_one = core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask0, counts_plus_one, counts);
					"vmerge.vim v8, v8, 1, v0",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[0]);
					"vrgather.vi v16, v20, 0",
					// let pair_representatives_or_t = t;
					// pair_representatives = core::simd::Select::select(mask0, pair_representatives_or_t, pair_representatives);
					"vmerge.vvm v12, v12, v16, v0",

					// let mask1 = masks[1];
					"vsetivli zero, 1, e64, m1, tu, ma",
					// Masks: 1 ? 2 3 4 5 6 7 8 9 10 11 12 13
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask1, counts_plus_one, counts);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[1]);
					"vrgather.vi v16, v20, 1",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask1, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks23 = masks.extract::<2, 2>();
					// Masks: 2 3 2 3 4 5 6 7 8 9 10 11 12 13
					"vsetivli zero, 2, e64, m{e64x4_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 2",
					// let mask2 = masks23[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					// counts = core::simd::Select::select(mask2, counts_plus_one, counts);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[2]);
					"vrgather.vi v16, v20, 2",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask2, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask3 = masks23[1];
					"vsetivli zero, 1, e64, m1, tu, ma",
					// Masks: 3 ? 2 3 4 5 6 7 8 9 10 11 12 13
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask3, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[3]);
					"vrgather.vi v16, v20, 3",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask3, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks4567 = masks.extract::<4, 4>();
					// Masks: 4 5 6 7 4 5 6 7 8 9 10 11 12 13
					"vsetivli zero, 4, e64, m{e64x8_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 4",
					// let mask4 = masks4567[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask4, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[4]);
					"vrgather.vi v16, v20, 4",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask4, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask5 = masks4567[1];
					// Masks: 5 ? 6 7 4 5 6 7 8 9 10 11 12 13
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask5, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[5]);
					"vrgather.vi v16, v20, 5",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask5, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks67 = masks4567.extract::<2, 2>();
					// Masks: 6 7 ? ? 4 5 6 7 8 9 10 11 12 13
					"vsetivli zero, 2, e64, m{e64x4_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 2",
					// let mask6 = masks67[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask6, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[6]);
					"vrgather.vi v16, v20, 6",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask6, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask7 = masks67[1];
					// Masks: 7 ? ? ? 4 5 6 7 8 9 10 11 12 13
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask7, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[7]);
					"vrgather.vi v16, v20, 7",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask7, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks = masks.extract::<8, 6>();
					// Masks: 8 9 10 11 12 13 ? ? ? ? ? ? ?
					"vsetivli zero, 6, e64, m{e64x14_lmul}, ta, ma",
					"vslidedown.vi v0, v0, 8",
					// let mask8 = masks[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask8, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[8]);
					"vrgather.vi v16, v20, 8",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask8, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask9 = masks[1];
					// Masks: 9 ? 10 11 12 13 ? ? ? ? ? ? ?
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask9, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[9]);
					"vrgather.vi v16, v20, 9",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask9, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks1011 = masks.extract::<2, 2>();
					// Masks: 10 11 10 11 12 13 ? ? ? ? ? ? ?
					"vsetivli zero, 2, e64, m{e64x4_lmul}, tu, ma",
					"vslidedown.vi v0, v0, 2",
					// let mask10 = masks1011[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask10, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[10]);
					"vrgather.vi v16, v20, 10",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask10, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask11 = masks1011[1];
					// Masks: 11 ? 10 11 12 13 ? ? ? ? ? ? ?
					"vsetivli zero, 1, e64, m1, tu, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask11, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[11]);
					"vrgather.vi v16, v20, 11",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask11, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let masks = masks.extract::<4, 1>();
					// Masks: 12 13 ? ? ? ? ? ? ? ? ? ? ?
					"vsetivli zero, 2, e64, m{e64x8_lmul}, ta, ma",
					"vslidedown.vi v0, v0, 4",
					// let mask12 = masks[0];
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask12, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[12]);
					"vrgather.vi v16, v20, 12",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask12, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let mask13 = masks[1];
					// Masks: 13 ? ? ? ? ? ? ? ? ? ? ? ?
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vslidedown.vi v0, v0, 1",
					// let counts_plus_one = counts + core::simd::Simd::splat(1);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					// counts = core::simd::Select::select(mask13, counts_plus_one, counts);
					"vadd.vi v8, v8, 1, v0.t",
					// let t /* : v16:v19 */ = core::simd::Simd::<u8, 34>::splat(ts[13]);
					"vrgather.vi v16, v20, 13",
					// let pair_representatives_or_t = pair_representatives | t;
					// pair_representatives = core::simd::Select::select(mask13, pair_representatives_or_t, pair_representatives);
					"vor.vv v12, v12, v16, v0.t",

					// let pair_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));
					"vmseq.vi v0, v8, 2",
					// let num_pairs = pair_is.to_bitmask().count_ones();
					"vcpop.m {num_pairs}, v0",

					// let pair_representatives /* : v20:v23 */ = __riscv_vcompress_vm_u8m4(pair_representatives, pair_is, 34);
					"vcompress.vm v8, v12, v0",
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vmv.x.s {pair_representatives}, v8",

					out("v0") _,
					out("v1") _,
					out("v2") _,
					out("v3") _,
					out("v4") _,
					out("v5") _,
					out("v6") _,
					out("v7") _,
					out("v8") _,
					out("v9") _,
					out("v10") _,
					out("v11") _,
					out("v12") _,
					out("v13") _,
					out("v14") _,
					out("v15") _,
					out("v16") _,
					out("v17") _,
					out("v18") _,
					out("v19") _,
					out("v20") _,

					thirty_four = in(reg) 34_usize,
					e8x34_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					e64x4_lmul = const cfg_select! {
						target_feature = "zvl256b" => 1,
						_ => 2,
					},
					e64x8_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					e64x14_lmul = const cfg_select! {
						target_feature = "zvl1024b" => 1,
						target_feature = "zvl512b" => 2,
						target_feature = "zvl256b" => 4,
						_ => 8,
					},
					ts = in(reg) ts.as_ptr(),
					num_pairs = lateout(reg) num_pairs,
					pair_representatives = lateout(reg) pair_representatives,
					options(nostack),
				);
			}

			if num_pairs != 7 {
				return None;
			}

			let ps = pair_representatives.to_le_bytes();
			let ps = [ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6]];
			// SAFETY: The pairs are guaranteed to be valid tiles themselves since they were formed by ORing tiles
			// that were equal to each other (after ignoring the "red" bit).
			let ps = unsafe { core::mem::transmute::<[u8; 7], [Tile; 7]>(ps) };
			ps.map(ScorableHandPair)
		}},

		_ => {{
			let mut first = 0_u64;
			let mut second = 0_u64;
			let mut invalid = 0_u64;
			let mut pair_representatives = [0_u8; 34];

			for &t in ts {
				let t = t as u8;
				let offset = t >> 1;
				pair_representatives[usize::from(offset)] |= t;
				let mask = 0b1 << offset;
				let first_mask = first & mask;
				let second_mask = second & mask;
				first |= mask;
				second |= first_mask;
				invalid |= second_mask;
			}

			if invalid | (first ^ second) != 0 {
				return None;
			}

			let mut ps = [const { core::mem::MaybeUninit::uninit() }; 7];
			chiitoi_extract_pair_representatives(&mut ps, &pair_representatives, second);
			// TODO(rustup): Use `MaybeUninit::array_assume_init` when that is stabilized.
			unsafe { core::mem::transmute::<[core::mem::MaybeUninit<ScorableHandPair>; 7], [ScorableHandPair; 7]>(ps) }
		}},
	};
	Some(ScorableHand::Chiitoi(ScorableHandChiitoi(ps)))
}

#[cfg(not(all(target_arch = "riscv64", target_feature = "v")))]
fn chiitoi_extract_pair_representatives(
	result: &mut [core::mem::MaybeUninit<ScorableHandPair>],
	pair_representatives: &[u8; 34],
	pair_is: u64,
) {
	cfg_select! {
		all(target_arch = "x86_64", target_feature = "avx512vbmi2") => {{
			let pair_representatives = unsafe { core::arch::x86_64::_mm512_maskz_loadu_epi8((1 << pair_representatives.len()) - 1, <*const _>::cast::<i8>(pair_representatives.as_ptr())) };
			let ps = unsafe { core::arch::x86_64::_mm512_maskz_compress_epi8(pair_is, pair_representatives.into()) };
			let ps = unsafe { core::mem::transmute_copy::<core::arch::x86_64::__m512i, u64>(&ps) };
			let ps = ps.to_le_bytes();
			// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
			let result = unsafe { core::slice::from_raw_parts_mut(<*mut core::mem::MaybeUninit<ScorableHandPair>>::cast::<core::mem::MaybeUninit<u8>>(result.as_mut_ptr()), result.len()) };
			result.write_copy_of_slice(&ps[..result.len()]);
		}},

		_ => {{
			let mut pair_is = pair_is;
			let mut result_i = 0;
			for p in result {
				let Some(i) = pair_is.lowest_one() else { break; };
				pair_is >>= i + 1;

				result_i += i as usize;
				// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
				unsafe { core::hint::assert_unchecked(result_i < pair_representatives.len()); }
				let pair_representative = pair_representatives[result_i];
				let pair_representative = unsafe { core::mem::transmute::<u8, Tile>(pair_representative) };
				p.write(ScorableHandPair(pair_representative));
				result_i += 1;
			}
		}},
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

	use crate::Tile37Set;

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
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 4p, 7p });
		}

		{
			let h = make_hand!(4m 5m 6p 7p 8p 1s 2s 3s 4s 5s 6s 8s 8s);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 3m, 6m });
		}

		{
			let h = make_hand!(1m 1m 4p 4p { minkou N N N } { minkou 3p 3p 3p } { minkou R R R });
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 1m, 4p });
		}

		{
			let h = make_hand!(1m 1m 4m 5m 6m 3p 4p 4p 0p 6p 1s 2s 3s);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 2p, 5p });
		}

		{
			let h = make_hand!(4m 4m 1p 2p 3p 0p 5p 1s 2s 3s { minjun 1m 2m 3m });
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 4m, 5p });
		}

		{
			let h = make_hand!(3p 3p 4p 4p 0p 5p 7p 8p 8p 8p 9p G G);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 8p, G });
		}

		{
			let h = make_hand!(4m 0m 6m 7m 7m 4s 0s 6s 7s 8s { minjun 4p 5p 6p });
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 3s, 6s, 9s });
		}

		{
			let h = make_hand!(1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m });
		}

		{
			let h = make_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R });
		}

		{
			let h = make_hand!(1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { S, });
		}

		// Red five
		{
			let h = make_hand!(1m 1m 2m 2m 2m 3m 3m 3m 4p 5p 5p 5p 6p);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 1m, 4m, 0p });
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand. Not considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 1m 1m 1m 3m 4m 5m 3p 4p 5p 3s 4s 5s);
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! {});
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand, but only 1x 1m in unmelded tiles. Considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 3m 4m 5m 3p 4p 5p 3s 4s 5s { minkou 1m 1m 1m });
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 1m, });
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
			assert_eq!(h.tenpai().collect::<Tile37Set>(), t37set! { 8p, });
		}
	}
}
