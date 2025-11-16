use generic_array::{
	ArrayLength,
	GenericArray,
	functional::FunctionalSequence as _,
	sequence::{Concat as _, Remove},
	typenum,
};

use crate::{
	ArrayVec, ArrayVecIntoCombinations,
	GameType,
	HandMeldType,
	NumberTile,
	ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair,
	Tile, Tile34MultiSet, Tile34MultiSetElement, TileMultiSetIntoIter, TsumoOrRon,
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
/// If any of these expectations are violated, the program will still be safe, but `to_scorable_hands()`
/// will produce an unspecified and meaningless result. Therefore it is recommended to always satisfy these expectations.
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
/// If any of these expectations are violated, the program will still be safe, but `to_scorable_hands()`
/// will produce an unspecified and meaningless result. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum HandMeld {
	/// Closed quad formed by kan.
	Ankan([Tile; 4]),
	/// Open quad formed by kan.
	Minkan([Tile; 4]),
	/// Open triplet formed by pon.
	Minkou([Tile; 3]),
	/// Open sequence formed by chii.
	Minjun([NumberTile; 3]),
}

/// A hand containing some number of tiles and melds when it's not the player's turn.
///
/// This enum is a way to hold all possible stable hand types during a game.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HandStable {
	/// A hand containing 1 tile and 4 melds.
	One(Hand<typenum::U1, typenum::U4>),

	/// A hand containing 4 tiles and 3 melds.
	Four(Hand<typenum::U4, typenum::U3>),

	/// A hand containing 7 tiles and 2 melds.
	Seven(Hand<typenum::U7, typenum::U2>),

	/// A hand containing 10 tiles and 1 meld.
	Ten(Hand<typenum::U10, typenum::U1>),

	/// A hand containing 13 tiles.
	Thirteen(Hand<typenum::U13, typenum::U0>),
}

/// A hand containing some number of tiles and melds when it's the player's turn.
/// This has an extra tile that must be discarded using [`discard`][HandTentative::discard]
/// to return to a [`HandStable`].
///
/// This enum is a way to hold all possible tentative hand types during a game.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HandTentative {
	/// A hand containing 2 tiles and 4 melds.
	Two(Hand<typenum::U2, typenum::U4>),

	/// A hand containing 5 tiles and 3 melds.
	Five(Hand<typenum::U5, typenum::U3>),

	/// A hand containing 8 tiles and 2 melds.
	Eight(Hand<typenum::U8, typenum::U2>),

	/// A hand containing 11 tiles and 1 meld.
	Eleven(Hand<typenum::U11, typenum::U1>),

	/// A hand containing 14 tiles.
	Fourteen(Hand<typenum::U14, typenum::U0>),
}

assert_size_of!(Hand<typenum::U1, typenum::U4>, 21);
assert_size_of!(Hand<typenum::U2, typenum::U4>, 22);
assert_size_of!(Hand<typenum::U4, typenum::U3>, 19);
assert_size_of!(Hand<typenum::U5, typenum::U3>, 20);
assert_size_of!(Hand<typenum::U7, typenum::U2>, 17);
assert_size_of!(Hand<typenum::U8, typenum::U2>, 18);
assert_size_of!(Hand<typenum::U10, typenum::U1>, 15);
assert_size_of!(Hand<typenum::U11, typenum::U1>, 16);
assert_size_of!(Hand<typenum::U13, typenum::U0>, 13);
assert_size_of!(Hand<typenum::U14, typenum::U0>, 14);
assert_size_of!(HandMeld, 5);

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Add<typenum::U1> + core::ops::Sub<typenum::U3>,
	<NT as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	<NT as core::ops::Sub<typenum::U3>>::Output: ArrayLength,
	NM: ArrayLength + core::ops::Add<typenum::U1>,
	<NM as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, <NT as core::ops::Add<typenum::U1>>::Output>: Copy,
	HandStable: From<Self>,
{
	/// Find all possible ankans (quad via kan call on a quad held in the hand).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_ankans(self, new_tile: Tile) -> Ankans<<NT as core::ops::Add<typenum::U1>>::Output, NM> {
		let Self(ts, ms) = self;
		let ts = ts.concat([new_tile].into());
		Ankans::new(Hand(ts, ms))
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<typenum::U3>,
	<NT as core::ops::Sub<typenum::U3>>::Output: ArrayLength,
	NM: ArrayLength + core::ops::Add<typenum::U1>,
	<NM as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	HandStable: From<Self>,
{
	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NT + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<<NT as core::ops::Sub<typenum::U3>>::Output, <NM as core::ops::Add<typenum::U1>>::Output>> {
		let Self(ts, ms) = self;
		find_daiminkan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, ms.concat([HandMeld::Minkan(m_new)].into())))
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Add<typenum::U1>,
	<NT as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, <NT as core::ops::Add<typenum::U1>>::Output>: Copy,
	HandStable: From<Self>,
{
	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_shouminkans(self, new_tile: Tile) -> Shouminkans<<NT as core::ops::Add<typenum::U1>>::Output, NM> {
		let Self(ts, ms) = self;
		let ts = ts.concat([new_tile].into());
		Shouminkans::new(Hand(ts, ms))
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

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> impl Iterator<Item = Tile> {
		HandStable::from(self).tenpai(game_type)
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<typenum::U1>,
	<NT as core::ops::Sub<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Remove<Tile, NT, Output = GenericArray<Tile, <NT as core::ops::Sub<typenum::U1>>::Output>>,
	NM: ArrayLength,
	HandTentative: From<Hand<NT, NM>>,
{
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile, and the discarded tile.
	pub fn discard(self, i: usize) -> (Hand<<NT as core::ops::Sub<typenum::U1>>::Output, NM>, Tile) {
		let Self(ts, ms) = self;
		let (t_discard, ts) = ts.remove(i);
		(Hand(ts, ms), t_discard)
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

impl Hand<typenum::U1, typenum::U4> {
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

		if t1 == new_tile {
			let mut ms: [ScorableHandMeld; _] = ms.map(Into::into).into();
			ms.sort_unstable();
			let [m1, m2, m3, m4] = ms;
			Some(ScorableHand::Regular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair: ScorableHandPair([t1, new_tile]) })
		}
		else {
			None
		}
	}
}

impl Hand<typenum::U4, typenum::U3> {
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
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akdora
	/// does not make any difference to the final score. For example a hand `233344450p567m88s` can form both `234p 345p 340p 567m 88s` and `234p 345p 340p 567m 88s`,
	/// but only one is guaranteed to be yielded. Scorable hands that differ in the wait *are* considered distinct, so in the case where the new tile was 3p,
	/// the possible scorable hands are:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p ryanmen_left } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p ryanmen_left } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p kanchan } { anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> impl Iterator<Item = ScorableHand> {
		let Self(ts, ms) = self;
		let mut ts = ts.map(|t| (t, None)).concat([(new_tile, Some(tsumo_or_ron))].into());
		ts.sort_unstable_by_key(|(t, _)| *t);
		let mut ms = ms.map(Into::into);
		ms.sort_unstable();

		ArrayAdjacentPairs::new(ts)
			.filter_map(move |([(pt1, _), (pt2, _)], rest)| {
				if pt1 != pt2 { return None; }
				let pair = ScorableHandPair([pt1, pt2]);
				let md = to_meld(rest.into())?;
				match md {
					ScorableHandFourthMeld::Tanki(md) => {
						let [m1, m2, m3, m4] = merge_sorted(&ms, &[md].into()).into();
						Some(ScorableHand::Regular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair })
					},
					m4 => Some(ScorableHand::Regular { melds: (ms.into(), m4), pair }),
				}
			})
	}
}

impl Hand<typenum::U7, typenum::U2> {
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
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akdora
	/// does not make any difference to the final score. For example a hand `233344450p567m88s` can form both `234p 345p 340p 567m 88s` and `234p 345p 340p 567m 88s`,
	/// but only one is guaranteed to be yielded. Scorable hands that differ in the wait *are* considered distinct, so in the case where the new tile was 3p,
	/// the possible scorable hands are:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p ryanmen_left } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p ryanmen_left } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p kanchan } { anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> impl Iterator<Item = ScorableHand> {
		let Self(ts, ms) = self;
		let mut ts = ts.map(|t| (t, None)).concat([(new_tile, Some(tsumo_or_ron))].into());
		ts.sort_unstable_by_key(|(t, _)| *t);
		let mut ms = ms.map(Into::into);
		ms.sort_unstable();

		ArrayAdjacentPairs::new(ts)
			.filter(|([(pt1, _), (pt2, _)], _)| pt1 == pt2)
			.flat_map(move |([(pt1, _), (pt2, _)], rest)| {
				let pair = ScorableHandPair([pt1, pt2]);
				to_melds_2(rest.into()).map(move |(mc, md)| match md {
					ScorableHandFourthMeld::Tanki(md) => {
						let [m1, m2, m3, m4] = merge_sorted(&ms, &[mc, md].into()).into();
						ScorableHand::Regular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair }
					},
					m4 => {
						let [m1, m2, m3] = merge_sorted(&ms, &[mc].into()).into();
						ScorableHand::Regular { melds: ([m1, m2, m3], m4), pair }
					},
				})
			})
	}
}

impl Hand<typenum::U10, typenum::U1> {
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
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akdora
	/// does not make any difference to the final score. For example a hand `233344450p567m88s` can form both `234p 345p 340p 567m 88s` and `234p 345p 340p 567m 88s`,
	/// but only one is guaranteed to be yielded. Scorable hands that differ in the wait *are* considered distinct, so in the case where the new tile was 3p,
	/// the possible scorable hands are:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p ryanmen_left } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p ryanmen_left } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p kanchan } { anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> impl Iterator<Item = ScorableHand> {
		let Self(ts, ms) = self;
		let mut ts = ts.map(|t| (t, None)).concat([(new_tile, Some(tsumo_or_ron))].into());
		ts.sort_unstable_by_key(|(t, _)| *t);
		let ms = ms.map(Into::into);

		ArrayAdjacentPairs::new(ts)
			.filter(|([(pt1, _), (pt2, _)], _)| pt1 == pt2)
			.flat_map(move |([(pt1, _), (pt2, _)], rest)| {
				let pair = ScorableHandPair([pt1, pt2]);
				to_melds_3(rest.into()).map(move |([mb, mc], md)| match md {
					ScorableHandFourthMeld::Tanki(md) => {
						let [m1, m2, m3, m4] = merge_sorted(&ms, &[mb, mc, md].into()).into();
						ScorableHand::Regular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair }
					},
					m4 => {
						let [m1, m2, m3] = merge_sorted(&ms, &[mb, mc].into()).into();
						ScorableHand::Regular { melds: ([m1, m2, m3], m4), pair }
					},
				})
			})
	}
}

impl Hand<typenum::U13, typenum::U0> {
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
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akdora
	/// does not make any difference to the final score. For example a hand `233344450p567m88s` can form both `234p 345p 340p 567m 88s` and `234p 345p 340p 567m 88s`,
	/// but only one is guaranteed to be yielded. Scorable hands that differ in the wait *are* considered distinct, so in the case where the new tile was 3p,
	/// the possible scorable hands are:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p ryanmen_left } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p ryanmen_left } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p kanchan } { anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> impl Iterator<Item = ScorableHand> {
		let Self(ts, ms) = self;
		let mut ts = ts.map(|t| (t, None)).concat([(new_tile, Some(tsumo_or_ron))].into());
		ts.sort_unstable_by_key(|(t, _)| *t);
		let [] = ms.into();

		ArrayAdjacentPairs::new(ts)
			.filter(|([(pt1, _), (pt2, _)], _)| pt1 == pt2)
			.flat_map(move |([(pt1, _), (pt2, _)], rest)| {
				let pair = ScorableHandPair([pt1, pt2]);
				to_melds_4(rest.into()).map(move |([m1, m2, m3], m4)| ScorableHand::Regular { melds: ([m1, m2, m3], m4), pair })
			})
			.chain(to_chiitoi(ts.into()))
			.chain(to_kokushi_musou(ts.map(|(t, _)| t).into(), new_tile))
	}
}

impl Hand<typenum::U14, typenum::U0> {
	/// Find all possible ankans (quad via kan call on a quad held in the hand).
	///
	/// This is used for the special case where the dealer's starting hand can call an ankan. All other cases are handled by
	/// a stable hand type (like `Hand<13, 0>`) calling `find_ankans` at the time of drawing a new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_ankans(self) -> Ankans<typenum::U14, typenum::U0> {
		Ankans::new(self)
	}

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
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akdora
	/// does not make any difference to the final score. For example a hand `233344450p567m88s` can form both `234p 345p 340p 567m 88s` and `234p 345p 340p 567m 88s`,
	/// but only one is guaranteed to be yielded. Scorable hands that differ in the wait *are* considered distinct, so in the case where the new tile was 3p,
	/// the possible scorable hands are:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p ryanmen_left } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p ryanmen_left } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p kanchan } { anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self) -> impl Iterator<Item = ScorableHand> {
		let Self(ts, ms) = self;

		ts.into_iter().enumerate()
			.flat_map(move |(i, new_tile)| {
				let (_, ts) = ts.remove(i);
				Hand(ts, ms).to_scorable_hands(new_tile, TsumoOrRon::Tsumo)
			})
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
			Self::Ankan([t1, t2, t3, t4]) =>
				write!(f, "{{ ankan {t1} {t2} {t3} {t4} }}"),
			Self::Minkan([t1, t2, t3, t4]) =>
				write!(f, "{{ minkan {t1} {t2} {t3} {t4} }}"),
			Self::Minkou([t1, t2, t3]) =>
				write!(f, "{{ minkou {t1} {t2} {t3} }}"),
			Self::Minjun([t1, t2, t3]) =>
				write!(f, "{{ minjun {t1} {t2} {t3} }}"),
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
		let (ts, ty) = Tile::parse_run(s)?;
		let ty = ty.ok_or(())?;
		Ok(match ts[..] {
			[t1, t2, t3, t4] if is_kan([t1, t2, t3, t4]) => match ty {
				HandMeldType::Ankan => Self::Ankan([t1, t2, t3, t4]),
				HandMeldType::Shouminkan |
				HandMeldType::MinjunMinkouDaiminkan => Self::Minkan([t1, t2, t3, t4]),
			},

			[t1, t2, t3] if matches!(ty, HandMeldType::MinjunMinkouDaiminkan) =>
				if is_kou([t1, t2, t3]) {
					Self::Minkou([t1, t2, t3])
				}
				else {
					let t1 = NumberTile::try_from(t1)?;
					let t2 = NumberTile::try_from(t2)?;
					let t3 = NumberTile::try_from(t3)?;
					let mut ts = [t1, t2, t3];
					ts.sort_unstable();
					let [t1, t2, t3] = ts;
					if is_shun([t1, t2, t3]) {
						Self::Minjun([t1, t2, t3])
					}
					else {
						return Err(());
					}
				},

			_ => return Err(()),
		})
	}
}

impl HandStable {
	/// Find a possible ankan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_ankans(self, new_tile: Tile) -> HandAnkans {
		match self {
			Self::One(_) => HandAnkans::One,
			Self::Four(h) => HandAnkans::Four(h.find_ankans(new_tile)),
			Self::Seven(h) => HandAnkans::Seven(h.find_ankans(new_tile)),
			Self::Ten(h) => HandAnkans::Ten(h.find_ankans(new_tile)),
			Self::Thirteen(h) => HandAnkans::Thirteen(h.find_ankans(new_tile)),
		}
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Self> {
		Some(match self {
			Self::One(_) => return None,
			Self::Four(h) => Self::One(h.find_daiminkan(new_tile)?),
			Self::Seven(h) => Self::Four(h.find_daiminkan(new_tile)?),
			Self::Ten(h) => Self::Seven(h.find_daiminkan(new_tile)?),
			Self::Thirteen(h) => Self::Ten(h.find_daiminkan(new_tile)?),
		})
	}

	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_shouminkans(self, new_tile: Tile) -> HandShouminkans {
		match self {
			Self::One(h) => HandShouminkans::One(h.find_shouminkans(new_tile)),
			Self::Four(h) => HandShouminkans::Four(h.find_shouminkans(new_tile)),
			Self::Seven(h) => HandShouminkans::Seven(h.find_shouminkans(new_tile)),
			Self::Ten(h) => HandShouminkans::Ten(h.find_shouminkans(new_tile)),
			Self::Thirteen(_) => HandShouminkans::Thirteen,
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
	/// The iterator is guaranteed to yield all possible scorable hands, except those that differ only in the position of akadora, since the position of akdora
	/// does not make any difference to the final score. For example a hand `233344450p567m88s` can form both `234p 345p 340p 567m 88s` and `234p 345p 340p 567m 88s`,
	/// but only one is guaranteed to be yielded. Scorable hands that differ in the wait *are* considered distinct, so in the case where the new tile was 3p,
	/// the possible scorable hands are:
	///
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 5p ryanmen_left } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p } { anjun 3p 4p 0p ryanmen_left } { anjun 3p 4p 5p } { anjun 5m 6m 7m } { 8s 8s }`
	/// - `{ anjun 2p 3p 4p kanchan } { anjun 3p 4p 5p } { anjun 3p 4p 0p } { anjun 5m 6m 7m } { 8s 8s }`
	///
	/// One of the first two is guaranteed to be yielded, and the third is guaranteed to be yielded.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> alloc::boxed::Box<dyn Iterator<Item = ScorableHand>> {
		match self {
			Self::One(h) => alloc::boxed::Box::new(h.to_scorable_hand(new_tile).into_iter()),
			Self::Four(h) => alloc::boxed::Box::new(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Seven(h) => alloc::boxed::Box::new(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Ten(h) => alloc::boxed::Box::new(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Thirteen(h) => alloc::boxed::Box::new(h.to_scorable_hands(new_tile, tsumo_or_ron)),
		}
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> impl Iterator<Item = Tile> {
		// Note that tiles contained in `self` are *not* ignored, even if `self` contains all extant copies of the tile.
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447

		Tile::each(game_type).iter().copied().filter(move |&new_tile| match self {
			Self::One(h) => h.to_scorable_hand(new_tile).is_some(),
			Self::Four(h) => h.to_scorable_hands(new_tile, TsumoOrRon::Tsumo).next().is_some(),
			Self::Seven(h) => h.to_scorable_hands(new_tile, TsumoOrRon::Tsumo).next().is_some(),
			Self::Ten(h) => h.to_scorable_hands(new_tile, TsumoOrRon::Tsumo).next().is_some(),
			Self::Thirteen(h) => h.to_scorable_hands(new_tile, TsumoOrRon::Tsumo).next().is_some(),
		})
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
/// Also, since the result of this parse is a `HandStable`, it should not include the newly drawn tile.
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
		let (ts, s) = s.split_once(' ').unwrap_or((s, ""));
		let (ts, ts_type) = Tile::parse_run(ts)?;
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
				let m1 = s.parse()?;
				Hand(
					[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into(),
					[m1].into(),
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7] => {
				let (m1, m2) = s.split_once(' ').ok_or(())?;
				let m1 = m1.parse()?;
				let m2 = m2.parse()?;
				Hand(
					[t1, t2, t3, t4, t5, t6, t7].into(),
					[m1, m2].into(),
				).into()
			},

			[t1, t2, t3, t4] => {
				let (m1, s) = s.split_once(' ').ok_or(())?;
				let m1 = m1.parse()?;
				let (m2, m3) = s.split_once(' ').ok_or(())?;
				let m2 = m2.parse()?;
				let m3 = m3.parse()?;
				Hand(
					[t1, t2, t3, t4].into(),
					[m1, m2, m3].into(),
				).into()
			},

			[t1] => {
				let (m1, s) = s.split_once(' ').ok_or(())?;
				let m1 = m1.parse()?;
				let (m2, s) = s.split_once(' ').ok_or(())?;
				let m2 = m2.parse()?;
				let (m3, m4) = s.split_once(' ').ok_or(())?;
				let m3 = m3.parse()?;
				let m4 = m4.parse()?;
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
	pub fn discard(self, i: usize) -> (HandStable, Tile) {
		match self {
			Self::Two(h) => {
				let (h, t) = h.discard(i);
				(HandStable::One(h), t)
			},
			Self::Five(h) => {
				let (h, t) = h.discard(i);
				(HandStable::Four(h), t)
			},
			Self::Eight(h) => {
				let (h, t) = h.discard(i);
				(HandStable::Seven(h), t)
			},
			Self::Eleven(h) => {
				let (h, t) = h.discard(i);
				(HandStable::Ten(h), t)
			},
			Self::Fourteen(h) => {
				let (h, t) = h.discard(i);
				(HandStable::Thirteen(h), t)
			},
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
	typenum::U1, typenum::U4 => HandStable::One,
	typenum::U2, typenum::U4 => HandTentative::Two,
	typenum::U4, typenum::U3 => HandStable::Four,
	typenum::U5, typenum::U3 => HandTentative::Five,
	typenum::U7, typenum::U2 => HandStable::Seven,
	typenum::U8, typenum::U2 => HandTentative::Eight,
	typenum::U10, typenum::U1 => HandStable::Ten,
	typenum::U11, typenum::U1 => HandTentative::Eleven,
	typenum::U13, typenum::U0 => HandStable::Thirteen,
	typenum::U14, typenum::U0 => HandTentative::Fourteen,
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
		let tiles: Tile34MultiSet = hand.0.into_iter().collect();
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
	NT: ArrayLength + core::ops::Sub<typenum::U4>,
	<NT as core::ops::Sub<typenum::U4>>::Output: ArrayLength,
	NM: ArrayLength + core::ops::Add<typenum::U1>,
	<NM as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = Hand<<NT as core::ops::Sub<typenum::U4>>::Output, <NM as core::ops::Add<typenum::U1>>::Output>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (t_kan, count) = self.tiles.next()?;
			if count.get() == 4 {
				let Hand(ts, ms) = self.hand;

				let mut ts_rest = ArrayVec::new();
				let mut ts_kan = ArrayVec::new();
				for t in ts {
					if t == t_kan {
						let push_result = ts_kan.push(t);
						unsafe { push_result.unwrap_unchecked(); }
					}
					else {
						let push_result = ts_rest.push(t);
						unsafe { push_result.unwrap_unchecked(); }
					}
				}
				let ts_rest = ts_rest.try_into();
				let ts_rest = unsafe { ts_rest.unwrap_unchecked() };
				let ts_kan = ts_kan.try_into();
				let ts_kan: GenericArray<_, typenum::U4> = unsafe { ts_kan.unwrap_unchecked() };
				return Some(Hand(ts_rest, ms.concat([HandMeld::Ankan(ts_kan.into())].into())));
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl<NT, NM> core::iter::FusedIterator for Ankans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<typenum::U4>,
	<NT as core::ops::Sub<typenum::U4>>::Output: ArrayLength,
	NM: ArrayLength + core::ops::Add<typenum::U1>,
	<NM as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{}

/// [`Iterator`] of [`HandStable`] values formed by creating an ankan in the given hand.
#[derive(Clone, Debug)]
pub enum HandAnkans {
	One,
	Four(Ankans<typenum::U5, typenum::U3>),
	Seven(Ankans<typenum::U8, typenum::U2>),
	Ten(Ankans<typenum::U11, typenum::U1>),
	Thirteen(Ankans<typenum::U14, typenum::U0>),
}

impl Iterator for HandAnkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::One(hand);
				Some(hand)
			},
			Self::Seven(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::Four(hand);
				Some(hand)
			},
			Self::Ten(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::Seven(hand);
				Some(hand)
			},
			Self::Thirteen(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::Ten(hand);
				Some(hand)
			},
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

impl core::iter::FusedIterator for HandAnkans {}

fn find_daiminkan<N>(
	ts: GenericArray<Tile, N>,
	new_tile: Tile,
) -> Option<(GenericArray<Tile, <N as core::ops::Sub<typenum::U3>>::Output>, [Tile; 4])>
where
	N: ArrayLength + core::ops::Sub<typenum::U3>,
	<N as core::ops::Sub<typenum::U3>>::Output: ArrayLength,
	GenericArray<Tile, N>: Copy,
{
	let [(i1, t1), (i2, t2), (i3, t3)] = GenericArray::try_from_iter(ts.into_iter().enumerate().filter(|&(_, t)| t == new_tile)).ok()?.into();
	let m = [t1, t2, t3, new_tile];
	let (ts, _) = unsafe { except(ts, [i1, i2, i3].into()) };
	Some((ts, m))
}

/// [`Iterator`] of [`Hand<{ NT - 1 }, NM>`](Hand) values formed by creating a shouminkan in the given hand.
pub struct Shouminkans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	tiles: core::iter::Enumerate<generic_array::GenericArrayIter<Tile, NT>>,
}

impl<NT, NM> Shouminkans<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>) -> Self {
		let tiles = hand.0.into_iter().enumerate();
		Self {
			hand,
			tiles,
		}
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
			tiles: self.tiles.clone(),
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
			.field("tiles", &self.tiles)
			.finish()
	}
}

impl<NT, NM> Iterator for Shouminkans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<typenum::U1>,
	<NT as core::ops::Sub<typenum::U1>>::Output: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy + Remove<Tile, NT, Output = GenericArray<Tile, <NT as core::ops::Sub<typenum::U1>>::Output>>,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = Hand<<NT as core::ops::Sub<typenum::U1>>::Output, NM>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (i, tile) = self.tiles.next()?;
			let mut melds = self.hand.1;
			let mut found = false;
			for m in &mut melds {
				if let HandMeld::Minkou([t1, t2, t3]) = *m && t1 == tile {
					*m = HandMeld::Minkan([t1, t2, t3, tile]);
					found = true;
					break;
				}
			}
			if found {
				let (_, ts) = self.hand.0.remove(i);
				return Some(Hand(ts, melds));
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl<NT, NM> core::iter::FusedIterator for Shouminkans<NT, NM>
where
	NT: ArrayLength + core::ops::Sub<typenum::U1>,
	<NT as core::ops::Sub<typenum::U1>>::Output: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy + Remove<Tile, NT, Output = GenericArray<Tile, <NT as core::ops::Sub<typenum::U1>>::Output>>,
	GenericArray<HandMeld, NM>: Copy,
{}

/// [`Iterator`] of [`HandStable`] values formed by creating an shouminkan in the given hand.
#[derive(Clone, Debug)]
pub enum HandShouminkans {
	One(Shouminkans<typenum::U2, typenum::U4>),
	Four(Shouminkans<typenum::U5, typenum::U3>),
	Seven(Shouminkans<typenum::U8, typenum::U2>),
	Ten(Shouminkans<typenum::U11, typenum::U1>),
	Thirteen,
}

impl Iterator for HandShouminkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::One(hand);
				Some(hand)
			},
			Self::Four(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::Four(hand);
				Some(hand)
			},
			Self::Seven(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::Seven(hand);
				Some(hand)
			},
			Self::Ten(inner) => {
				let hand = inner.next()?;
				let hand = HandStable::Ten(hand);
				Some(hand)
			},
			Self::Thirteen => None,
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			Self::One(inner) => inner.size_hint(),
			Self::Four(inner) => inner.size_hint(),
			Self::Seven(inner) => inner.size_hint(),
			Self::Ten(inner) => inner.size_hint(),
			Self::Thirteen => (0, Some(0)),
		}
	}
}

impl core::iter::FusedIterator for HandShouminkans {}

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minkou
/// in the given hand using the given new tile. Along with the `Hand`, the iterator element contains a list of tile indices
/// in the resulting hand that are allowed to be discarded. Indices that are not present in this list are not allowed to be discarded due to kuikae.
pub struct Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	new_tile: Tile,
	combinations: ArrayVecIntoCombinations<(usize, Tile), NT>,
}

impl<NT, NM> Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>, new_tile: Tile) -> Self {
		let ts_consider: ArrayVec<_, _> = hand.0.into_iter().enumerate().filter(|&(_, t)| t == new_tile).collect();
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
	NT: ArrayLength + core::ops::Sub<typenum::U2>,
	<NT as core::ops::Sub<typenum::U2>>::Output: ArrayLength,
	NM: ArrayLength + core::ops::Add<typenum::U1>,
	<NM as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = (Hand<<NT as core::ops::Sub<typenum::U2>>::Output, <NM as core::ops::Add<typenum::U1>>::Output>, ArrayVec<usize, <NT as core::ops::Sub<typenum::U2>>::Output>);

	fn next(&mut self) -> Option<Self::Item> {
		let ((i1, t1), (i2, t2)) = self.combinations.next()?;
		let ts = [t1, t2, self.new_tile];
		let m = HandMeld::Minkou(ts);
		let (ts, _) = unsafe { except(self.hand.0, [i1, i2].into()) };
		let allowed_discards: ArrayVec<_, _> =
			ts.iter().enumerate()
			.filter_map(|(i, &t)| (t != self.new_tile).then_some(i))
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

/// [`Iterator`] of [`HandTentative`] values formed by creating a minkou
/// in the given hand using the given new tile. Along with the `HandTentative`, the iterator element contains a list of tile indices
/// in the resulting hand that are allowed to be discarded. Indices that are not present in this list are not allowed to be discarded due to kuikae.
#[derive(Clone, Debug)]
pub enum HandMinkous {
	One,
	Four(Minkous<typenum::U4, typenum::U3>),
	Seven(Minkous<typenum::U7, typenum::U2>),
	Ten(Minkous<typenum::U10, typenum::U1>),
	Thirteen(Minkous<typenum::U13, typenum::U0>),
}

impl Iterator for HandMinkous {
	type Item = (HandTentative, ArrayVec<usize, typenum::U11>);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Two(hand);
				let allowed_discards = allowed_discards.into_iter().collect();
				Some((hand, allowed_discards))
			},
			Self::Seven(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Five(hand);
				let allowed_discards = allowed_discards.into_iter().collect();
				Some((hand, allowed_discards))
			},
			Self::Ten(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Eight(hand);
				let allowed_discards = allowed_discards.into_iter().collect();
				Some((hand, allowed_discards))
			},
			Self::Thirteen(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Eleven(hand);
				Some((hand, allowed_discards))
			},
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

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minjun
/// in the given hand using the given new tile. Along with the `Hand`, the iterator element contains a list of tile indices
/// in the resulting hand that are allowed to be discarded. Indices that are not present in this list are not allowed to be discarded due to kuikae.
pub struct Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	new_tile: NumberTile,
	combinations: ArrayVecIntoCombinations<(usize, NumberTile), NT>,
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
				if t.suit() != new_tile.suit() { return None; }
				if !(1..=2).contains(&t.number().value().abs_diff(new_tile.number().value())) { return None; }
				Some((i, t))
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
	NT: ArrayLength + core::ops::Sub<typenum::U2>,
	<NT as core::ops::Sub<typenum::U2>>::Output: ArrayLength,
	NM: ArrayLength + core::ops::Add<typenum::U1>,
	<NM as core::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = (Hand<<NT as core::ops::Sub<typenum::U2>>::Output, <NM as core::ops::Add<typenum::U1>>::Output>, ArrayVec<usize, <NT as core::ops::Sub<typenum::U2>>::Output>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ((i1, t1), (i2, t2)) = self.combinations.next()?;
			let [t1, t2, t3] = {
				let mut ts = [t1, t2, self.new_tile];
				ts.sort_unstable();
				ts
			};
			if t2.is_next_in_sequence(t1) && t3.is_next_in_sequence(t2) {
				let m = HandMeld::Minjun([t1, t2, t3]);
				let (ts, _) = unsafe { except(self.hand.0, [i1, i2].into()) };
				let cannot_discard_new = Tile::from(self.new_tile);
				let cannot_discard_left = if t3 == self.new_tile { t1.previous_in_sequence().map(Tile::from) } else { None };
				let cannot_discard_right = if t1 == self.new_tile { t3.next_in_sequence().map(Tile::from) } else { None };
				let allowed_discards: ArrayVec<_, _> =
					ts.iter().enumerate()
					.filter_map(|(i, &t)| (t != cannot_discard_new && Some(t) != cannot_discard_left && Some(t) != cannot_discard_right).then_some(i))
					.collect();
				if !allowed_discards.is_empty() {
					return Some((Hand(ts, self.hand.1.concat([m].into())), allowed_discards));
				}
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

/// [`Iterator`] of [`HandTentative`] values formed by creating a minjun
/// in the given hand using the given new tile. Along with the `HandTentative`, the iterator element contains a list of tile indices
/// in the resulting hand that are allowed to be discarded. Indices that are not present in this list are not allowed to be discarded due to kuikae.
#[derive(Clone, Debug)]
pub enum HandMinjuns {
	One,
	Four(Minjuns<typenum::U4, typenum::U3>),
	Seven(Minjuns<typenum::U7, typenum::U2>),
	Ten(Minjuns<typenum::U10, typenum::U1>),
	Thirteen(Minjuns<typenum::U13, typenum::U0>),
}

impl Iterator for HandMinjuns {
	type Item = (HandTentative, ArrayVec<usize, typenum::U11>);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Two(hand);
				let allowed_discards = allowed_discards.into_iter().collect();
				Some((hand, allowed_discards))
			},
			Self::Seven(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Five(hand);
				let allowed_discards = allowed_discards.into_iter().collect();
				Some((hand, allowed_discards))
			},
			Self::Ten(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Eight(hand);
				let allowed_discards = allowed_discards.into_iter().collect();
				Some((hand, allowed_discards))
			},
			Self::Thirteen(inner) => {
				let (hand, allowed_discards) = inner.next()?;
				let hand = HandTentative::Eleven(hand);
				Some((hand, allowed_discards))
			},
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

/// # Safety
///
/// Every element of `i_discard` must be distinct and within the bounds of `ts`.
unsafe fn except<T, N, DN>(
	ts: GenericArray<T, N>,
	i_discard: GenericArray<usize, DN>,
) -> (GenericArray<T, <N as core::ops::Sub<DN>>::Output>, GenericArray<T, DN>)
where
	N: ArrayLength + core::ops::Sub<DN>,
	<N as core::ops::Sub<DN>>::Output: ArrayLength,
	DN: ArrayLength,
	GenericArray<usize, DN>: Copy,
{
	let mut ts_result = ArrayVec::new();
	let mut discards = ArrayVec::new();
	for (i, t) in ts.into_iter().enumerate() {
		if i_discard.get(discards.len()).copied() == Some(i) {
			let push_result = discards.push(t);
			unsafe { push_result.unwrap_unchecked(); }
		}
		else {
			let push_result = ts_result.push(t);
			unsafe { push_result.unwrap_unchecked(); }
		}
	}
	let ts_result = ts_result.try_into();
	let ts_result = unsafe { ts_result.unwrap_unchecked() };
	let discards = discards.try_into();
	let discards = unsafe { discards.unwrap_unchecked() };
	(ts_result, discards)
}

struct ArrayAdjacentPairs<T, N> where N: ArrayLength {
	arr: GenericArray<T, N>,
	range: core::ops::Range<usize>,
}

impl<T, N> ArrayAdjacentPairs<T, N>
where
	N: ArrayLength,
{
	fn new(arr: GenericArray<T, N>) -> Self {
		let range = 0..(arr.len().saturating_sub(1));
		Self { arr, range }
	}
}

impl<T, N> ArrayAdjacentPairs<T, N>
where
	T: Copy,
	N: ArrayLength + core::ops::Sub<typenum::U2>,
	<N as core::ops::Sub<typenum::U2>>::Output: ArrayLength,
	GenericArray<T, N>: Copy,
{
	// # Safety
	//
	// `i` and `i + 1` must be within bounds of `self.arr`.
	unsafe fn next_inner(&mut self, i: usize) -> ([T; 2], GenericArray<T, <N as core::ops::Sub<typenum::U2>>::Output>) {
		unsafe { core::hint::assert_unchecked(i + 1 < self.arr.len()) };

		let pt1 = self.arr[i];
		let pt2 = self.arr[i + 1];

		let rest = GenericArray::try_from_iter(self.arr.into_iter().take(i).chain(self.arr.into_iter().skip(i + 2)));
		let rest = unsafe { rest.unwrap_unchecked() };

		([pt1, pt2], rest)
	}
}

impl<T, N> Iterator for ArrayAdjacentPairs<T, N>
where
	T: Copy,
	N: ArrayLength + core::ops::Sub<typenum::U2>,
	<N as core::ops::Sub<typenum::U2>>::Output: ArrayLength,
	GenericArray<T, N>: Copy,
{
	type Item = ([T; 2], GenericArray<T, <N as core::ops::Sub<typenum::U2>>::Output>);

	fn next(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end < self.arr.len()) };

		let i = self.range.next()?;
		Some(unsafe { self.next_inner(i) })
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.range.size_hint();
		(0, hi)
	}
}

impl<T, N> DoubleEndedIterator for ArrayAdjacentPairs<T, N>
where
	T: Copy,
	N: ArrayLength + core::ops::Sub<typenum::U2>,
	<N as core::ops::Sub<typenum::U2>>::Output: ArrayLength,
	GenericArray<T, N>: Copy,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };
		unsafe { core::hint::assert_unchecked(self.range.end < self.arr.len()) };

		let i = self.range.next_back()?;
		Some(unsafe { self.next_inner(i) })
	}
}

impl<T, N> ExactSizeIterator for ArrayAdjacentPairs<T, N> where N: ArrayLength, Self: Iterator {}

fn merge_sorted<T, N1, N2>(arr1: &GenericArray<T, N1>, arr2: &GenericArray<T, N2>) -> GenericArray<T, <N1 as core::ops::Add<N2>>::Output>
where
	T: Copy + core::cmp::PartialOrd,
	N1: ArrayLength + core::ops::Add<N2>,
	N2: ArrayLength,
	<N1 as core::ops::Add<N2>>::Output: ArrayLength,
{
	fn merge_sorted_inner<T>(dst: &mut [core::mem::MaybeUninit<T>], s1: &[T], s2: &[T]) where T: Copy + core::cmp::PartialOrd {
		let mut a_s = s1.iter().copied();
		let mut b_s = s2.iter().copied();
		let mut a_prev = None;
		let mut b_prev = None;
		let iter = core::iter::from_fn(move || {
			match (a_prev.take().or_else(|| a_s.next()), b_prev.take().or_else(|| b_s.next())) {
				(Some(a), Some(b)) =>
					if a <= b {
						b_prev = Some(b);
						Some(a)
					}
					else {
						a_prev = Some(a);
						Some(b)
					},

				(Some(a), None) => Some(a),

				(None, Some(b)) => Some(b),

				(None, None) => None,
			}
		});
		for (dst, src) in dst.iter_mut().zip(iter) {
			dst.write(src);
		}
	}

	let mut result = GenericArray::<_, <N1 as core::ops::Add<N2>>::Output>::uninit();
	merge_sorted_inner(&mut result, arr1, arr2);
	unsafe { GenericArray::assume_init(result) }
}

fn is_kan([t1, t2, t3, t4]: [Tile; 4]) -> bool {
	t2 == t1 && t3 == t2 && t4 == t3
}

fn is_kou([t1, t2, t3]: [Tile; 3]) -> bool {
	t2 == t1 && t3 == t2
}

fn is_shun([t1, t2, t3]: [NumberTile; 3]) -> bool {
	t2.is_next_in_sequence(t1) && t3.is_next_in_sequence(t2)
}

const fn to_kou([(t1, t1tr), (t2, t2tr), (t3, t3tr)]: [(Tile, Option<TsumoOrRon>); 3]) -> ScorableHandFourthMeld {
	let tiles = [t1, t2, t3];
	let was_completed_with_ron = matches!(t1tr, Some(TsumoOrRon::Ron)) || matches!(t2tr, Some(TsumoOrRon::Ron)) || matches!(t3tr, Some(TsumoOrRon::Ron));
	let tsumo_or_ron = if was_completed_with_ron { TsumoOrRon::Ron } else { TsumoOrRon::Tsumo };

	if t1tr.is_none() && t2tr.is_none() && t3tr.is_none() {
		ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(tiles))
	}
	else {
		ScorableHandFourthMeld::Shanpon { tiles, tsumo_or_ron }
	}
}

const fn to_shun([(t1, t1tr), (t2, t2tr), (t3, t3tr)]: [(NumberTile, Option<TsumoOrRon>); 3]) -> ScorableHandFourthMeld {
	let tiles = [t1, t2, t3];
	let was_completed_with_ron = matches!(t1tr, Some(TsumoOrRon::Ron)) || matches!(t2tr, Some(TsumoOrRon::Ron)) || matches!(t3tr, Some(TsumoOrRon::Ron));
	let tsumo_or_ron = if was_completed_with_ron { TsumoOrRon::Ron } else { TsumoOrRon::Tsumo };

	match (t1tr.is_some(), t2tr.is_some(), t3tr.is_some()) {
		(false, false, false) => ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun([t1, t2, t3])),
		(true, _, _) =>
			if t3.number().value() == 9 {
				ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron }
			}
			else {
				ScorableHandFourthMeld::RyanmenLeft { tiles, tsumo_or_ron }
			},
		(_, true, _) => ScorableHandFourthMeld::Kanchan { tiles, tsumo_or_ron },
		(_, _, true) =>
			if t1.number().value() == 1 {
				ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron }
			}
			else {
				ScorableHandFourthMeld::RyanmenRight { tiles, tsumo_or_ron }
			},
	}
}

fn meld_and_rest<N>(
	ts: GenericArray<(Tile, Option<TsumoOrRon>), N>,
) -> impl Iterator<Item = (ScorableHandFourthMeld, GenericArray<(Tile, Option<TsumoOrRon>), <N as core::ops::Sub<typenum::U3>>::Output>)>
where
	N: ArrayLength + core::ops::Sub<typenum::U3>,
	<N as core::ops::Sub<typenum::U3>>::Output: ArrayLength,
	GenericArray<(Tile, Option<TsumoOrRon>), N>: Copy,
{
	let (t1, t1tr) = ts[0];

	// There are at most two unique kous:
	//
	// - Any kous that use the new tile will be formed as `ScorableHandFourthMeld::Shanpon`, and we only need one of them.
	//
	// - Any kous that don't use the new tile will be formed as `ScorableHandFourthMeld::Tanki`, and we only need one of them.
	//
	// If t1 is the new tile, then only the `ScorableHandFourthMeld::Shanpon` will be found so we don't need to look for the `ScorableHandFourthMeld::Tanki`.
	let mut kou_non_tanki_and_rest = None;
	let mut kou_tanki_and_rest = None;
	{
		let kou_and_rests = {
			// If t1 is an old tile, we only need one t2 that is an old tile and one t2 that is a new tile.
			// If t1 is a new tile, then we only need one t2 that is an old tile.
			let t2s =
				ts.into_iter().skip(1).enumerate()
				.try_fold((None, None), |(mut old, mut new), (i2, (t2, t2tr))| {
					if t2 != t1 { return core::ops::ControlFlow::Continue((old, new)); }
					if old.is_none() && t2tr.is_none() {
						old = Some((i2, t2));
					}
					if new.is_none() && let Some(t2tr) = t2tr {
						new = Some((i2, t2, t2tr));
					}
					if old.is_some() && (t1tr.is_some() || new.is_some()) {
						core::ops::ControlFlow::Break((old, new))
					}
					else {
						core::ops::ControlFlow::Continue((old, new))
					}
				});
			// TODO(rustup): Use `core::ops::ControlFlow::into_value` when that is stabilized.
			let (t2_old, t2_new) = match t2s {
				core::ops::ControlFlow::Continue(value) |
				core::ops::ControlFlow::Break(value) => value,
			};
			[
				t2_old.map(|(i2_old, t2_old)| (i2_old, t2_old, None)),
				t2_new.map(|(i2_new, t2_new, t2tr_new)| (i2_new, t2_new, Some(t2tr_new))),
			].into_iter()
				.flatten()
				.flat_map(move |(i2, t2, t2tr)| {
					// If t1 and t2 are old tiles, we only need one t3 that is an old tile and one t3 that is a new tile.
					// If either t1 or t2 is a new tile, then we only need one t3 that is an old tile.
					let t3s =
						ts.into_iter().skip(1).enumerate()
						.skip(i2 + 1)
						.try_fold((None, None), |(mut old, mut new), (i3, (t3, t3tr))| {
							if t3 != t1 { return core::ops::ControlFlow::Continue((old, new)); }
							if old.is_none() && t3tr.is_none() {
								old = Some((i3, t3));
							}
							if new.is_none() && let Some(t3tr) = t3tr {
								new = Some((i3, t3, t3tr));
							}
							if old.is_some() && (t1tr.is_some() || t2tr.is_some() || new.is_some()) {
								core::ops::ControlFlow::Break((old, new))
							}
							else {
								core::ops::ControlFlow::Continue((old, new))
							}
						});
					// TODO(rustup): Use `core::ops::ControlFlow::into_value` when that is stabilized.
					let (t3_old, t3_new) = match t3s {
						core::ops::ControlFlow::Continue(value) |
						core::ops::ControlFlow::Break(value) => value,
					};
					[
						t3_old.map(|(i3_old, t3_old)| (i3_old, t3_old, None)),
						t3_new.map(|(i3_new, t3_new, t3tr_new)| (i3_new, t3_new, Some(t3tr_new))),
					].into_iter()
						.flatten()
						.map(move |(i3, t3, t3tr)| (i2, t2, t2tr, i3, t3, t3tr))
				})
				.map(move |(i2, t2, t2tr, i3, t3, t3tr)| {
					let m1 = to_kou([(t1, t1tr), (t2, t2tr), (t3, t3tr)]);
					let ts = GenericArray::try_from_iter(ts.into_iter().skip(1).enumerate().filter_map(|(i, t)| (i != i2 && i != i3).then_some(t)));
					let ts = unsafe { ts.unwrap_unchecked() };
					(m1, ts)
				})
		};
		for (kou, rest) in kou_and_rests {
			let result = if matches!(kou, ScorableHandFourthMeld::Tanki(_)) { &mut kou_tanki_and_rest } else { &mut kou_non_tanki_and_rest };
			if result.is_none() {
				*result = Some((kou, rest));
			}
			if (t1tr.is_some() || kou_tanki_and_rest.is_some()) && kou_non_tanki_and_rest.is_some() {
				break;
			}
		}
	};

	// There are at most two unique shuns.
	//
	// - Any shuns that use the new tile will be formed as `ScorableHandFourthMeld::{Kanchan | Penchan | RyanmenLeft | RyanmenRight}`, and we only need one of them.
	//   It doesn't matter which one we pick, since the ones we didn't pick will be found when the caller calls `meld_and_rest` on the `Tanki` result's `rest` tiles.
	//
	//   Eg if the tiles are 2334556s + 4s, the calls to `meld_and_rest` will produce these:
	//
	//   [2334556s + 4s]
	//   -> { anjun 2s 3s 4s ryanmen_right }, [344556s]
	//       -> { anjun 2s 3s 4s ryanmen_right }, { anjun 3s 4s 5s }, [456s]
	//           -> { anjun 2s 3s 4s ryanmen_right }, { anjun 3s 4s 5s }, { anjun 4s 5s 6s }
	//   -> { anjun 2s 3s 4s }, [34556s + 4s]
	//       -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s kanchan }, [456s]
	//           -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s kanchan }, { anjun 4s 5s 6s }
	//       -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s }, [56s + 4s]
	//           -> { anjun 2s 3s 4s }, { anjun 3s 4s 5s }, { anjun 4s 5s 6s ryanmen_left }
	//
	//   ... which are indeed all the sets of melds that can be formed from the given tiles.
	//
	// - Any shuns that don't use the new tile will be formed as `ScorableHandFourthMeld::Tanki`, and we only need one of them.
	//
	// If t1 is the new tile, then only the `ScorableHandFourthMeld::{Kanchan | Penchan | RyanmenLeft | RyanmenRight}` will be found so we don't need to look for the `ScorableHandFourthMeld::Tanki`.
	let mut shun_non_tanki_and_rest = None;
	let mut shun_tanki_and_rest = None;
	if
		let Ok(t1) = NumberTile::try_from(t1) &&
		let Some((t2_expected, t3_expected)) = t1.shun_rest()
	{
		let shun_and_rests = {
			// If t1 is an old tile, we only need one t2 that is an old tile and one t2 that is a new tile.
			// If t1 is a new tile, then we only need one t2 that is an old tile.
			let t2s =
				ts.into_iter().skip(1).enumerate()
				.try_fold((None, None), |(mut old, mut new), (i2, (t2, t2tr))| {
					let Ok(t2) = NumberTile::try_from(t2) else { return core::ops::ControlFlow::Continue((old, new)); };
					if t2 != t2_expected { return core::ops::ControlFlow::Continue((old, new)); }
					if old.is_none() && t2tr.is_none() {
						old = Some((i2, t2));
					}
					if new.is_none() && let Some(t2tr) = t2tr {
						new = Some((i2, t2, t2tr));
					}
					if old.is_some() && (t1tr.is_some() || new.is_some()) {
						core::ops::ControlFlow::Break((old, new))
					}
					else {
						core::ops::ControlFlow::Continue((old, new))
					}
				});
			// TODO(rustup): Use `core::ops::ControlFlow::into_value` when that is stabilized.
			let (t2_old, t2_new) = match t2s {
				core::ops::ControlFlow::Continue(value) |
				core::ops::ControlFlow::Break(value) => value,
			};
			[
				t2_old.map(|(i2_old, t2_old)| (i2_old, t2_old, None)),
				t2_new.map(|(i2_new, t2_new, t2tr_new)| (i2_new, t2_new, Some(t2tr_new))),
			].into_iter()
				.flatten()
				.flat_map(move |(i2, t2, t2tr)| {
					// If t1 and t2 are old tiles, we only need one t3 that is an old tile and one t3 that is a new tile.
					// If either t1 or t2 is a new tile, then we only need one t3 that is an old tile.
					let t3s =
						ts.into_iter().skip(1).enumerate()
						.skip(i2 + 1)
						.try_fold((None, None), |(mut old, mut new), (i3, (t3, t3tr))| {
							let Ok(t3) = NumberTile::try_from(t3) else { return core::ops::ControlFlow::Continue((old, new)); };
							if t3 != t3_expected { return core::ops::ControlFlow::Continue((old, new)); }
							if old.is_none() && t3tr.is_none() {
								old = Some((i3, t3));
							}
							if new.is_none() && let Some(t3tr) = t3tr {
								new = Some((i3, t3, t3tr));
							}
							if old.is_some() && (t1tr.is_some() || t2tr.is_some() || new.is_some()) {
								core::ops::ControlFlow::Break((old, new))
							}
							else {
								core::ops::ControlFlow::Continue((old, new))
							}
						});
					// TODO(rustup): Use `core::ops::ControlFlow::into_value` when that is stabilized.
					let (t3_old, t3_new) = match t3s {
						core::ops::ControlFlow::Continue(value) |
						core::ops::ControlFlow::Break(value) => value,
					};
					[
						t3_old.map(|(i3_old, t3_old)| (i3_old, t3_old, None)),
						t3_new.map(|(i3_new, t3_new, t3tr_new)| (i3_new, t3_new, Some(t3tr_new))),
					].into_iter()
						.flatten()
						.map(move |(i3, t3, t3tr)| (i2, t2, t2tr, i3, t3, t3tr))
				})
				.map(move |(i2, t2, t2tr, i3, t3, t3tr)| {
					let m1 = to_shun([(t1, t1tr), (t2, t2tr), (t3, t3tr)]);
					let ts = GenericArray::try_from_iter(ts.into_iter().skip(1).enumerate().filter_map(|(i, t)| (i != i2 && i != i3).then_some(t)));
					let ts = unsafe { ts.unwrap_unchecked() };
					(m1, ts)
				})
		};
		for (shun, rest) in shun_and_rests {
			let result = if matches!(shun, ScorableHandFourthMeld::Tanki(_)) { &mut shun_tanki_and_rest } else { &mut shun_non_tanki_and_rest };
			if result.is_none() {
				*result = Some((shun, rest));
			}
			if (t1tr.is_some() || shun_tanki_and_rest.is_some()) && shun_non_tanki_and_rest.is_some() {
				break;
			}
		}
	}

	[
		kou_non_tanki_and_rest,
		kou_tanki_and_rest,
		shun_non_tanki_and_rest,
		shun_tanki_and_rest,
	].into_iter().flatten()
}

fn to_meld([(t1, t1tr), (t2, t2tr), (t3, t3tr)]: [(Tile, Option<TsumoOrRon>); 3]) -> Option<ScorableHandFourthMeld> {
	if is_kou([t1, t2, t3]) {
		Some(to_kou([(t1, t1tr), (t2, t2tr), (t3, t3tr)]))
	}
	else if
		let Ok(t1) = NumberTile::try_from(t1) &&
		let Ok(t2) = NumberTile::try_from(t2) &&
		let Ok(t3) = NumberTile::try_from(t3) &&
		is_shun([t1, t2, t3])
	{
		Some(to_shun([(t1, t1tr), (t2, t2tr), (t3, t3tr)]))
	}
	else {
		None
	}
}

fn to_melds_2(ts: [(Tile, Option<TsumoOrRon>); 6]) -> impl Iterator<Item = (ScorableHandMeld, ScorableHandFourthMeld)> {
	let mas = meld_and_rest(ts.into());
	let mabs = Dedup::new(mas).filter_map(|(ma, ts)| to_meld(ts.into()).map(|mb| {
		if mb >= ma { (ma, mb) }
		else { (mb, ma) }
	}));
	Dedup::new(mabs)
		.map(|(ma, mb)| match (ma, mb) {
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb)) =>
				(ma, ScorableHandFourthMeld::Tanki(mb)),

			(m4, ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m3), m4) =>
				(m3, m4),

			// At most one meld can be non-tanki
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
}

fn to_melds_3(ts: [(Tile, Option<TsumoOrRon>); 9]) -> impl Iterator<Item = ([ScorableHandMeld; 2], ScorableHandFourthMeld)> {
	let mas = meld_and_rest(ts.into());
	let mabs = Dedup::new(mas).flat_map(|(ma, ts)| meld_and_rest(ts).map(move |(mb, ts)| {
		if mb >= ma { (ma, mb, ts) }
		else { (mb, ma, ts) }
	}));
	let mabcs = Dedup::new(mabs).filter_map(|(ma, mb, ts)| to_meld(ts.into()).map(|mc| {
		if mc >= mb { (ma, mb, mc) }
		else if mc >= ma { (ma, mc, mb) }
		else { (mc, ma, mb) }
	}));
	Dedup::new(mabcs)
		.map(|(ma, mb, mc)| match (ma, mb, mc) {
			(ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), ScorableHandFourthMeld::Tanki(m4)) =>
				([m2, m3], ScorableHandFourthMeld::Tanki(m4)),

			(m4, ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m2), m4, ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), m4) =>
				([m2, m3], m4),

			// At most one meld can be non-tanki
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
}

fn to_melds_4(ts: [(Tile, Option<TsumoOrRon>); 12]) -> impl Iterator<Item = ([ScorableHandMeld; 3], ScorableHandFourthMeld)> {
	let mas = meld_and_rest(ts.into());
	let mabs = mas.flat_map(|(ma, ts)| meld_and_rest(ts).map(move |(mb, ts)| {
		if mb >= ma { (ma, mb, ts) }
		else { (mb, ma, ts) }
	}));
	let mabcs = Dedup::new(mabs).flat_map(|(ma, mb, ts)| meld_and_rest(ts).map(move |(mc, ts)| {
		if mc >= mb { (ma, mb, mc, ts) }
		else if mc >= ma { (ma, mc, mb, ts) }
		else { (mc, ma, mb, ts) }
	}));
	let mabcds = Dedup::new(mabcs).filter_map(|(ma, mb, mc, ts)| to_meld(ts.into()).map(|md| {
		if md >= mc { (ma, mb, mc, md) }
		else if md >= mb { (ma, mb, md, mc) }
		else if md >= ma { (ma, md, mb, mc) }
		else { (md, ma, mb, mc) }
	}));
	Dedup::new(mabcds)
		.map(|(ma, mb, mc, md)| match (ma, mb, mc, md) {
			(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), ScorableHandFourthMeld::Tanki(m4)) =>
				([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)),

			(m4, ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m1), m4, ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), m4, ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), m4) =>
				([m1, m2, m3], m4),

			// At most one meld can be non-tanki
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
}

struct Dedup<I> where I: Iterator {
	inner: I,
	prev: Option<I::Item>,
}

impl<I> Dedup<I> where I: Iterator {
	const fn new(inner: I) -> Self {
		Self { inner, prev: None }
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

fn to_chiitoi(
	[(t1, _), (t2, _), (t3, _), (t4, _), (t5, _), (t6, _), (t7, _), (t8, _), (t9, _), (t10, _), (t11, _), (t12, _), (t13, _), (t14, _)]: [(Tile, Option<TsumoOrRon>); 14],
) -> Option<ScorableHand> {
	let is_chiitoi =
		(t1, t3, t5, t7, t9, t11, t13) == (t2, t4, t6, t8, t10, t12, t14) &&
		t2 != t3 &&
		t4 != t5 &&
		t6 != t7 &&
		t8 != t9 &&
		t10 != t11 &&
		t12 != t13;
	is_chiitoi.then_some(ScorableHand::Chiitoi([
		ScorableHandPair([t1, t2]),
		ScorableHandPair([t3, t4]),
		ScorableHandPair([t5, t6]),
		ScorableHandPair([t7, t8]),
		ScorableHandPair([t9, t10]),
		ScorableHandPair([t11, t12]),
		ScorableHandPair([t13, t14]),
	]))
}

fn to_kokushi_musou(ts: [Tile; 14], new_tile: Tile) -> Option<ScorableHand> {
	let mut tiles: Tile34MultiSet = ts.into_iter().collect();
	let was_juusanmen_wait = tiles.get(new_tile) == 2;
	let is_kokushi_musou =
		tiles.remove_all(t!(1m)) >= 1 &&
		tiles.remove_all(t!(9m)) >= 1 &&
		tiles.remove_all(t!(1p)) >= 1 &&
		tiles.remove_all(t!(9p)) >= 1 &&
		tiles.remove_all(t!(1s)) >= 1 &&
		tiles.remove_all(t!(9s)) >= 1 &&
		tiles.remove_all(t!(E)) >= 1 &&
		tiles.remove_all(t!(S)) >= 1 &&
		tiles.remove_all(t!(W)) >= 1 &&
		tiles.remove_all(t!(N)) >= 1 &&
		tiles.remove_all(t!(Wh)) >= 1 &&
		tiles.remove_all(t!(G)) >= 1 &&
		tiles.remove_all(t!(R)) >= 1 &&
		tiles.is_empty();
	is_kokushi_musou.then_some(ScorableHand::KokushiMusou { tiles: ts, was_juusanmen_wait })
}

#[cfg(test)]
mod tests {
	extern crate std;

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
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s ryanmen_left }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_left }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_right }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_left }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_right }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_left }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_right }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_left }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_right }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_left }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_right }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s penchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s ryanmen_right }),
		]
	}

	fn to_ttrs(meld: ScorableHandFourthMeld) -> [(Tile, Option<TsumoOrRon>); 3] {
		match meld {
			ScorableHandFourthMeld::Tanki(m) => match m {
				ScorableHandMeld::Ankou([t1, t2, t3]) => [(t1, None), (t2, None), (t3, None)],
				ScorableHandMeld::Anjun([t1, t2, t3]) => [(t1.into(), None), (t2.into(), None), (t3.into(), None)],
				_ => unreachable!(),
			},
			ScorableHandFourthMeld::Kanchan { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), None), (t2.into(), Some(tsumo_or_ron)), (t3.into(), None)],
			ScorableHandFourthMeld::Penchan { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), matches!(t1, tn!(7m | 7p | 7s)).then_some(tsumo_or_ron)), (t2.into(), None), (t3.into(), matches!(t3, tn!(3m | 3p | 3s)).then_some(tsumo_or_ron))],
			ScorableHandFourthMeld::RyanmenLeft { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), Some(tsumo_or_ron)), (t2.into(), None), (t3.into(), None)],
			ScorableHandFourthMeld::RyanmenRight { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), None), (t2.into(), None), (t3.into(), Some(tsumo_or_ron))],
			ScorableHandFourthMeld::Shanpon { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1, None), (t2, None), (t3, Some(tsumo_or_ron))],
		}
	}

	#[test]
	fn to_meld() {
		for expected in melds_last() {
			let [(t1, t1tr), (t2, t2tr), (t3, t3tr)] = to_ttrs(expected);

			let mut ts = [(t1, t1tr), (t2, t2tr), (t3, t3tr)];
			ts.sort_unstable_by_key(|(t, _)| *t);
			let actual = super::to_meld(ts);
			assert_eq!(actual, Some(expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
		}

		// 124 -> X
		assert_eq!(super::to_meld([(t!(1s), None), (t!(2s), None), (t!(4s), None)]), None);
	}

	#[test]
	fn to_melds_2() {
		let melds = melds();
		let melds_last = melds_last();

		for ma in melds {
			let [t1, t2, t3] = match ma {
				ScorableHandMeld::Ankou(ts) => ts,
				ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
				_ => unreachable!(),
			};
			let mut used: Tile34MultiSet = Default::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}
			for mb in melds.into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last) {
				let [(t4, t4tr), (t5, t5tr), (t6, t6tr)] = to_ttrs(mb);

				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				let expected =
					if let ScorableHandFourthMeld::Tanki(mb) = mb {
						let mut ms = [ma, mb];
						ms.sort_unstable();
						let [m3, m4] = ms;
						(m3, ScorableHandFourthMeld::Tanki(m4))
					}
					else {
						(ma, mb)
					};

				let mut ts = [(t1, None), (t2, None), (t3, None), (t4, t4tr), (t5, t5tr), (t6, t6tr)];
				ts.sort_unstable_by_key(|(t, _)| *t);
				let actual: std::vec::Vec<_> = super::to_melds_2(ts).collect();
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
				ScorableHandMeld::Ankou(ts) => ts,
				ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
				_ => unreachable!(),
			};
			let mut used: Tile34MultiSet = Default::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}

			for mb in melds {
				let [t4, t5, t6] = match mb {
					ScorableHandMeld::Ankou(ts) => ts,
					ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
					_ => unreachable!(),
				};
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				for mc in melds.into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last) {
					let [(t7, t7tr), (t8, t8tr), (t9, t9tr)] = to_ttrs(mc);

					let mut used = used.clone();
					if used.try_extend([t7, t8, t9]).is_err() {
						continue;
					}

					let expected =
						if let ScorableHandFourthMeld::Tanki(mc) = mc {
							let mut ms = [ma, mb, mc];
							ms.sort_unstable();
							let [m2, m3, m4] = ms;
							([m2, m3], ScorableHandFourthMeld::Tanki(m4))
						}
						else {
							let mut ms = [ma, mb];
							ms.sort_unstable();
							let [m2, m3] = ms;
							([m2, m3], mc)
						};

					let mut ts = [(t1, None), (t2, None), (t3, None), (t4, None), (t5, None), (t6, None), (t7, t7tr), (t8, t8tr), (t9, t9tr)];
					ts.sort_unstable_by_key(|(t, _)| *t);
					let actual: std::vec::Vec<_> = super::to_melds_3(ts).collect();
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
				ScorableHandMeld::Ankou(ts) => ts,
				ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
				_ => unreachable!(),
			};
			let mut used: Tile34MultiSet = Default::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}

			for mb in melds {
				let [t4, t5, t6] = match mb {
					ScorableHandMeld::Ankou(ts) => ts,
					ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
					_ => unreachable!(),
				};
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				for mc in melds {
					let [t7, t8, t9] = match mc {
						ScorableHandMeld::Ankou(ts) => ts,
						ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
						_ => unreachable!(),
					};
					let mut used = used.clone();
					if used.try_extend([t7, t8, t9]).is_err() {
						continue;
					}

					for md in melds.into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last) {
						let [(t10, t10tr), (t11, t11tr), (t12, t12tr)] = to_ttrs(md);

						let mut used = used.clone();
						if used.try_extend([t10, t11, t12]).is_err() {
							continue;
						}

						let expected =
							if let ScorableHandFourthMeld::Tanki(md) = md {
								let mut ms = [ma, mb, mc, md];
								ms.sort_unstable();
								let [m1, m2, m3, m4] = ms;
								([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
							}
							else {
								let mut ms = [ma, mb, mc];
								ms.sort_unstable();
								let [m1, m2, m3] = ms;
								([m1, m2, m3], md)
							};

						let mut ts = [(t1, None), (t2, None), (t3, None), (t4, None), (t5, None), (t6, None), (t7, None), (t8, None), (t9, None), (t10, t10tr), (t11, t11tr), (t12, t12tr)];
						ts.sort_unstable_by_key(|(t, _)| *t);
						let actual: std::vec::Vec<_> = super::to_melds_4(ts).collect();
						assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
					}
				}
			}
		}
	}

	#[test]
	fn find_ankans() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		let mut ankans = h.find_ankans(t!(E));
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
		let mut shouminkans = h.find_shouminkans(t!(E));
		assert_eq!(shouminkans.next().unwrap(), Hand(t![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m, G].into(), [make_hand!(@meld { minkan E E E E })].into()));
		assert_eq!(shouminkans.next(), None);
	}

	#[test]
	fn find_minkous() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let minkous = h.find_minkous(t!(2m));

		{
			// 22m => 2C2 = 1
			assert_eq!(minkous.size_hint(), (0, Some(1)));
			let mut minkous = minkous.clone();
			assert!(matches!(minkous.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m].into(), [make_hand!(@meld { minkou 2m 2m 2m })].into()) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minkous.size_hint(), (0, Some(0)));
			assert!(minkous.next().is_none());
			assert_eq!(minkous.size_hint(), (0, Some(0)));
		}

		let hs: std::vec::Vec<_> = minkous.collect();
		assert_eq!(hs.len(), 1);
		assert!(hs[0].0 == Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m].into(), [make_hand!(@meld { minkou 2m 2m 2m })].into()) && hs[0].1 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let minjuns = h.find_minjuns(tn!(4m));

		{
			// 23506m => 5C2 = 10
			assert_eq!(minjuns.size_hint(), (0, Some(10)));
			let mut minjuns = minjuns.clone();
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 2m 3m 4m })].into()) && allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(9)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 5m })].into()) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(5)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 0m })].into()) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(4)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 5m 6m })].into()) && allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(1)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 0m 6m })].into()) && allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
			assert!(minjuns.next().is_none());
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
		}

		let hs: std::vec::Vec<_> = minjuns.collect();
		assert_eq!(hs.len(), 5);
		assert!(hs[0].0 == Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 2m 3m 4m })].into()) && hs[0].1 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert!(hs[1].0 == Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 5m })].into()) && hs[1].1 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert!(hs[2].0 == Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 0m })].into()) && hs[2].1 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert!(hs[3].0 == Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 5m 6m })].into()) && hs[3].1 == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]);
		assert!(hs[4].0 == Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 0m 6m })].into()) && hs[4].1 == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]);
	}

	#[test]
	fn kuikae() {
		{
			let h = make_hand!(1m 1m 1m E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minkous(t!(1m)).collect();
			for (h, allowed_discards) in hs {
				assert_eq!(h, Hand(t![1m, E, E, E, S, S, S, W, W, W, N].into(), [make_hand!(@meld { minkou 1m 1m 1m })].into()));
				assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
			}
		}

		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(2p)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![2p, E, E, E, S, S, S, W, W, W, N].into(), [make_hand!(@meld { minjun 1p 2p 3p })].into()));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1s)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1s, E, E, E, S, S, S, W, W, W, N].into(), [make_hand!(@meld { minjun 1s 2s 3s })].into()));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1s)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1s, E, E, E, S, S, S, W, W, W, N].into(), [make_hand!(@meld { minjun 1s 2s 3s })].into()));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(4m)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1m, E, E, E, S, S, S, W, W, W, N].into(), [make_hand!(@meld { minjun 2m 3m 4m })].into()));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1p 2p 3p 4p { minkou E E E } { minkou S S S } { minkou W W W });
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1p)).collect();
			assert!(hs.is_empty(), "{hs:?}");
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(4m)).collect();
			assert_eq!(hs.len(), 3);
			assert!(matches!(&hs[0], (h, allowed_discards) if *h == Hand(t![1m, 4m, 5m, 6m, E, E, E, S, S, S, W].into(), [make_hand!(@meld { minjun 2m 3m 4m })].into()) && *allowed_discards == [2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert!(matches!(&hs[1], (h, allowed_discards) if *h == Hand(t![1m, 2m, 4m, 6m, E, E, E, S, S, S, W].into(), [make_hand!(@meld { minjun 3m 4m 5m })].into()) && *allowed_discards == [0, 1, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert!(matches!(&hs[2], (h, allowed_discards) if *h == Hand(t![1m, 2m, 3m, 4m, E, E, E, S, S, S, W].into(), [make_hand!(@meld { minjun 4m 5m 6m })].into()) && *allowed_discards == [0, 1, 2, 4, 5, 6, 7, 8, 9, 10]));
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(7m)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1m, 2m, 3m, 4m, E, E, E, S, S, S, W].into(), [make_hand!(@meld { minjun 5m 6m 7m })].into()));
			assert_eq!(*allowed_discards, [0, 1, 2, 4, 5, 6, 7, 8, 9, 10]);
		}
	}

	#[test]
	fn tenpai() {
		{
			let h = make_hand!(5p 6p 0s 6s 7s 8s 8s Wh Wh Wh { minkou R R R });
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![4p, 7p]);
		}

		{
			let h = make_hand!(4m 5m 6p 7p 8p 1s 2s 3s 4s 5s 6s 8s 8s);
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![3m, 6m]);
		}

		{
			let h = make_hand!(1m 1m 4p 4p { minkou N N N } { minkou 3p 3p 3p } { minkou R R R });
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![1m, 4p]);
		}

		{
			let h = make_hand!(1m 1m 4m 5m 6m 3p 4p 4p 0p 6p 1s 2s 3s);
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![2p, 5p]);
		}

		{
			let h = make_hand!(4m 4m 1p 2p 3p 0p 5p 1s 2s 3s { minjun 1m 2m 3m });
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![4m, 5p]);
		}

		{
			let h = make_hand!(3p 3p 4p 4p 0p 5p 7p 8p 8p 8p 9p G G);
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![8p, G]);
		}

		{
			let h = make_hand!(4m 0m 6m 7m 7m 4s 0s 6s 7s 8s { minjun 4p 5p 6p });
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![3s, 6s, 9s]);
		}

		{
			let h = make_hand!(1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m);
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m]);
		}

		{
			let h = make_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R);
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R]);
		}
	}
}
