use generic_array::{
	ArrayLength,
	GenericArray,
	functional::FunctionalSequence as _,
	sequence::{Concat as _, Remove},
	typenum,
};

use crate::{
	HandMeldType,
	NumberTile,
	ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair,
	Tile, Tile34MultiSet, TsumoOrRon,
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
/// - `Minjun` really contains three [`NumberTile`]s that would form a valid sequence.
///
/// - `Minkou` really contains three of the same [`Tile`], except that if two of them are [`Number::Five`][crate::Number::Five]s
///   then the third may be a [`Number::FiveRed`][crate::Number::FiveRed].
///
/// - `Minkan` really contains four of the same [`Tile`], except that if three of them are [`Number::Five`][crate::Number::Five]s
///   then the fourth may be a [`Number::FiveRed`][crate::Number::FiveRed].
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program will still be safe, but `to_scorable_hands()`
/// will produce an unspecified and meaningless result. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum HandMeld {
	/// Open sequence formed by chii.
	Minjun([NumberTile; 3]),
	/// Open triplet formed by pon.
	Minkou([Tile; 3]),
	/// Closed quad formed by kan.
	Ankan([Tile; 4]),
	/// Open quad formed by kan.
	Minkan([Tile; 4]),
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
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	HandStable: From<Self>,
{
	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> Minjuns<NT, NM> {
		Minjuns::new(self, new_tile)
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> Minkous<NT, NM> {
		Minkous::new(self, new_tile)
	}

	/// Find a possible shouminkan (quad via kan call on a minkou formed previously) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_shouminkan(self, new_tile: Tile) -> Option<Self> {
		let Self(ts, ms) = self;
		Some(Self(ts, find_shouminkan(ms, new_tile)?))
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + std::ops::Sub<typenum::U3>,
	<NT as std::ops::Sub<typenum::U3>>::Output: ArrayLength,
	NM: ArrayLength + std::ops::Add<typenum::U1>,
	<NM as std::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	HandStable: From<Self>,
{
	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NT + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<<NT as std::ops::Sub<typenum::U3>>::Output, <NM as std::ops::Add<typenum::U1>>::Output>> {
		let Self(ts, ms) = self;
		find_kan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, ms.concat([HandMeld::Minkan(m_new)].into())))
	}

	/// Find a possible ankan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NT + 1 }>` that would result from this call, if any.
	pub fn find_ankan(self, new_tile: Tile) -> Option<Hand<<NT as std::ops::Sub<typenum::U3>>::Output, <NM as std::ops::Add<typenum::U1>>::Output>> {
		let Self(ts, ms) = self;
		find_kan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, ms.concat([HandMeld::Ankan(m_new)].into())))
	}
}

impl<NT, NM> Hand<NT, NM>
where
	NT: ArrayLength + std::ops::Sub<typenum::U1>,
	<NT as std::ops::Sub<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Remove<Tile, NT, Output = GenericArray<Tile, <NT as std::ops::Sub<typenum::U1>>::Output>>,
	NM: ArrayLength,
	HandTentative: From<Hand<NT, NM>>,
{
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile, and the discarded tile.
	// TODO: Check for kuikae
	pub fn discard(self, i: usize) -> (Hand<<NT as std::ops::Sub<typenum::U1>>::Output, NM>, Tile) {
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

impl<NT, NM> std::fmt::Debug for Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: std::fmt::Display,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl<NT, NM> std::fmt::Display for Hand<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
	pub fn to_scorable_hands(self, new_tile: Tile) -> Option<ScorableHand> {
		let Self(ts, ms) = self;
		let [t1] = ts.into();

		if t1 == new_tile {
			let [m1, m2, m3, m4] = ms.map(Into::into).into();
			Some(ScorableHand::regular([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4), ScorableHandPair([t1, new_tile])))
		}
		else {
			None
		}
	}
}

impl Hand<typenum::U4, typenum::U3> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let ts = {
			let [t1, t2, t3, t4] = ts.map(|t| (t, None)).into();
			let mut ts = [t1, t2, t3, t4, (new_tile, Some(tsumo_or_ron))];
			ts.sort_unstable();
			GenericArray::from(ts)
		};
		let [m1, m2, m3] = ms.map(Into::into).into();

		ts.windows(2).enumerate()
			.filter_map(|(i, pts)| {
				let &[(pt1, _), (pt2, _)] = pts else { unsafe { std::hint::unreachable_unchecked(); } };
				if pt1 != pt2 {
					return None;
				}
				let rest = unsafe { skip_adjacent_2(ts, i) };
				let m4 = to_meld(rest.into())?;
				Some(ScorableHand::regular([m1, m2, m3], m4, ScorableHandPair([pt1, pt2])))
			})
			.collect()
	}
}

impl Hand<typenum::U7, typenum::U2> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let ts = {
			let [t1, t2, t3, t4, t5, t6, t7] = ts.map(|t| (t, None)).into();
			let mut ts = [t1, t2, t3, t4, t5, t6, t7, (new_tile, Some(tsumo_or_ron))];
			ts.sort_unstable();
			GenericArray::from(ts)
		};
		let [m1, m2] = ms.map(Into::into).into();

		ts.windows(2).enumerate()
			.filter_map(|(i, pts)| {
				let &[(pt1, _), (pt2, _)] = pts else { unsafe { std::hint::unreachable_unchecked(); } };
				if pt1 != pt2 {
					return None;
				}
				let rest = unsafe { skip_adjacent_2(ts, i) };
				Some((rest.into(), pt1, pt2))
			})
			.flat_map(|(rest, pt1, pt2)| to_melds_2(rest).into_iter().map(move |(m3, m4)| ScorableHand::regular([m1, m2, m3], m4, ScorableHandPair([pt1, pt2]))))
			.collect()
	}
}

impl Hand<typenum::U10, typenum::U1> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let ts = {
			let [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] = ts.map(|t| (t, None)).into();
			let mut ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, (new_tile, Some(tsumo_or_ron))];
			ts.sort_unstable();
			GenericArray::from(ts)
		};
		let [m1] = ms.map(Into::into).into();

		ts.windows(2).enumerate()
			.filter_map(|(i, pts)| {
				let &[(pt1, _), (pt2, _)] = pts else { unsafe { std::hint::unreachable_unchecked(); } };
				if pt1 != pt2 {
					return None;
				}
				let rest = unsafe { skip_adjacent_2(ts, i) };
				Some((rest.into(), pt1, pt2))
			})
			.flat_map(|(rest, pt1, pt2)| to_melds_3(rest).into_iter().map(move |([m2, m3], m4)| ScorableHand::regular([m1, m2, m3], m4, ScorableHandPair([pt1, pt2]))))
			.collect()
	}
}

impl Hand<typenum::U13, typenum::U0> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let mut result: std::collections::BTreeSet<_> = Default::default();
		self.to_scorable_hands_inner(new_tile, tsumo_or_ron, &mut result);
		result
	}

	fn to_scorable_hands_inner(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon, result: &mut std::collections::BTreeSet<ScorableHand>) {
		let Self(ts, ms) = self;
		let ts = {
			let [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] = ts.map(|t| (t, None)).into();
			let mut ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, (new_tile, Some(tsumo_or_ron))];
			ts.sort_unstable();
			GenericArray::from(ts)
		};
		let [] = ms.into();

		result.extend(
			ts.windows(2).enumerate()
			.filter_map(|(i, pts)| {
				let &[(pt1, _), (pt2, _)] = pts else { unsafe { std::hint::unreachable_unchecked(); } };
				if pt1 != pt2 {
					return None;
				}
				let rest = unsafe { skip_adjacent_2(ts, i) };
				Some((rest.into(), pt1, pt2))
			})
			.flat_map(|(rest, pt1, pt2)| to_melds_4(rest).into_iter().map(move |([m1, m2, m3], m4)| ScorableHand::regular([m1, m2, m3], m4, ScorableHandPair([pt1, pt2])))),
		);

		if let Some(h) = to_chiitoi(ts.into()) {
			result.insert(h);
		}

		if let Some(h) = to_kokushi_musou(ts.map(|(t, _)| t).into(), new_tile) {
			result.insert(h);
		}
	}
}

impl Hand<typenum::U14, typenum::U0> {
	/// Convert this hand into a set of [`ScorableHand`]s by considering each tile as a new tile.
	///
	/// This is used for rulesets where tenhou can be won by considering any tile of the starting hand as the new tile.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let mut result: std::collections::BTreeSet<_> = Default::default();

		for i in 0..ts.len() {
			let (ts, new_tile) = unsafe { except(ts, [i].into()) };
			let [new_tile] = new_tile.into();
			Hand(ts, ms).to_scorable_hands_inner(new_tile, TsumoOrRon::Tsumo, &mut result);
		}

		result
	}
}

impl std::fmt::Debug for HandMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for HandMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Minjun([t1, t2, t3]) =>
				write!(f, "{{ minjun {t1} {t2} {t3} }}"),
			Self::Minkou([t1, t2, t3]) =>
				write!(f, "{{ minkou {t1} {t2} {t3} }}"),
			Self::Ankan([t1, t2, t3, t4]) =>
				write!(f, "{{ ankan {t1} {t2} {t3} {t4} }}"),
			Self::Minkan([t1, t2, t3, t4]) =>
				write!(f, "{{ minkan {t1} {t2} {t3} {t4} }}"),
		}
	}
}

impl Ord for HandMeld {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		let t: Tile = match *self {
			Self::Minjun([t, ..]) => t.into(),
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => t,
		};
		let t_other = match *other {
			Self::Minjun([t, ..]) => t.into(),
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => t,
		};
		#[expect(clippy::match_same_arms)]
		t.cmp(&t_other).then_with(|| match (self, other) {
			(Self::Minjun(_), Self::Minjun(_)) => std::cmp::Ordering::Equal,
			(Self::Minjun(_), Self::Minkou(_) | Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minkou(_), Self::Minjun(_)) => std::cmp::Ordering::Greater,
			(Self::Minkou(_), Self::Minkou(_)) => std::cmp::Ordering::Equal,
			(Self::Minkou(_), Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Ankan(_), Self::Minjun(_) | Self::Minkou(_)) => std::cmp::Ordering::Greater,
			(Self::Ankan(_), Self::Ankan(_)) => std::cmp::Ordering::Equal,
			(Self::Ankan(_), Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minkan(_), Self::Minjun(_) | Self::Minkou(_) | Self::Ankan(_)) => std::cmp::Ordering::Greater,
			(Self::Minkan(_), Self::Minkan(_)) => std::cmp::Ordering::Equal,
		})
	}
}

impl PartialOrd for HandMeld {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl HandStable {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		match self {
			Self::One(h) => h.to_scorable_hands(new_tile).into_iter().collect(),
			Self::Four(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
			Self::Seven(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
			Self::Ten(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
			Self::Thirteen(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
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

	/// Find a possible shouminkan (quad via kan call on a minkou formed previously) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_shouminkan(self, new_tile: Tile) -> Option<Self> {
		Some(match self {
			Self::One(h) => Self::One(h.find_shouminkan(new_tile)?),
			Self::Four(h) => Self::Four(h.find_shouminkan(new_tile)?),
			Self::Seven(h) => Self::Seven(h.find_shouminkan(new_tile)?),
			Self::Ten(h) => Self::Ten(h.find_shouminkan(new_tile)?),
			Self::Thirteen(h) => Self::Thirteen(h.find_shouminkan(new_tile)?),
		})
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

	/// Find a possible ankan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_ankan(self, new_tile: Tile) -> Option<Self> {
		Some(match self {
			Self::One(_) => return None,
			Self::Four(h) => Self::One(h.find_ankan(new_tile)?),
			Self::Seven(h) => Self::Four(h.find_ankan(new_tile)?),
			Self::Ten(h) => Self::Seven(h.find_ankan(new_tile)?),
			Self::Thirteen(h) => Self::Ten(h.find_ankan(new_tile)?),
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
/// # use riichi::{
/// #     HandStable,
/// #     make_hand,
/// #     t,
/// # };
/// #
/// // chii, chii
/// let h: HandStable = "4477m1p11z 7-68m 5-46s".parse().unwrap();
/// assert_eq!(h, HandStable::Seven(make_hand!(4m 4m 7m 7m 1p E E { minjun 6m 7m 8m } { minjun 4s 5s 6s })));
///
/// // chii, pon
/// let h: HandStable = "35m3378p3467s 2-22m".parse().unwrap();
/// assert_eq!(h, HandStable::Ten(make_hand!(3m 5m 3p 3p 7p 8p 3s 4s 6s 7s { minkou 2m 2m 2m })));
///
/// // chii, shouminkan
/// let h: HandStable = "3377p678s 2-34s 2=222m".parse().unwrap();
/// assert_eq!(h, HandStable::Seven(make_hand!(3p 3p 7p 7p 6s 7s 8s { minjun 2s 3s 4s } { minkan 2m 2m 2m 2m })));
///
/// // chii, daiminkan
/// let h: HandStable = "1309p789s 5555-z 5-46p".parse().unwrap();
/// assert_eq!(h, HandStable::Seven(make_hand!(1p 3p 0p 9p 7s 8s 9s { minkan Wh Wh Wh Wh } { minjun 4p 5p 6p })));
/// ```
impl std::str::FromStr for HandStable {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		fn identify_meld(ty: Option<HandMeldType>, ts: &[Tile]) -> Result<Option<HandMeld>, ()> {
			Ok(Some(match (ty, ts) {
				(None, &[]) => return Ok(None),

				(Some(HandMeldType::MinjunMinkouDaiminkan), &[t1, t2, t3]) =>
					if t2 == t1 && t3 == t2 {
						HandMeld::Minkou([t1, t2, t3])
					}
					else if
						let Ok(t1) = NumberTile::try_from(t1) &&
						let Ok(t2) = NumberTile::try_from(t2) &&
						let Ok(t3) = NumberTile::try_from(t3)
					{
						let mut ts = [t1, t2, t3];
						ts.sort_unstable();
						let [t1, t2, t3] = ts;
						let Some((t2_expected, t3_expected)) = t1.shun_rest() else { return Err(()); };
						if t2 == t2_expected && t3 == t3_expected {
							HandMeld::Minjun([t1, t2, t3])
						}
						else {
							return Err(());
						}
					}
					else {
						return Err(());
					},

				(Some(HandMeldType::MinjunMinkouDaiminkan | HandMeldType::Shouminkan), &[t1, t2, t3, t4])
					if t2 == t1 && t3 == t2 && t4 == t3 =>
						HandMeld::Minkan([t1, t2, t3, t4]),

				(Some(HandMeldType::Ankan), &[t1, t2, t3, t4])
					if t2 == t1 && t3 == t2 && t4 == t3 =>
						HandMeld::Ankan([t1, t2, t3, t4]),

				_ => return Err(()),
			}))
		}

		let mut ts_type = None;
		let mut ts = vec![];
		let (mut m1_type, mut m1) = (None, vec![]);
		let (mut m2_type, mut m2) = (None, vec![]);
		let (mut m3_type, mut m3) = (None, vec![]);
		let (mut m4_type, mut m4) = (None, vec![]);

		{
			let mut collections = [(&mut m1_type, &mut m1), (&mut m2_type, &mut m2), (&mut m3_type, &mut m3), (&mut m4_type, &mut m4)].into_iter();
			let (mut current_collection_type, mut current_collection) = (&mut ts_type, &mut ts);
			for s in s.split(' ') {
				(*current_collection, *current_collection_type) = Tile::parse_run(s)?;
				(current_collection_type, current_collection) = collections.next().ok_or(())?;
			}
		}

		if ts_type.is_some() {
			return Err(());
		}

		Ok(match (&ts[..], identify_meld(m1_type, &m1)?, identify_meld(m2_type, &m2)?, identify_meld(m3_type, &m3)?, identify_meld(m4_type, &m4)?) {
			(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13], None, None, None, None) => Hand(
				[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into(),
				[].into(),
			).into(),

			(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10], Some(m1), None, None, None) => Hand(
				[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into(),
				[m1].into(),
			).into(),

			(&[t1, t2, t3, t4, t5, t6, t7], Some(m1), Some(m2), None, None) => Hand(
				[t1, t2, t3, t4, t5, t6, t7].into(),
				[m1, m2].into(),
			).into(),

			(&[t1, t2, t3, t4], Some(m1), Some(m2), Some(m3), None) => Hand(
				[t1, t2, t3, t4].into(),
				[m1, m2, m3].into(),
			).into(),

			(&[t1], Some(m1), Some(m2), Some(m3), Some(m4)) => Hand(
				[t1].into(),
				[m1, m2, m3, m4].into(),
			).into(),

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

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minjun
/// in the given hand using the given new tile.
pub struct Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	new_tile: NumberTile,
	ts_consider_raw: GenericArray<std::mem::MaybeUninit<(usize, NumberTile)>, NT>,
	combinations: Combinations,
}

impl<NT, NM> Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>, new_tile: NumberTile) -> Self {
		let mut ts_consider_raw = GenericArray::uninit();
		let mut ts_consider_len = 0;
		let ts_consider =
			hand.0.into_iter()
			.enumerate()
			.filter_map(|(i, t)|
				if
					let Ok(t) = NumberTile::try_from(t) &&
					t.suit() == new_tile.suit() &&
					(1..=2).contains(&t.number().value().abs_diff(new_tile.number().value()))
				{
					Some((i, t))
				}
				else {
					None
				},
			);
		for (i, t) in ts_consider {
			ts_consider_raw[ts_consider_len].write((i, t));
			ts_consider_len += 1;
		}

		Self {
			hand,
			new_tile,
			ts_consider_raw,
			combinations: Combinations::new(ts_consider_len),
		}
	}
}

impl<NT, NM> Clone for Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: Copy,
	GenericArray<std::mem::MaybeUninit<(usize, NumberTile)>, NT>: Copy,
{
	fn clone(&self) -> Self {
		Self {
			hand: self.hand,
			new_tile: self.new_tile,
			ts_consider_raw: self.ts_consider_raw,
			combinations: self.combinations.clone(),
		}
	}
}

impl<NT, NM> std::fmt::Debug for Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("Minjuns")
			.field("hand", &self.hand)
			.field("new_tile", &self.new_tile)
			.field("combinations", &self.combinations)
			.finish_non_exhaustive()
	}
}

impl<NT, NM> Iterator for Minjuns<NT, NM>
where
	NT: ArrayLength + std::ops::Sub<typenum::U2>,
	<NT as std::ops::Sub<typenum::U2>>::Output: ArrayLength,
	NM: ArrayLength + std::ops::Add<typenum::U1>,
	<NM as std::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = Hand<<NT as std::ops::Sub<typenum::U2>>::Output, <NM as std::ops::Add<typenum::U1>>::Output>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (i1, i2) = self.combinations.next()?;
			let (i1, t1) = unsafe { self.ts_consider_raw[i1].assume_init() };
			let (i2, t2) = unsafe { self.ts_consider_raw[i2].assume_init() };
			let [t1, t2, t3] = {
				let mut ts = [t1, t2, self.new_tile];
				ts.sort_unstable();
				ts
			};
			if t2.number() == t1.number().next_in_sequence() && t3.number() == t2.number().next_in_sequence() {
				let m = HandMeld::Minjun([t1, t2, t3]);
				let (ts, _) = unsafe { except(self.hand.0, [i1, i2].into()) };
				// TODO: Track kuikae
				return Some(Hand(ts, self.hand.1.concat([m].into())));
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.combinations.size_hint();
		(0, hi)
	}
}

impl<NT, NM> std::iter::FusedIterator for Minjuns<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Self: Iterator,
{}

/// [`Iterator`] of [`HandTentative`] values formed by creating a minjun
/// in the given hand using the given new tile.
#[derive(Clone, Debug)]
pub enum HandMinjuns {
	One,
	Four(Minjuns<typenum::U4, typenum::U3>),
	Seven(Minjuns<typenum::U7, typenum::U2>),
	Ten(Minjuns<typenum::U10, typenum::U1>),
	Thirteen(Minjuns<typenum::U13, typenum::U0>),
}

impl Iterator for HandMinjuns {
	type Item = HandTentative;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(HandTentative::Two),
			Self::Seven(inner) => inner.next().map(HandTentative::Five),
			Self::Ten(inner) => inner.next().map(HandTentative::Eight),
			Self::Thirteen(inner) => inner.next().map(HandTentative::Eleven),
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

impl std::iter::FusedIterator for HandMinjuns {}

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minkou
/// in the given hand using the given new tile.
pub struct Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	hand: Hand<NT, NM>,
	new_tile: Tile,
	ts_consider_raw: GenericArray<std::mem::MaybeUninit<(usize, Tile)>, NT>,
	combinations: Combinations,
}

impl<NT, NM> Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	GenericArray<Tile, NT>: Copy,
{
	fn new(hand: Hand<NT, NM>, new_tile: Tile) -> Self {
		let mut ts_consider_raw = GenericArray::uninit();
		let mut ts_consider_len = 0;
		for (i, t) in hand.0.into_iter().enumerate().filter(|&(_, t)| t == new_tile) {
			ts_consider_raw[ts_consider_len].write((i, t));
			ts_consider_len += 1;
		}

		Self {
			hand,
			new_tile,
			ts_consider_raw,
			combinations: Combinations::new(ts_consider_len),
		}
	}
}

impl<NT, NM> Clone for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Hand<NT, NM>: Copy,
	GenericArray<std::mem::MaybeUninit<(usize, Tile)>, NT>: Copy,
{
	fn clone(&self) -> Self {
		Self {
			hand: self.hand,
			new_tile: self.new_tile,
			ts_consider_raw: self.ts_consider_raw,
			combinations: self.combinations.clone(),
		}
	}
}

impl<NT, NM> std::fmt::Debug for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("Minkous")
			.field("hand", &self.hand)
			.field("new_tile", &self.new_tile)
			.field("combinations", &self.combinations)
			.finish_non_exhaustive()
	}
}

impl<NT, NM> Iterator for Minkous<NT, NM>
where
	NT: ArrayLength + std::ops::Sub<typenum::U2>,
	<NT as std::ops::Sub<typenum::U2>>::Output: ArrayLength,
	NM: ArrayLength + std::ops::Add<typenum::U1>,
	<NM as std::ops::Add<typenum::U1>>::Output: ArrayLength,
	GenericArray<Tile, NT>: Copy,
	GenericArray<HandMeld, NM>: Copy,
{
	type Item = Hand<<NT as std::ops::Sub<typenum::U2>>::Output, <NM as std::ops::Add<typenum::U1>>::Output>;

	fn next(&mut self) -> Option<Self::Item> {
		let (i1, i2) = self.combinations.next()?;
		let (i1, t1) = unsafe { self.ts_consider_raw[i1].assume_init() };
		let (i2, t2) = unsafe { self.ts_consider_raw[i2].assume_init() };
		let ts = [t1, t2, self.new_tile];
		let m = HandMeld::Minkou(ts);
		let (ts, _) = unsafe { except(self.hand.0, [i1, i2].into()) };
		// TODO: Track kuikae
		Some(Hand(ts, self.hand.1.concat([m].into())))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.combinations.size_hint()
	}
}

impl<NT, NM> ExactSizeIterator for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Self: Iterator,
{}

impl<NT, NM> std::iter::FusedIterator for Minkous<NT, NM>
where
	NT: ArrayLength,
	NM: ArrayLength,
	Self: Iterator,
{}

/// [`Iterator`] of [`HandTentative`] values formed by creating a minkou
/// in the given hand using the given new tile.
#[derive(Clone, Debug)]
pub enum HandMinkous {
	One,
	Four(Minkous<typenum::U4, typenum::U3>),
	Seven(Minkous<typenum::U7, typenum::U2>),
	Ten(Minkous<typenum::U10, typenum::U1>),
	Thirteen(Minkous<typenum::U13, typenum::U0>),
}

impl Iterator for HandMinkous {
	type Item = HandTentative;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(HandTentative::Two),
			Self::Seven(inner) => inner.next().map(HandTentative::Five),
			Self::Ten(inner) => inner.next().map(HandTentative::Eight),
			Self::Thirteen(inner) => inner.next().map(HandTentative::Eleven),
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

impl ExactSizeIterator for HandMinkous {}

impl std::iter::FusedIterator for HandMinkous {}

#[derive(Clone, Debug)]
struct Combinations {
	n: usize,
	i1: usize,
	i2: usize,
}

impl Combinations {
	fn new(n: usize) -> Self {
		Self { n, i1: 0, i2: 1 }
	}
}

impl Iterator for Combinations {
	type Item = (usize, usize);

	fn next(&mut self) -> Option<Self::Item> {
		if self.i2 >= self.n {
			None
		}
		else {
			let result = Some((self.i1, self.i2));
			if self.i1 + 1 < self.i2 {
				self.i1 += 1;
			}
			else {
				self.i1 = 0;
				self.i2 += 1;
			}
			result
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = (self.n * self.n.saturating_sub(1) / 2) - (self.i2 * (self.i2 - 1) / 2) - self.i1;
		(len, Some(len))
	}
}

impl ExactSizeIterator for Combinations {}

impl std::iter::FusedIterator for Combinations {}

fn find_shouminkan<N>(mut ms: GenericArray<HandMeld, N>, new_tile: Tile) -> Option<GenericArray<HandMeld, N>>
where
	N: ArrayLength,
{
	let mut found = false;
	for m in &mut ms {
		if let HandMeld::Minkou([t1, t2, t3]) = *m && t1 == new_tile {
			*m = HandMeld::Minkan([t1, t2, t3, new_tile]);
			found = true;
			break;
		}
	}
	found.then_some(ms)
}

fn find_kan<N>(
	ts: GenericArray<Tile, N>,
	new_tile: Tile,
) -> Option<(GenericArray<Tile, <N as std::ops::Sub<typenum::U3>>::Output>, [Tile; 4])>
where
	N: ArrayLength + std::ops::Sub<typenum::U3>,
	<N as std::ops::Sub<typenum::U3>>::Output: ArrayLength,
	GenericArray<Tile, N>: Copy,
{
	let [(i1, t1), (i2, t2), (i3, t3)] = GenericArray::try_from_iter(ts.into_iter().enumerate().filter(|&(_, t)| t == new_tile)).ok()?.into();
	let m = [t1, t2, t3, new_tile];
	let (ts, _) = unsafe { except(ts, [i1, i2, i3].into()) };
	Some((ts, m))
}

/// # Safety
///
/// Every element of `i_discard` must be distinct and within the bounds of `ts`.
unsafe fn except<T, N, DN>(
	ts: GenericArray<T, N>,
	i_discard: GenericArray<usize, DN>,
) -> (GenericArray<T, <N as std::ops::Sub<DN>>::Output>, GenericArray<T, DN>)
where
	N: ArrayLength + std::ops::Sub<DN>,
	<N as std::ops::Sub<DN>>::Output: ArrayLength,
	DN: ArrayLength,
	GenericArray<usize, DN>: Copy,
{
	let mut discards = GenericArray::uninit();
	let mut discards_i = 0_usize;
	let mut ts_result = GenericArray::uninit();
	let mut ts_result_i = 0_usize;
	for (i, t) in ts.into_iter().enumerate() {
		if i_discard.get(discards_i).copied() == Some(i) {
			discards[discards_i].write(t);
			discards_i += 1;
		}
		else {
			ts_result[ts_result_i].write(t);
			ts_result_i += 1;
		}
	}
	let ts_result = unsafe { GenericArray::assume_init(ts_result) };
	let discards = unsafe { GenericArray::assume_init(discards) };
	(ts_result, discards)
}

/// # Safety
///
/// `pt1_i` must be within the bounds of `ts`.
unsafe fn skip_adjacent_2<T, N>(ts: GenericArray<T, N>, pt1_i: usize) -> GenericArray<T, <N as std::ops::Sub<typenum::U2>>::Output>
where
	T: Copy,
	N: ArrayLength + std::ops::Sub<typenum::U2>,
	<N as std::ops::Sub<typenum::U2>>::Output: ArrayLength,
	GenericArray<T, N>: Copy,
{
	let rest = GenericArray::try_from_iter(ts.into_iter().take(pt1_i).chain(ts.into_iter().skip(pt1_i + 2)));
	unsafe { rest.unwrap_unchecked() }
}

fn is_shun([t1, t2, t3]: [NumberTile; 3]) -> bool {
	t2.is_next_in_sequence(t1) && t3.is_next_in_sequence(t2)
}

fn is_kou([t1, t2, t3]: [Tile; 3]) -> bool {
	t2 == t1 && t3 == t2
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

const fn to_kou([(t1, t1tr), (t2, t2tr), (t3, t3tr)]: [(Tile, Option<TsumoOrRon>); 3]) -> ScorableHandFourthMeld {
	let tiles = [t1, t2, t3];
	let was_completed_with_ron = matches!(t1tr, Some(TsumoOrRon::Ron)) || matches!(t2tr, Some(TsumoOrRon::Ron)) || matches!(t3tr, Some(TsumoOrRon::Ron));
	let tsumo_or_ron = if was_completed_with_ron { TsumoOrRon::Ron } else { TsumoOrRon::Tsumo };

	if t1tr.is_some() || t2tr.is_some() || t3tr.is_some() {
		ScorableHandFourthMeld::Shanpon { tiles, tsumo_or_ron }
	}
	else {
		ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(tiles))
	}
}

fn meld_and_rest<N>(
	ts: GenericArray<(Tile, Option<TsumoOrRon>), N>,
) -> impl Iterator<Item = (ScorableHandFourthMeld, GenericArray<(Tile, Option<TsumoOrRon>), <N as std::ops::Sub<typenum::U3>>::Output>)>
where
	N: ArrayLength + std::ops::Sub<typenum::U3>,
	<N as std::ops::Sub<typenum::U3>>::Output: ArrayLength,
	GenericArray<(Tile, Option<TsumoOrRon>), N>: Copy,
{
	let (t1, t1tr) = ts[0];

	// There are at most two unique kous:
	//
	// - Any kous that use the new tile will be formed as `ScorableHandFourthMeld::Shanpon`, and we only need one of them.
	//
	// - Any kous that don't use the new tile will be formed as `ScorableHandFourthMeld::Tanki`, and we only need one of them.
	let mut kou_non_tanki_and_rest = None;
	let mut kou_tanki_and_rest = None;
	{
		let kou_and_rests = ts.into_iter().skip(1).enumerate()
			.filter(|(_, (t2, _))| *t2 == t1)
			.flat_map(move |(i2, (t2, t2tr))| {
				ts.into_iter().skip(1).enumerate()
				.skip(i2 + 1)
				.filter(move |(_, (t3, _))| *t3 == t1)
				.map(move |(i3, (t3, t3tr))| {
					let m1 = to_kou([(t1, t1tr), (t2, t2tr), (t3, t3tr)]);
					let ts = GenericArray::try_from_iter(ts.into_iter().skip(1).enumerate().filter_map(|(i, t)| (i != i2 && i != i3).then_some(t)));
					let ts = unsafe { ts.unwrap_unchecked() };
					(m1, ts)
				})
			});
		for (kou, rest) in kou_and_rests {
			let result = if matches!(kou, ScorableHandFourthMeld::Tanki(_)) { &mut kou_tanki_and_rest } else { &mut kou_non_tanki_and_rest };
			if result.is_none() {
				*result = Some((kou, rest));
			}
			if kou_tanki_and_rest.is_some() && kou_non_tanki_and_rest.is_some() {
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
	let mut shun_non_tanki_and_rest = None;
	let mut shun_tanki_and_rest = None;
	if
		let Ok(t1) = NumberTile::try_from(t1) &&
		let Some((t2_expected, t3_expected)) = t1.shun_rest()
	{
		let shun_and_rests =
			ts.into_iter().skip(1).enumerate()
			.filter_map(move |(i2, (t2, t2tr))| {
				let t2 = NumberTile::try_from(t2).ok()?;
				(t2 == t2_expected).then_some((i2, t2, t2tr))
			})
			.flat_map(move |(i2, t2, t2tr)|
				ts.into_iter().skip(1).enumerate()
				.skip(i2 + 1)
				.filter_map(move |(i3, (t3, t3tr))| {
					let t3 = NumberTile::try_from(t3).ok()?;
					(t3 == t3_expected).then_some((i2, t2, t2tr, i3, t3, t3tr))
				}),
			)
			.map(move |(i2, t2, t2tr, i3, t3, t3tr)| {
				let m1 = to_shun([(t1, t1tr), (t2, t2tr), (t3, t3tr)]);
				let ts = GenericArray::try_from_iter(ts.into_iter().skip(1).enumerate().filter_map(|(i, t)| (i != i2 && i != i3).then_some(t)));
				let ts = unsafe { ts.unwrap_unchecked() };
				(m1, ts)
			});
		for (shun, rest) in shun_and_rests {
			let result = if matches!(shun, ScorableHandFourthMeld::Tanki(_)) { &mut shun_tanki_and_rest } else { &mut shun_non_tanki_and_rest };
			if result.is_none() {
				*result = Some((shun, rest));
			}
			if shun_tanki_and_rest.is_some() && shun_non_tanki_and_rest.is_some() {
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

fn to_melds_2(ts: [(Tile, Option<TsumoOrRon>); 6]) -> std::collections::BTreeSet<(ScorableHandMeld, ScorableHandFourthMeld)> {
	meld_and_rest(ts.into())
		.filter_map(|(ma, ts)| to_meld(ts.into()).map(|mb| (ma, mb)))
		.map(|(ma, mb)| match (ma, mb) {
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb)) => {
				let mut ms = [ma, mb];
				ms.sort_unstable();
				let [m3, m4] = ms;
				(m3, ScorableHandFourthMeld::Tanki(m4))
			},

			(m4, ScorableHandFourthMeld::Tanki(m3)) |
			(ScorableHandFourthMeld::Tanki(m3), m4) => (m3, m4),

			// At most one meld can be non-tanki
			_ => unsafe { std::hint::unreachable_unchecked(); },
		})
		.collect()
}

fn to_melds_3(ts: [(Tile, Option<TsumoOrRon>); 9]) -> std::collections::BTreeSet<([ScorableHandMeld; 2], ScorableHandFourthMeld)> {
	meld_and_rest(ts.into())
		.flat_map(|(ma, ts)| meld_and_rest(ts).map(move |(mb, ts)| (ma, mb, ts))
		.filter_map(|(ma, mb, ts)| to_meld(ts.into()).map(|mc| (ma, mb, mc))
		.map(|(ma, mb, mc)| match (ma, mb, mc) {
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb), ScorableHandFourthMeld::Tanki(mc)) => {
				let mut ms = [ma, mb, mc];
				ms.sort_unstable();
				let [m2, m3, m4] = ms;
				([m2, m3], ScorableHandFourthMeld::Tanki(m4))
			},

			(m4, ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb)) |
			(ScorableHandFourthMeld::Tanki(ma), m4, ScorableHandFourthMeld::Tanki(mb)) |
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb), m4) => {
				let mut ms = [ma, mb];
				ms.sort_unstable();
				let [m2, m3] = ms;
				([m2, m3], m4)
			},

			// At most one meld can be non-tanki
			_ => unsafe { std::hint::unreachable_unchecked(); },
		})))
		.collect()
}

fn to_melds_4(ts: [(Tile, Option<TsumoOrRon>); 12]) -> std::collections::BTreeSet<([ScorableHandMeld; 3], ScorableHandFourthMeld)> {
	meld_and_rest(ts.into())
		.flat_map(|(ma, ts)| meld_and_rest(ts).map(move |(mb, ts)| (ma, mb, ts)))
		.flat_map(|(ma, mb, ts)| meld_and_rest(ts).map(move |(mc, ts)| (ma, mb, mc, ts)))
		.filter_map(|(ma, mb, mc, ts)| to_meld(ts.into()).map(|m4| (ma, mb, mc, m4)))
		.map(|(ma, mb, mc, m4)| match (ma, mb, mc, m4) {
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb), ScorableHandFourthMeld::Tanki(mc), ScorableHandFourthMeld::Tanki(m4)) => {
				let mut ms = [ma, mb, mc, m4];
				ms.sort_unstable();
				let [m1, m2, m3, m4] = ms;
				([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
			},

			(m4, ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb), ScorableHandFourthMeld::Tanki(mc)) |
			(ScorableHandFourthMeld::Tanki(ma), m4, ScorableHandFourthMeld::Tanki(mb), ScorableHandFourthMeld::Tanki(mc)) |
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb), m4, ScorableHandFourthMeld::Tanki(mc)) |
			(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb), ScorableHandFourthMeld::Tanki(mc), m4) => {
				let mut ms = [ma, mb, mc];
				ms.sort_unstable();
				let [m1, m2, m3] = ms;
				([m1, m2, m3], m4)
			},

			// At most one meld can be non-tanki
			_ => unsafe { std::hint::unreachable_unchecked(); },
		})
		.collect()
}

fn to_chiitoi(
	[(t1, _), (t2, _), (t3, _), (t4, _), (t5, _), (t6, _), (t7, _), (t8, _), (t9, _), (t10, _), (t11, _), (t12, _), (t13, _), (t14, _)]: [(Tile, Option<TsumoOrRon>); 14],
) -> Option<ScorableHand> {
	let is_chiitoi =
		t1 == t2 &&
		t2 != t3 &&
		t3 == t4 &&
		t4 != t5 &&
		t5 == t6 &&
		t6 != t7 &&
		t7 == t8 &&
		t8 != t9 &&
		t9 == t10 &&
		t10 != t11 &&
		t11 == t12 &&
		t12 != t13 &&
		t13 == t14;
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
			ScorableHandFourthMeld::Kanchan { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), None), (t2.into(), Some(tsumo_or_ron)), (t3.into(), None)],
			ScorableHandFourthMeld::Penchan { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), matches!(t1, tn!(7m | 7p | 7s)).then_some(tsumo_or_ron)), (t2.into(), None), (t3.into(), matches!(t3, tn!(3m | 3p | 3s)).then_some(tsumo_or_ron))],
			ScorableHandFourthMeld::RyanmenLeft { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), Some(tsumo_or_ron)), (t2.into(), None), (t3.into(), None)],
			ScorableHandFourthMeld::RyanmenRight { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), None), (t2.into(), None), (t3.into(), Some(tsumo_or_ron))],
			ScorableHandFourthMeld::Shanpon { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1, None), (t2, None), (t3, Some(tsumo_or_ron))],
			ScorableHandFourthMeld::Tanki(m) => match m {
				ScorableHandMeld::Anjun([t1, t2, t3]) => [(t1.into(), None), (t2.into(), None), (t3.into(), None)],
				ScorableHandMeld::Ankou([t1, t2, t3]) => [(t1, None), (t2, None), (t3, None)],
				_ => unreachable!(),
			},
		}
	}

	#[test]
	fn to_meld() {
		for expected in melds_last() {
			let [(t1, t1tr), (t2, t2tr), (t3, t3tr)] = to_ttrs(expected);

			let mut ts = [(t1, t1tr), (t2, t2tr), (t3, t3tr)];
			ts.sort_unstable();
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
				ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
				ScorableHandMeld::Ankou(ts) => ts,
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
				ts.sort_unstable();
				let actual = super::to_melds_2(ts);
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
				ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
				ScorableHandMeld::Ankou(ts) => ts,
				_ => unreachable!(),
			};
			let mut used: Tile34MultiSet = Default::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}

			for mb in melds {
				let [t4, t5, t6] = match mb {
					ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
					ScorableHandMeld::Ankou(ts) => ts,
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
					ts.sort_unstable();
					let actual = super::to_melds_3(ts);
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
				ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
				ScorableHandMeld::Ankou(ts) => ts,
				_ => unreachable!(),
			};
			let mut used: Tile34MultiSet = Default::default();
			if used.try_extend([t1, t2, t3]).is_err() {
				continue;
			}

			for mb in melds {
				let [t4, t5, t6] = match mb {
					ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
					ScorableHandMeld::Ankou(ts) => ts,
					_ => unreachable!(),
				};
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6]).is_err() {
					continue;
				}

				for mc in melds {
					let [t7, t8, t9] = match mc {
						ScorableHandMeld::Anjun(ts) => ts.map(Into::into),
						ScorableHandMeld::Ankou(ts) => ts,
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
						ts.sort_unstable();
						let actual = super::to_melds_4(ts);
						assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
					}
				}
			}
		}
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let minjuns = h.find_minjuns(tn!(4m));

		{
			// 23506m => 5C2 = 10
			assert_eq!(minjuns.size_hint(), (0, Some(10)));
			let mut minjuns = minjuns.clone();
			assert_eq!(minjuns.next(), Some(Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 2m 3m 4m })].into())));
			assert_eq!(minjuns.size_hint(), (0, Some(9)));
			assert_eq!(minjuns.next(), Some(Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 5m })].into())));
			assert_eq!(minjuns.size_hint(), (0, Some(7)));
			assert_eq!(minjuns.next(), Some(Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 0m })].into())));
			assert_eq!(minjuns.size_hint(), (0, Some(5)));
			assert_eq!(minjuns.next(), Some(Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 5m 6m })].into())));
			assert_eq!(minjuns.size_hint(), (0, Some(1)));
			assert_eq!(minjuns.next(), Some(Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 0m 6m })].into())));
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
			assert!(minjuns.next().is_none());
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
		}

		let hs: Vec<_> = minjuns.collect();
		assert_eq!(hs, [
			Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 2m 3m 4m })].into()),
			Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 5m })].into()),
			Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 3m 4m 0m })].into()),
			Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 5m 6m })].into()),
			Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G].into(), [make_hand!(@meld { minjun 4m 0m 6m })].into()),
		]);
	}

	#[test]
	fn find_minkous() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let minkous = h.find_minkous(t!(2m));

		{
			// 22m => 2C2 = 1
			assert_eq!(minkous.len(), 1);
			let mut minkous = minkous.clone();
			assert_eq!(minkous.next(), Some(Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m].into(), [make_hand!(@meld { minkou 2m 2m 2m })].into())));
			assert_eq!(minkous.len(), 0);
			assert!(minkous.next().is_none());
			assert_eq!(minkous.len(), 0);
		}

		let hs: Vec<_> = minkous.collect();
		assert_eq!(hs, [
			Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m].into(), [make_hand!(@meld { minkou 2m 2m 2m })].into()),
		]);
	}

	#[test]
	fn find_shouminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkou E E E });
		let h = h.find_shouminkan(t!(E)).unwrap();
		assert_eq!(h, Hand(t![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m, G].into(), [make_hand!(@meld { minkan E E E E })].into()));
	}

	#[test]
	fn find_kan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		{
			let h = h.find_daiminkan(t!(E)).unwrap();
			assert_eq!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E }));
		}
		{
			let h = h.find_ankan(t!(E)).unwrap();
			assert_eq!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { ankan E E E E }));
		}
	}
}
