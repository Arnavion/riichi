use crate::{
	ArrayVec, ArrayVecIntoCombinations,
	CmpIgnoreRed,
	GameType,
	HandMeldType,
	Number, NumberTile,
	ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ScorableHandRegular, SortingNetwork,
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
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive_const(Eq, PartialEq)]
#[derive(Copy)]
pub struct Hand<const NT: usize, const NM: usize>(
	pub [Tile; NT],
	pub [HandMeld; NM],
);

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
#[derive_const(Eq, PartialEq)]
#[derive(Copy)]
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
#[derive_const(Clone, Eq, PartialEq)]
#[derive(Copy, Debug)]
pub enum HandStable {
	/// A hand containing 1 tile and 4 melds.
	One(Hand<1, 4>),

	/// A hand containing 4 tiles and 3 melds.
	Four(Hand<4, 3>),

	/// A hand containing 7 tiles and 2 melds.
	Seven(Hand<7, 2>),

	/// A hand containing 10 tiles and 1 meld.
	Ten(Hand<10, 1>),

	/// A hand containing 13 tiles.
	Thirteen(Hand<13, 0>),
}

/// A hand containing some number of tiles and melds when it's the player's turn.
/// This has an extra tile that must be discarded using [`discard`][HandTentative::discard]
/// to return to a [`HandStable`].
///
/// This enum is a way to hold all possible tentative hand types during a game.
#[derive_const(Clone, Eq, PartialEq)]
#[derive(Copy, Debug)]
pub enum HandTentative {
	/// A hand containing 2 tiles and 4 melds.
	Two(Hand<2, 4>),

	/// A hand containing 5 tiles and 3 melds.
	Five(Hand<5, 3>),

	/// A hand containing 8 tiles and 2 melds.
	Eight(Hand<8, 2>),

	/// A hand containing 11 tiles and 1 meld.
	Eleven(Hand<11, 1>),

	/// A hand containing 14 tiles.
	Fourteen(Hand<14, 0>),
}

assert_size_of!(Hand<1, 4>, 21);
assert_size_of!(Hand<2, 4>, 22);
assert_size_of!(Hand<4, 3>, 19);
assert_size_of!(Hand<5, 3>, 20);
assert_size_of!(Hand<7, 2>, 17);
assert_size_of!(Hand<8, 2>, 18);
assert_size_of!(Hand<10, 1>, 15);
assert_size_of!(Hand<11, 1>, 16);
assert_size_of!(Hand<13, 0>, 13);
assert_size_of!(Hand<14, 0>, 14);
assert_size_of!(HandMeld, 5);

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandStable: From<Self>,
{
	/// Find all possible ankans (quad via kan call on a quad held in the hand).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_ankans(self, new_tile: Tile) -> Ankans<{ NT + 1 }, NM> {
		let Self(ts, ms) = self;
		let ts = append(ts, new_tile);
		Ankans::new(Hand(ts, ms))
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NT + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<{ NT - 3 }, { NM + 1 }>> {
		let Self(ts, ms) = self;
		find_daiminkan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, append(ms, HandMeld::Minkan(m_new))))
	}

	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_shouminkans(self, new_tile: Tile) -> Shouminkans<{ NT + 1 }, NM> {
		let Self(ts, ms) = self;
		let ts = append(ts, new_tile);
		Shouminkans::new(Hand(ts, ms))
	}

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

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandTentative: From<Hand<NT, NM>>,
{
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile, and the discarded tile.
	///
	/// # Panics
	///
	/// Panics if the given index is not within bounds.
	pub fn discard(self, i: usize) -> (Hand<{ NT - 1 }, NM>, Tile) {
		let Self(ts, ms) = self;
		let t_discard = ts[i];
		let ts = unsafe { except(&ts, [i]) };
		(Hand(ts, ms), t_discard)
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl<const NT: usize, const NM: usize> const Clone for Hand<NT, NM> {
	fn clone(&self) -> Self {
		*self
	}
}

impl<const NT: usize, const NM: usize> core::fmt::Debug for Hand<NT, NM>
where
	Hand<NT, NM>: core::fmt::Display,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl<const NT: usize, const NM: usize> core::fmt::Display for Hand<NT, NM> {
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

impl Hand<1, 4> {
	/// Add the given drawn / called tile to this hand and convert it into a [`ScorableHand`] if one exists.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Returns `None` if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hand(self, new_tile: Tile) -> Option<ScorableHand> {
		let Self([t1], ms) = self;

		if t1.eq_ignore_red(&new_tile) {
			let mut ms = ms.map(Into::into);
			ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
			let [m1, m2, m3, m4] = ms;
			Some(ScorableHand::Regular(ScorableHandRegular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair: ScorableHandPair([t1, new_tile]) }))
		}
		else {
			None
		}
	}
}

impl Hand<4, 3> {
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
		Hand4ScorableHands::new(self, new_tile, tsumo_or_ron)
	}
}

#[derive(Clone, Debug)]
pub struct Hand4ScorableHands {
	pairs: ArrayAdjacentPairs<Tile, 5>,
	new_tile_i: (usize, TsumoOrRon),
	ms: [ScorableHandMeld; 3],
}

impl Hand4ScorableHands {
	fn new(Hand(ts, ms): Hand<4, 3>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		let mut ts = append(ts, new_tile);
		ts.sort_unstable();
		// Set `new_tile_i` to the last index of the tile, not the first, to be consistent with `Hand13ScorableHands`.
		let new_tile_i = ts.iter().rposition(|&t_| t_ == new_tile);
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);

		let pairs = ArrayAdjacentPairs::new(ts);

		let mut ms = ms.map(Into::into);
		ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);

		Self { pairs, new_tile_i, ms }
	}
}

impl Iterator for Hand4ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (pt1_i, [pt1, pt2], rest) = self.pairs.next()?;
			let pair = ScorableHandPair([pt1, pt2]);
			let new_tile_i = extract_new_tile_i_pair_rest(self.new_tile_i, pt1_i);
			let Some(md) = to_meld(rest, new_tile_i) else { continue; };
			break Some(ScorableHand::Regular(match md {
				ScorableHandFourthMeld::Tanki(md) => {
					let [m1, m2, m3, m4] = merge_sorted(&self.ms, &[md]);
					ScorableHandRegular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair }
				},
				m4 => ScorableHandRegular { melds: (self.ms, m4), pair },
			}));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.pairs.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Hand4ScorableHands {}

impl Hand<7, 2> {
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
		Hand7ScorableHands::new(self, new_tile, tsumo_or_ron)
	}
}

#[derive(Clone, Debug)]
pub struct Hand7ScorableHands {
	pairs: ArrayAdjacentPairs<Tile, 8>,
	mcds: Option<(ScorableHandPair, SortMelds<Melds2>)>,
	new_tile_i: (usize, TsumoOrRon),
	ms: [ScorableHandMeld; 2],
}

impl Hand7ScorableHands {
	fn new(Hand(ts, ms): Hand<7, 2>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		let mut ts = append(ts, new_tile);
		ts.sort_unstable();
		// Set `new_tile_i` to the last index of the tile, not the first, to be consistent with `Hand13ScorableHands`.
		let new_tile_i = ts.iter().rposition(|&t_| t_ == new_tile);
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);

		let pairs = ArrayAdjacentPairs::new(ts);

		let mut ms = ms.map(Into::into);
		ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);

		Self { pairs, mcds: None, new_tile_i, ms }
	}
}

impl Iterator for Hand7ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((pair, mcds)) = &mut self.mcds else {
				let (pt1_i, [pt1, pt2], rest) = self.pairs.next()?;
				let pair = ScorableHandPair([pt1, pt2]);
				let new_tile_i = extract_new_tile_i_pair_rest(self.new_tile_i, pt1_i);
				self.mcds = Some((pair, SortMelds::new2(rest, new_tile_i)));
				continue;
			};

			let Some((mc, md)) = mcds.next() else { self.mcds = None; continue; };
			let pair = *pair;
			break Some(ScorableHand::Regular(match md {
				ScorableHandFourthMeld::Tanki(md) => {
					let [m1, m2, m3, m4] = merge_sorted(&self.ms, &[mc, md]);
					ScorableHandRegular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair }
				},
				m4 => {
					let [m1, m2, m3] = merge_sorted(&self.ms, &[mc]);
					ScorableHandRegular { melds: ([m1, m2, m3], m4), pair }
				},
			}));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.pairs.size_hint() == (0, Some(0)) && let Some((_, mcds)) = &self.mcds {
			let (_, hi) = mcds.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl core::iter::FusedIterator for Hand7ScorableHands where SortMelds<Melds2>: core::iter::FusedIterator {}

impl Hand<10, 1> {
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
		Hand10ScorableHands::new(self, new_tile, tsumo_or_ron)
	}
}

#[derive(Clone, Debug)]
pub struct Hand10ScorableHands {
	pairs: ArrayAdjacentPairs<Tile, 11>,
	mbcds: Option<(ScorableHandPair, SortMelds<Melds3>)>,
	new_tile_i: (usize, TsumoOrRon),
	m: ScorableHandMeld,
}

impl Hand10ScorableHands {
	fn new(Hand(ts, ms): Hand<10, 1>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		let mut ts = append(ts, new_tile);
		ts.sort_unstable();
		// Set `new_tile_i` to the last index of the tile, not the first, to be consistent with `Hand13ScorableHands`.
		let new_tile_i = ts.iter().rposition(|&t_| t_ == new_tile);
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);

		let pairs = ArrayAdjacentPairs::new(ts);

		let [m] = ms.map(Into::into);

		Self { pairs, mbcds: None, new_tile_i, m }
	}
}

impl Iterator for Hand10ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((pair, mbcds)) = &mut self.mbcds else {
				let (pt1_i, [pt1, pt2], rest) = self.pairs.next()?;
				let pair = ScorableHandPair([pt1, pt2]);
				let new_tile_i = extract_new_tile_i_pair_rest(self.new_tile_i, pt1_i);
				self.mbcds = Some((pair, SortMelds::new3(rest, new_tile_i)));
				continue;
			};

			let Some(([mb, mc], md)) = mbcds.next() else { self.mbcds = None; continue; };
			let pair = *pair;
			break Some(ScorableHand::Regular(match md {
				ScorableHandFourthMeld::Tanki(md) => {
					let [m1, m2, m3, m4] = merge_sorted(&[self.m], &[mb, mc, md]);
					ScorableHandRegular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair }
				},
				m4 => {
					let [m1, m2, m3] = merge_sorted(&[self.m], &[mb, mc]);
					ScorableHandRegular { melds: ([m1, m2, m3], m4), pair }
				},
			}));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.pairs.size_hint() == (0, Some(0)) && let Some((_, mbcds)) = &self.mbcds {
			let (_, hi) = mbcds.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl core::iter::FusedIterator for Hand10ScorableHands where SortMelds<Melds3>: core::iter::FusedIterator {}

impl Hand<13, 0> {
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
		Hand13ScorableHands::new(self, new_tile, tsumo_or_ron)
	}
}

#[derive(Clone, Debug)]
pub struct Hand13ScorableHands {
	pairs: ArrayAdjacentPairs<Tile, 14>,
	mabcds: Option<(ScorableHandPair, SortMelds<Melds4>)>,
	new_tile_i: (usize, TsumoOrRon),
	kokushi_musou: Option<ScorableHand>,
	chiitoi: Option<ScorableHand>,
}

impl Hand13ScorableHands {
	fn new(Hand(ts, []): Hand<13, 0>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		let mut ts = append(ts, new_tile);
		ts.sort_unstable();
		// Set `new_tile_i` to the last index of the tile, not the first, so that `to_kokushi_musou` can use it to determine juusanmen-wait.
		let new_tile_i = ts.iter().rposition(|&t_| t_ == new_tile);
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);

		let pairs = ArrayAdjacentPairs::new(ts);

		let kokushi_musou = to_kokushi_musou(&ts, new_tile_i.0);
		let chiitoi = to_chiitoi(&ts);

		Self { pairs, mabcds: None, new_tile_i, kokushi_musou, chiitoi }
	}
}

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
			let Some((pair, mabcds)) = &mut self.mabcds else {
				let (pt1_i, [pt1, pt2], rest) = self.pairs.next()?;
				let pair = ScorableHandPair([pt1, pt2]);
				let new_tile_i = extract_new_tile_i_pair_rest(self.new_tile_i, pt1_i);
				self.mabcds = Some((pair, SortMelds::new4(rest, new_tile_i)));
				continue;
			};

			let Some(([m1, m2, m3], m4)) = mabcds.next() else { self.mabcds = None; continue; };
			let pair = *pair;
			break Some(ScorableHand::Regular(ScorableHandRegular { melds: ([m1, m2, m3], m4), pair }));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let lo = usize::from(self.kokushi_musou.is_some()) + usize::from(self.chiitoi.is_some());
		if self.pairs.size_hint() == (0, Some(0)) && let Some((_, mabcds)) = &self.mabcds {
			let (_, hi) = mabcds.size_hint();
			(lo, hi)
		}
		else {
			(lo, None)
		}
	}
}

impl core::iter::FusedIterator for Hand13ScorableHands where SortMelds<Melds4>: core::iter::FusedIterator {}

impl Hand<14, 0> {
	/// Find all possible ankans (quad via kan call on a quad held in the hand).
	///
	/// This is used for the special case where the dealer's starting hand can call an ankan. All other cases are handled by
	/// a stable hand type (like `Hand<13, 0>`) calling `find_ankans` at the time of drawing a new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_ankans(self) -> Ankans<14, 0> {
		Ankans::new(self)
	}

	/// Convert this hand into a set of [`ScorableHand`]s by considering each tile as a new tile.
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
		let Self(ts, ms) = self;

		ts.into_iter().enumerate()
			.flat_map(move |(i, new_tile)| {
				let ts = unsafe { except(&ts, [i]) };
				Hand(ts, ms).to_scorable_hands(new_tile, TsumoOrRon::Tsumo)
			})
	}
}

impl HandMeld {
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
		let (ts, ty, s) = Tile::parse_run_until::<4>(s, end)?;
		let ty = ty.ok_or(())?;
		Ok((match ts[..] {
			[t1, t2, t3, t4] if is_kan(t1, t2, t3, t4) => match ty {
				HandMeldType::Ankan => Self::Ankan([t1, t2, t3, t4]),
				HandMeldType::Shouminkan |
				HandMeldType::MinjunMinkouDaiminkan => Self::Minkan([t1, t2, t3, t4]),
			},

			[t1, t2, t3] if matches!(ty, HandMeldType::MinjunMinkouDaiminkan) =>
				if is_kou(t1, t2, t3) {
					Self::Minkou([t1, t2, t3])
				}
				else {
					let t1 = NumberTile::try_from(t1)?;
					let t2 = NumberTile::try_from(t2)?;
					let t3 = NumberTile::try_from(t3)?;
					let mut ts = [t1, t2, t3];
					SortingNetwork::sort_three(&mut ts);
					if is_shun(ts[0], ts[1], ts[2]) {
						Self::Minjun(ts)
					}
					else {
						return Err(());
					}
				},

			_ => return Err(()),
		}, s))
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl const Clone for HandMeld {
	fn clone(&self) -> Self {
		*self
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
		let (result, _) = Self::parse_until(s.as_ref(), None)?;
		Ok(result)
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
		match self {
			Self::One(_) => None,
			Self::Four(h) => h.find_daiminkan(new_tile).map(Self::One),
			Self::Seven(h) => h.find_daiminkan(new_tile).map(Self::Four),
			Self::Ten(h) => h.find_daiminkan(new_tile).map(Self::Seven),
			Self::Thirteen(h) => h.find_daiminkan(new_tile).map(Self::Ten),
		}
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
		let (ts, ts_type, s) = Tile::parse_run_until::<13>(s.as_ref(), Some(b' '))?;
		if ts_type.is_some() {
			return Err(());
		}

		let (h, s) = match ts[..] {
			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] => (
				Hand(
					[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13],
					[],
				).into(),
				s,
			),

			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] => {
				let (m1, s) = HandMeld::parse_until(s, None)?;
				(
					Hand(
						[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10],
						[m1],
					).into(),
					s,
				)
			},

			[t1, t2, t3, t4, t5, t6, t7] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, None)?;
				(
					Hand(
						[t1, t2, t3, t4, t5, t6, t7],
						[m1, m2],
					).into(),
					s,
				)
			},

			[t1, t2, t3, t4] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, s) = HandMeld::parse_until(s, None)?;
				(
					Hand(
						[t1, t2, t3, t4],
						[m1, m2, m3],
					).into(),
					s,
				)
			},

			[t1] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m4, s) = HandMeld::parse_until(s, None)?;
				(
					Hand(
						[t1],
						[m1, m2, m3, m4],
					).into(),
					s,
				)
			},

			_ => return Err(()),
		};
		if !s.is_empty() {
			return Err(());
		}

		Ok(h)
	}
}

impl HandTentative {
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the hand resulting from the discard of that tile, and the discarded tile.
	pub fn discard(self, i: usize) -> (HandStable, Tile) {
		match self {
			Self::Two(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Five(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Eight(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Eleven(h) => { let (h, t) = h.discard(i); (h.into(), t) },
			Self::Fourteen(h) => { let (h, t) = h.discard(i); (h.into(), t) },
		}
	}
}

macro_rules! hand_enum_from {
	($($nt:expr, $nm:expr => $ty:tt :: $variant:ident ,)*) => {
		$(
			impl const From<Hand<$nt, $nm>> for $ty {
				fn from(h: Hand<$nt, $nm>) -> Self {
					Self::$variant(h)
				}
			}
		)*
	};
}

hand_enum_from! {
	1, 4 => HandStable::One,
	2, 4 => HandTentative::Two,
	4, 3 => HandStable::Four,
	5, 3 => HandTentative::Five,
	7, 2 => HandStable::Seven,
	8, 2 => HandTentative::Eight,
	10, 1 => HandStable::Ten,
	11, 1 => HandTentative::Eleven,
	13, 0 => HandStable::Thirteen,
	14, 0 => HandTentative::Fourteen,
}

/// [`Iterator`] of [`Hand<{ NT - 4 }, { NM + 1 }>`](Hand) values formed by creating an ankan in the given hand.
#[derive(Debug)]
#[derive_const(Clone)]
pub struct Ankans<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	tiles: TileMultiSetIntoIter<Tile34MultiSetElement>,
}

impl<const NT: usize, const NM: usize> Ankans<NT, NM> {
	fn new(hand: Hand<NT, NM>) -> Self {
		let tiles: Tile34MultiSet = hand.0.into_iter().collect();
		Self {
			hand,
			tiles: tiles.into_iter(),
		}
	}
}

impl<const NT: usize, const NM: usize> Iterator for Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
{
	type Item = Hand<{ NT - 4 }, { NM + 1 }>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (t_kan, count) = self.tiles.next()?;
			if count.get() != 4 { continue; }

			let Hand(ts, ms) = self.hand;

			let mut ts_rest = ArrayVec::<_, { NT - 4 }>::new();
			let mut ts_kan = ArrayVec::<_, 4>::new();
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
			let ts_kan = unsafe { ts_kan.unwrap_unchecked() };
			break Some(Hand(ts_rest, append(ms, HandMeld::Ankan(ts_kan))));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
{}

/// [`Iterator`] of [`HandStable`] values formed by creating an ankan in the given hand.
#[derive(Debug)]
#[derive_const(Clone)]
pub enum HandAnkans {
	One,
	Four(Ankans<5, 3>),
	Seven(Ankans<8, 2>),
	Ten(Ankans<11, 1>),
	Thirteen(Ankans<14, 0>),
}

impl Iterator for HandAnkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(Into::into),
			Self::Seven(inner) => inner.next().map(Into::into),
			Self::Ten(inner) => inner.next().map(Into::into),
			Self::Thirteen(inner) => inner.next().map(Into::into),
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

fn find_daiminkan<const N: usize>(
	ts: [Tile; N],
	new_tile: Tile,
) -> Option<([Tile; N - 3], [Tile; 4])> {
	let [(i1, t1), (i2, t2), (i3, t3)] = ts.into_iter().enumerate().filter(|&(_, t)| t.eq_ignore_red(&new_tile)).next_chunk().ok()?;
	let m = [t1, t2, t3, new_tile];
	let ts = unsafe { except(&ts, [i1, i2, i3]) };
	Some((ts, m))
}

/// [`Iterator`] of [`Hand<{ NT - 1 }, NM>`](Hand) values formed by creating a shouminkan in the given hand.
#[derive_const(Clone)]
#[derive(Debug)]
pub struct Shouminkans<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	i: core::ops::Range<usize>,
}

impl<const NT: usize, const NM: usize> Shouminkans<NT, NM> {
	fn new(hand: Hand<NT, NM>) -> Self {
		let i = 0..hand.0.len();
		Self { hand, i }
	}
}

impl<const NT: usize, const NM: usize> Shouminkans<NT, NM>
where
	[(); NT - 1]:,
{
	fn next_inner(&self, i: usize) -> Option<Hand<{ NT - 1 }, NM>> {
		unsafe { core::hint::assert_unchecked(i < self.hand.0.len()); }
		let tile = self.hand.0[i];
		// Note: This modifies the meld in a copy of `self.hand`, not `self.hand` itself,
		// because every Iterator element should be a modification on top of the original hand.
		let mut melds = self.hand.1;
		for m in &mut melds {
			if let HandMeld::Minkou([t1, t2, t3]) = *m && t1.eq_ignore_red(&tile) {
				*m = HandMeld::Minkan([t1, t2, t3, tile]);
				let ts = unsafe { except(&self.hand.0, [i]) };
				return Some(Hand(ts, melds));
			}
		}
		None
	}
}

impl<const NT: usize, const NM: usize> Iterator for Shouminkans<NT, NM>
where
	[(); NT - 1]:,
{
	type Item = Hand<{ NT - 1 }, NM>;

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

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Shouminkans<NT, NM>
where
	[(); NT - 1]:,
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

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Shouminkans<NT, NM>
where
	[(); NT - 1]:,
{}

/// [`Iterator`] of [`HandStable`] values formed by creating an shouminkan in the given hand.
#[derive(Debug)]
#[derive_const(Clone)]
pub enum HandShouminkans {
	One(Shouminkans<2, 4>),
	Four(Shouminkans<5, 3>),
	Seven(Shouminkans<8, 2>),
	Ten(Shouminkans<11, 1>),
	Thirteen,
}

impl Iterator for HandShouminkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One(inner) => inner.next().map(Into::into),
			Self::Four(inner) => inner.next().map(Into::into),
			Self::Seven(inner) => inner.next().map(Into::into),
			Self::Ten(inner) => inner.next().map(Into::into),
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

impl DoubleEndedIterator for HandShouminkans {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self {
			Self::One(inner) => inner.next_back().map(Into::into),
			Self::Four(inner) => inner.next_back().map(Into::into),
			Self::Seven(inner) => inner.next_back().map(Into::into),
			Self::Ten(inner) => inner.next_back().map(Into::into),
			Self::Thirteen => None,
		}
	}
}

impl core::iter::FusedIterator for HandShouminkans {}

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minkou in the given hand using the given new tile.
/// Along with the `Hand`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae.
#[derive(Clone, Debug)]
pub struct Minkous<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	new_tile: Tile,
	combinations: ArrayVecIntoCombinations<(usize, Tile), 4>,
}

impl<const NT: usize, const NM: usize> Minkous<NT, NM> {
	fn new(hand: Hand<NT, NM>, new_tile: Tile) -> Self {
		let ts_consider: ArrayVec<_, _> = hand.0.into_iter().enumerate().filter(|&(_, t)| t.eq_ignore_red(&new_tile)).collect();
		Self {
			hand,
			new_tile,
			combinations: ts_consider.into_combinations(),
		}
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minkous<NT, NM>
where
	[(); NT - 2]:,
	[(); NM + 1]:,
{
	type Item = (Hand<{ NT - 2 }, { NM + 1 }>, ArrayVec<usize, { NT - 2 }>);

	fn next(&mut self) -> Option<Self::Item> {
		let ((i1, t1), (i2, t2)) = self.combinations.next()?;
		let ts = [t1, t2, self.new_tile];
		let m = HandMeld::Minkou(ts);
		let ts = unsafe { except(&self.hand.0, [i1, i2]) };
		let allowed_discards: ArrayVec<_, _> =
			ts.iter().enumerate()
			.filter_map(|(i, &t)| t.ne_ignore_red(&self.new_tile).then_some(i))
			.collect();
		(!allowed_discards.is_empty()).then(|| (Hand(ts, append(self.hand.1, m)), allowed_discards))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.combinations.size_hint();
		(0, hi)
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minkous<NT, NM>
where
	Self: Iterator,
{}

/// [`Iterator`] of [`HandTentative`] values formed by creating a minkou in the given hand using the given new tile.
/// Along with the `HandTentative`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae.
#[derive(Clone, Debug)]
pub enum HandMinkous {
	One,
	Four(Minkous<4, 3>),
	Seven(Minkous<7, 2>),
	Ten(Minkous<10, 1>),
	Thirteen(Minkous<13, 0>),
}

impl Iterator for HandMinkous {
	type Item = (HandTentative, ArrayVec<usize, 11>);

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
/// Indices that are not present in this list are not allowed to be discarded due to kuikae.
#[derive(Clone, Debug)]
pub struct Minjuns<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	new_tile: NumberTile,
	combinations: ArrayVecIntoCombinations<(usize, NumberTile), 8>,
}

impl<const NT: usize, const NM: usize> Minjuns<NT, NM> {
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

impl<const NT: usize, const NM: usize> Iterator for Minjuns<NT, NM>
where
	[(); NT - 2]:,
	[(); NM + 1]:,
{
	type Item = (Hand<{ NT - 2 }, { NM + 1 }>, ArrayVec<usize, { NT - 2 }>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ((i1, t1), (i2, t2)) = self.combinations.next()?;
			let [t1, t2, t3] = {
				let mut ts = [t1, t2, self.new_tile];
				SortingNetwork::sort_three(&mut ts);
				ts
			};
			if t2.is_next_in_sequence(t1) && t3.is_next_in_sequence(t2) {
				let m = HandMeld::Minjun([t1, t2, t3]);
				let ts = unsafe { except(&self.hand.0, [i1, i2]) };
				let cannot_discard_new = Tile::from(self.new_tile);
				let cannot_discard_low = if t3.eq_ignore_red(&self.new_tile) { t1.previous_in_sequence().map(Tile::from) } else { None };
				let cannot_discard_high = if t1.eq_ignore_red(&self.new_tile) { t3.next_in_sequence().map(Tile::from) } else { None };
				let allowed_discards: ArrayVec<_, _> =
					ts.iter().enumerate()
					.filter_map(|(i, &t)| (t != cannot_discard_new && Some(t) != cannot_discard_low && Some(t) != cannot_discard_high).then_some(i))
					.collect();
				if !allowed_discards.is_empty() {
					return Some((Hand(ts, append(self.hand.1, m)), allowed_discards));
				}
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.combinations.size_hint();
		(0, hi)
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minjuns<NT, NM>
where
	Self: Iterator,
{}

/// [`Iterator`] of [`HandTentative`] values formed by creating a minjun in the given hand using the given new tile.
/// Along with the `HandTentative`, the iterator element contains a list of tile indices in the resulting hand that are allowed to be discarded.
/// Indices that are not present in this list are not allowed to be discarded due to kuikae.
#[derive(Clone, Debug)]
pub enum HandMinjuns {
	One,
	Four(Minjuns<4, 3>),
	Seven(Minjuns<7, 2>),
	Ten(Minjuns<10, 1>),
	Thirteen(Minjuns<13, 0>),
}

impl Iterator for HandMinjuns {
	type Item = (HandTentative, ArrayVec<usize, 11>);

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

#[expect(clippy::large_enum_variant)]
pub enum HandScorableHands {
	One(core::option::IntoIter<ScorableHand>),
	Four(Hand4ScorableHands),
	Seven(Hand7ScorableHands),
	Ten(Hand10ScorableHands),
	Thirteen(Hand13ScorableHands),
}

impl core::fmt::Debug for HandScorableHands {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			Self::One(inner) => f.debug_tuple("One").field(inner).finish(),
			Self::Four(inner) => f.debug_tuple("Four").field(inner).finish(),
			Self::Seven(inner) => f.debug_tuple("Seven").field(inner).finish(),
			Self::Ten(inner) => f.debug_tuple("Ten").field(inner).finish(),
			Self::Thirteen(inner) => f.debug_tuple("Thirteen").field(inner).finish(),
		}
	}
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

fn append<T, const N: usize>(arr: [T; N], element: T) -> [T; N + 1] {
	let mut result = [const { core::mem::MaybeUninit::uninit() }; N + 1];
	unsafe { result.as_mut_ptr().cast::<[T; N]>().write(arr); }
	result[N].write(element);
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

/// # Safety
///
/// Every element of `i_discard` must be distinct, in sort order, and within the bounds of `ts`.
unsafe fn except<T, const N: usize, const DN: usize>(
	ts: &[T; N],
	i_discard: [usize; DN],
) -> [T; N - DN]
where
	T: Copy,
{
	let mut result = [const { core::mem::MaybeUninit::uninit() }; N - DN];

	let mut i_start = 0;
	let mut result_start = 0;
	for i_end in i_discard {
		unsafe { core::hint::assert_unchecked(i_start <= i_end); }
		unsafe { core::hint::assert_unchecked(i_end < ts.len()); }

		let result_end = result_start + (i_end - i_start);
		unsafe { core::hint::assert_unchecked(result_end <= result.len()); }

		result[result_start..result_end].write_copy_of_slice(&ts[i_start..i_end]);

		i_start = i_end + 1;
		result_start = result_end;
	}

	unsafe { core::hint::assert_unchecked(result.len() - result_start == ts.len() - i_start); }
	result[result_start..].write_copy_of_slice(&ts[i_start..]);

	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

#[derive(Clone, Debug)]
struct ArrayAdjacentPairs<T, const N: usize> {
	arr: [T; N],
	range: core::ops::Range<usize>,
}

impl<T, const N: usize> ArrayAdjacentPairs<T, N> {
	fn new(arr: [T; N]) -> Self {
		let range = 0..(arr.len().saturating_sub(1));
		Self { arr, range }
	}
}

impl<T, const N: usize> ArrayAdjacentPairs<T, N>
where
	T: CmpIgnoreRed + Copy,
	[(); N - 2]:,
{
	// # Safety
	//
	// `i` and `i + 1` must be within bounds of `self.arr`.
	unsafe fn next_inner(&mut self, i: usize) -> Option<(usize, [T; 2], [T; N - 2])> {
		unsafe { core::hint::assert_unchecked(i < self.arr.len() - 1) };

		let pt1 = self.arr[i];
		let pt2 = self.arr[i + 1];
		if pt1.ne_ignore_red(&pt2) {
			return None;
		}

		let rest = self.arr.into_iter().take(i).chain(self.arr.into_iter().skip(i + 2)).next_chunk();
		let rest = unsafe { rest.unwrap_unchecked() };

		Some((i, [pt1, pt2], rest))
	}
}

impl<T, const N: usize> Iterator for ArrayAdjacentPairs<T, N>
where
	T: CmpIgnoreRed + Copy,
	[(); N - 2 ]:,
{
	type Item = (usize, [T; 2], [T; N - 2]);

	fn next(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };

		loop {
			let i = self.range.next()?;
			if let Some(result) = unsafe { self.next_inner(i) } {
				break Some(result);
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.range.size_hint();
		(0, hi)
	}
}

impl<T, const N: usize> DoubleEndedIterator for ArrayAdjacentPairs<T, N>
where
	T: CmpIgnoreRed + Copy,
	[(); N - 2 ]:,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		unsafe { core::hint::assert_unchecked(self.range.start <= self.range.end) };

		loop {
			let i = self.range.next_back()?;
			if let Some(result) = unsafe { self.next_inner(i) } {
				break Some(result);
			}
		}
	}
}

impl<T, const N: usize> ExactSizeIterator for ArrayAdjacentPairs<T, N> where Self: Iterator {}

impl<T, const N: usize> core::iter::FusedIterator for ArrayAdjacentPairs<T, N> where Self: Iterator {}

unsafe impl<T, const N: usize> core::iter::TrustedLen for ArrayAdjacentPairs<T, N> where Self: Iterator {}

fn merge_sorted<T, const N1: usize, const N2: usize>(a_s: &[T; N1], b_s: &[T; N2]) -> [T; N1 + N2]
where
	T: Copy + core::cmp::PartialOrd,
{
	/// SAFETY: Requires `dst_s.len() == a_s.len() + b_s.len()`.
	unsafe fn merge_sorted_inner<T>(dst_s: &mut [core::mem::MaybeUninit<T>], a_s: &[T], b_s: &[T]) where T: Copy + core::cmp::PartialOrd {
		let mut a_s = a_s.iter();
		let mut b_s = b_s.iter();
		let mut a_next = a_s.next();
		let mut b_next = b_s.next();
		dst_s.write_iter(core::iter::from_fn(move || match (a_next, b_next) {
			(Some(a), Some(b)) =>
				if a < b {
					core::mem::replace(&mut a_next, a_s.next()).copied()
				}
				else {
					core::mem::replace(&mut b_next, b_s.next()).copied()
				},

			(Some(_), None) => core::mem::replace(&mut a_next, a_s.next()).copied(),

			(None, Some(_)) => core::mem::replace(&mut b_next, b_s.next()).copied(),

			// SAFETY: `dst_s.len() == a_s.len() + b_s.len()` guaranteed by caller.
			(None, None) => unsafe { core::hint::unreachable_unchecked(); },
		}));
	}

	let mut result = [const { core::mem::MaybeUninit::uninit() }; N1 + N2];
	unsafe { merge_sorted_inner(&mut result, a_s, b_s); }
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

fn is_kan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> bool {
	(t1, t2, t3).eq_ignore_red(&(t2, t3, t4))
}

fn is_kou(t1: Tile, t2: Tile, t3: Tile) -> bool {
	(t1, t2).eq_ignore_red(&(t2, t3))
}

fn is_shun(t1: NumberTile, t2: NumberTile, t3: NumberTile) -> bool {
	t1.shun_rest().eq_ignore_red(&Some((t2, t3)))
}

const fn to_kou(tiles: [Tile; 3], new_tile_i: Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld {
	if let Some((_, tsumo_or_ron)) = new_tile_i {
		ScorableHandFourthMeld::Shanpon { tiles, tsumo_or_ron }
	}
	else {
		ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(tiles))
	}
}

const fn to_shun(tiles: [NumberTile; 3], new_tile_i: Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld {
	match new_tile_i {
		None => ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun(tiles)),
		Some((0, tsumo_or_ron)) =>
			if tiles[2].number() == Number::Nine {
				ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron }
			}
			else {
				ScorableHandFourthMeld::RyanmenLow { tiles, tsumo_or_ron }
			},
		Some((1, tsumo_or_ron)) => ScorableHandFourthMeld::Kanchan { tiles, tsumo_or_ron },
		Some((2, tsumo_or_ron)) =>
			if tiles[0].number() == Number::One {
				ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron }
			}
			else {
				ScorableHandFourthMeld::RyanmenHigh { tiles, tsumo_or_ron }
			},
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn extract_new_tile_i_pair_rest(
	new_tile_i: (usize, TsumoOrRon),
	pt1_i: usize,
) -> Option<(usize, TsumoOrRon)> {
	if new_tile_i.0 < pt1_i { Some(new_tile_i) }
	else if new_tile_i.0 > pt1_i + 1 { Some((new_tile_i.0 - 2, new_tile_i.1)) }
	else { None }
}

fn to_meld([t1, t2, t3]: [Tile; 3], new_tile_i: Option<(usize, TsumoOrRon)>) -> Option<ScorableHandFourthMeld> {
	if is_kou(t1, t2, t3) {
		Some(to_kou([t1, t2, t3], new_tile_i))
	}
	else if
		let Ok(t1) = NumberTile::try_from(t1) &&
		let Ok(t2) = NumberTile::try_from(t2) &&
		let Ok(t3) = NumberTile::try_from(t3) &&
		is_shun(t1, t2, t3)
	{
		Some(to_shun([t1, t2, t3], new_tile_i))
	}
	else {
		None
	}
}

/// Finds a meld from the given tiles.
///
/// When `N == 3`, using `to_meld` is more efficient.
type Melds1AndRest<const N: usize> = core::array::IntoIter<(ScorableHandFourthMeld, [Tile; N - 3], Option<(usize, TsumoOrRon)>), 4>;

fn to_meld_and_rest<const N: usize>(ts: [Tile; N], new_tile_i: Option<(usize, TsumoOrRon)>) -> Melds1AndRest<N>
where
	[(); N - 3]:,
{
	fn to_meld_and_rest_inner<const N: usize, T>(
		ts: [Tile; N],
		new_tile_i: Option<(usize, TsumoOrRon)>,
		t1: T,
		t1_is_new: bool,
		t2_expected: T,
		t3_expected: T,
		mut t_f: impl FnMut(Tile) -> Result<T, ()>,
		mut meld_f: impl FnMut([T; 3], Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld,
	) -> [Option<(ScorableHandFourthMeld, [Tile; N - 3], Option<(usize, TsumoOrRon)>)>; 2]
	where
		T: CmpIgnoreRed + Copy,
	{
		let mut non_tanki_and_rest = None;
		let mut tanki_and_rest = None;

		// If t1 is an old tile, we only need one t2 that is an old tile and one t2 that is a new tile.
		// If t1 is a new tile, then we only need one t2 that is an old tile.
		let mut t2_old = None;
		let mut t2_new = None;
		for (i2, &t2) in ts[1..(N - 1)].iter().enumerate() {
			let Ok(t2) = t_f(t2) else { continue; };
			if t2.ne_ignore_red(&t2_expected) { continue; }
			let i2 = 1 + i2;
			let t2_is_new = matches!(new_tile_i, Some((i, _)) if i == i2);
			if t2_old.is_none() && !t2_is_new {
				t2_old = Some((i2, t2, false));
			}
			if t2_new.is_none() && t2_is_new {
				t2_new = Some((i2, t2, true));
			}
			if t2_old.is_some() && (t1_is_new || t2_new.is_some()) {
				break;
			}
		}
		'outer: for (i2, t2, t2_is_new) in t2_old.into_iter().chain(t2_new) {
			unsafe { core::hint::assert_unchecked(1 + i2 < N); }

			// If t1 and t2 are old tiles, we only need one t3 that is an old tile and one t3 that is a new tile.
			// If either t1 or t2 is a new tile, then we only need one t3 that is an old tile.
			let mut t3_old = None;
			let mut t3_new = None;
			for (i3, &t3) in ts[(1 + i2)..].iter().enumerate() {
				let Ok(t3) = t_f(t3) else { continue; };
				if t3.ne_ignore_red(&t3_expected) { continue; }
				let i3 = 1 + i2 + i3;
				let t3_is_new = matches!(new_tile_i, Some((i, _)) if i == i3);
				if t3_old.is_none() && !t3_is_new {
					t3_old = Some((i3, t3));
				}
				if t3_new.is_none() && t3_is_new {
					t3_new = Some((i3, t3));
				}
				if t3_old.is_some() && (t1_is_new || t2_is_new || t3_new.is_some()) {
					break;
				}
			}

			for (i3, t3) in t3_old.into_iter().chain(t3_new) {
				let (new_tile_i_this, new_tile_i_rest) = extract_new_tile_i(new_tile_i, i2, i3);
				let meld = meld_f([t1, t2, t3], new_tile_i_this);
				let result = if matches!(meld, ScorableHandFourthMeld::Tanki(_)) { &mut tanki_and_rest } else { &mut non_tanki_and_rest };
				if result.is_none() {
					let rest = unsafe { except(&ts, [0, i2, i3]) };
					*result = Some((meld, rest, new_tile_i_rest));
					if (t1_is_new || tanki_and_rest.is_some()) && non_tanki_and_rest.is_some() {
						break 'outer;
					}
				}
			}
		}

		[non_tanki_and_rest, tanki_and_rest]
	}

	fn extract_new_tile_i(
		new_tile_i: Option<(usize, TsumoOrRon)>,
		i2: usize,
		i3: usize,
	) -> (Option<(usize, TsumoOrRon)>, Option<(usize, TsumoOrRon)>) {
		if let Some((i, tsumo_or_ron)) = new_tile_i {
			// Micro-optimization: Doing it this way generates only one branch for the outer `if let Some() = new_tile_i` check;
			// the implementation of that arm is itself branchless and uses no stack.
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
		else {
			(None, None)
		}
	}

	let t1 = ts[0];
	let t1_is_new = matches!(new_tile_i, Some((0, _)));

	// There are at most two unique kous:
	//
	// - Any kous that use the new tile will be formed as `ScorableHandFourthMeld::Shanpon`, and we only need one of them.
	//
	// - Any kous that don't use the new tile will be formed as `ScorableHandFourthMeld::Tanki`, and we only need one of them.
	//
	// If t1 is the new tile, then only the `ScorableHandFourthMeld::Shanpon` will be found so we don't need to look for the `ScorableHandFourthMeld::Tanki`.
	let [kou_non_tanki_and_rest, kou_tanki_and_rest] = to_meld_and_rest_inner(ts, new_tile_i, t1, t1_is_new, t1, t1, Ok, to_kou);

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
	let [shun_non_tanki_and_rest, shun_tanki_and_rest] =
		if
			let Ok(t1) = NumberTile::try_from(t1) &&
			let Some((t2_expected, t3_expected)) = t1.shun_rest()
		{
			to_meld_and_rest_inner(ts, new_tile_i, t1, t1_is_new, t2_expected, t3_expected, NumberTile::try_from, to_shun)
		}
		else {
			[None, None]
		};

	let inner: ArrayVec<_, 4> = [
		kou_non_tanki_and_rest,
		kou_tanki_and_rest,
		shun_non_tanki_and_rest,
		shun_tanki_and_rest,
	].into_iter().flatten().collect();
	inner.into_iter()
}

/// Finds two melds from the given six tiles.
#[derive(Clone, Debug)]
struct Melds2 {
	mas: Dedup<Melds1AndRest<6>>,
}

impl Melds2 {
	fn new(ts: [Tile; 6], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mas = Dedup::new(to_meld_and_rest(ts, new_tile_i));
		Self { mas }
	}
}

impl Iterator for Melds2 {
	type Item = [ScorableHandFourthMeld; 2];

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, ts, new_tile_i) = self.mas.next()?;
			let Some(mb) = to_meld(ts, new_tile_i) else { continue; };
			break Some(if mb >= ma { [ma, mb] } else { [mb, ma] });
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.mas.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Melds2 where Dedup<Melds1AndRest<6>>: core::iter::FusedIterator {}

/// Finds two melds from the given tiles.
///
/// When `N == 6`, using `Melds2` is more efficient.
#[derive(Clone, Debug)]
struct Melds2AndRest<const N: usize>
where
	Melds1AndRest<{ N - 3 }>:,
{
	mas: Dedup<Melds1AndRest<N>>,
	current: Option<(ScorableHandFourthMeld, Melds1AndRest<{ N - 3 }>)>,
}

impl<const N: usize> Melds2AndRest<N>
where
	Melds1AndRest<{ N - 3 }>:,
{
	fn new(ts: [Tile; N], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mas = Dedup::new(to_meld_and_rest(ts, new_tile_i));
		Self { mas, current: None }
	}
}

impl<const N: usize> Iterator for Melds2AndRest<N>
where
	Melds1AndRest<{ N - 3 }>: Iterator<Item = (ScorableHandFourthMeld, [Tile; (N - 3) - 3], Option<(usize, TsumoOrRon)>)>,
{
	type Item = ([ScorableHandFourthMeld; 2], [Tile; (N - 3) - 3], Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ma, current)) = &mut self.current else {
				let (ma, ts, new_tile_i) = self.mas.next()?;
				let current = to_meld_and_rest(ts, new_tile_i);
				self.current = Some((ma, current));
				continue;
			};

			let Some((mb, ts, new_tile_i)) = current.next() else { self.current = None; continue; };
			let ma = *ma;
			let ms = if mb >= ma { [ma, mb] } else { [mb, ma] };
			break Some((ms, ts, new_tile_i));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.mas.size_hint() == (0, Some(0)) && let Some((_, current)) = &self.current {
			let (_, hi) = current.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl<const N: usize> core::iter::FusedIterator for Melds2AndRest<N>
where
	Self: Iterator,
	Dedup<Melds1AndRest<N>>: core::iter::FusedIterator,
	Melds1AndRest<{ N - 3 }>: core::iter::FusedIterator,
{}

/// Finds three melds from the given nine tiles.
#[derive(Clone, Debug)]
struct Melds3 {
	mabs: Dedup<Melds2AndRest<9>>,
}

impl Melds3 {
	fn new(ts: [Tile; 9], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabs = Dedup::new(Melds2AndRest::new(ts, new_tile_i));
		Self { mabs }
	}
}

impl Iterator for Melds3 {
	type Item = [ScorableHandFourthMeld; 3];

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ([ma, mb], ts, new_tile_i) = self.mabs.next()?;
			let Some(mc) = to_meld(ts, new_tile_i) else { continue; };
			break Some(
				if mc >= mb { [ma, mb, mc] }
				else if mc >= ma { [ma, mc, mb] }
				else { [mc, ma, mb] }
			);
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.mabs.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Melds3 where Dedup<Melds2AndRest<9>>: core::iter::FusedIterator {}

/// Finds three melds from the given tiles.
///
/// When `N == 9`, using `Melds3` is more efficient.
#[derive(Clone, Debug)]
struct Melds3AndRest<const N: usize>
where
	Melds1AndRest<{ (N - 3) - 3 }>:,
{
	mabs: Dedup<Melds2AndRest<N>>,
	current: Option<([ScorableHandFourthMeld; 2], Melds1AndRest<{ (N - 3) - 3 }>)>,
}

impl<const N: usize> Melds3AndRest<N>
where
	Melds1AndRest<{ (N - 3) - 3 }>:,
{
	fn new(ts: [Tile; N], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabs = Dedup::new(Melds2AndRest::new(ts, new_tile_i));
		Self { mabs, current: None }
	}
}

impl<const N: usize> Iterator for Melds3AndRest<N>
where
	Melds1AndRest<{ (N - 3) - 3 }>: Iterator<Item = (ScorableHandFourthMeld, [Tile; ((N - 3) - 3) - 3], Option<(usize, TsumoOrRon)>)>,
{
	type Item = ([ScorableHandFourthMeld; 3], [Tile; ((N - 3) - 3) - 3], Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some(([ma, mb], current)) = &mut self.current else {
				let (mab, ts, new_tile_i) = self.mabs.next()?;
				let current = to_meld_and_rest(ts, new_tile_i);
				self.current = Some((mab, current));
				continue;
			};

			let Some((mc, ts, new_tile_i)) = current.next() else { self.current = None; continue; };
			let ma = *ma;
			let mb = *mb;
			let ms =
				if mc >= mb { [ma, mb, mc] }
				else if mc >= ma { [ma, mc, mb] }
				else { [mc, ma, mb] };
			break Some((ms, ts, new_tile_i));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.mabs.size_hint() == (0, Some(0)) && let Some((_, current)) = &self.current {
			let (_, hi) = current.size_hint();
			(0, hi)
		}
		else {
			(0, None)
		}
	}
}

impl<const N: usize> core::iter::FusedIterator for Melds3AndRest<N>
where
	Self: Iterator,
	Dedup<Melds2AndRest<N>>: core::iter::FusedIterator,
	Melds1AndRest<{ (N - 3) - 3 }>: core::iter::FusedIterator,
{}

/// Finds four melds from the given twelve tiles.
#[derive(Clone, Debug)]
struct Melds4 {
	mabcs: Dedup<Melds3AndRest<12>>,
}

impl Melds4 {
	fn new(ts: [Tile; 12], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabcs = Dedup::new(Melds3AndRest::new(ts, new_tile_i));
		Self { mabcs }
	}
}

impl Iterator for Melds4 {
	type Item = [ScorableHandFourthMeld; 4];

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ([ma, mb, mc], ts, new_tile_i) = self.mabcs.next()?;
			let Some(md) = to_meld(ts, new_tile_i) else { continue; };
			break Some(
				if md >= mc { [ma, mb, mc, md] }
				else if md >= mb { [ma, mb, md, mc] }
				else if md >= ma { [ma, md, mb, mc] }
				else { [md, ma, mb, mc] }
			);
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.mabcs.size_hint();
		(0, hi)
	}
}

impl core::iter::FusedIterator for Melds4 where Dedup<Melds3AndRest<12>>: core::iter::FusedIterator {}

struct SortMelds<I> where I: Iterator {
	ms: Dedup<I>,
}

impl<I> const Clone for SortMelds<I> where I: Iterator, Dedup<I>: [const] Clone {
	fn clone(&self) -> Self {
		Self { ms: self.ms.clone() }
	}
}

impl<I> core::fmt::Debug for SortMelds<I> where I: Iterator, Dedup<I>: core::fmt::Debug {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("SortMelds").field("ms", &self.ms).finish()
	}
}

impl SortMelds<Melds2> {
	fn new2(ts: [Tile; 6], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let ms = Dedup::new(Melds2::new(ts, new_tile_i));
		Self { ms }
	}
}

impl Iterator for SortMelds<Melds2> {
	type Item = (ScorableHandMeld, ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		self.ms.next().map(|mab| match mab {
			[ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb)] =>
				(ma, ScorableHandFourthMeld::Tanki(mb)),

			[m4, ScorableHandFourthMeld::Tanki(m3)] |
			[ScorableHandFourthMeld::Tanki(m3), m4] =>
				(m3, m4),

			// At most one meld can be non-tanki
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.ms.size_hint()
	}
}

impl SortMelds<Melds3> {
	fn new3(ts: [Tile; 9], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let ms = Dedup::new(Melds3::new(ts, new_tile_i));
		Self { ms }
	}
}

impl Iterator for SortMelds<Melds3> {
	type Item = ([ScorableHandMeld; 2], ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		self.ms.next().map(|mabc| match mabc {
			[ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), ScorableHandFourthMeld::Tanki(m4)] =>
				([m2, m3], ScorableHandFourthMeld::Tanki(m4)),

			[m4, ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3)] |
			[ScorableHandFourthMeld::Tanki(m2), m4, ScorableHandFourthMeld::Tanki(m3)] |
			[ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), m4] =>
				([m2, m3], m4),

			// At most one meld can be non-tanki
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.ms.size_hint()
	}
}

impl SortMelds<Melds4> {
	fn new4(ts: [Tile; 12], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let ms = Dedup::new(Melds4::new(ts, new_tile_i));
		Self { ms }
	}
}

impl Iterator for SortMelds<Melds4> {
	type Item = ([ScorableHandMeld; 3], ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		self.ms.next().map(|mabcd| match mabcd {
			[ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), ScorableHandFourthMeld::Tanki(m4)] =>
				([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)),

			[m4, ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3)] |
			[ScorableHandFourthMeld::Tanki(m1), m4, ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3)] |
			[ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), m4, ScorableHandFourthMeld::Tanki(m3)] |
			[ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m3), m4] =>
				([m1, m2, m3], m4),

			// At most one meld can be non-tanki
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.ms.size_hint()
	}
}

impl<I> core::iter::FusedIterator for SortMelds<I> where Self: Iterator, I: Iterator, Dedup<I>: core::iter::FusedIterator {}

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

/// `new_tile_i` must be set to the index of the last occurrence of the new tile.
/// Eg if the hand is `119m19p19s1234567z`, `new_tile_i` must be set to `1`, not `0`.
#[expect(clippy::unusual_byte_groupings)]
fn to_kokushi_musou(tiles: &[Tile; 14], new_tile_i: usize) -> Option<ScorableHand> {
	let (counts, was_juusanmen_wait) =
		tiles.iter().enumerate()
		// Micro-optimization: LSB of `counts` represents valid (0) or invalid (1). This is done instead of wrapping the tuple in `Option` to save space, and because we want to
		// have a defined number of iterations instead of short-circuiting using `try_fold`.
		.fold((0b000_0000_00_00_00_0_usize, false), |(counts, was_juusanmen_wait), (i, &t)| {
			// Micro-optimization: Avoid a LUT by constructing the offset from the individual bits. Same trick as `Tile::is_simple`.
			//
			//  t | t >> 1 | offset
			// ===+========+========
			// 1m |    0   | 0001
			// 2m |    1   | 0000
			// 3m |    2   | 0000
			// 4m |    3   | 0000
			// 5m |    4   | 0000
			// 6m |    5   | 0000
			// 7m |    6   | 0000
			// 8m |    7   | 0000
			// 9m |    8   | 0010
			// 1p |    9   | 0011
			// 2p |   10   | 0000
			// 3p |   11   | 0000
			// 4p |   12   | 0000
			// 5p |   13   | 0000
			// 6p |   14   | 0000
			// 7p |   15   | 0000
			// 8p |   16   | 0000
			// 9p |   17   | 0100
			// 1s |   18   | 0101
			// 2s |   19   | 0000
			// 3s |   20   | 0000
			// 4s |   21   | 0000
			// 5s |   22   | 0000
			// 6s |   23   | 0000
			// 7s |   24   | 0000
			// 8s |   25   | 0000
			// 9s |   26   | 0110
			// E  |   27   | 0111
			// S  |   28   | 1000
			// W  |   29   | 1001
			// N  |   30   | 1010
			// Wh |   31   | 1011
			// G  |   32   | 1100
			// R  |   33   | 1101
			let offset = {
				let offset_3 = u8::from(t >= t!(S)) << 3;
				let t = t as usize >> 1;
				let mask = 0b1_u64 << t;
				// let offset_2 = u8::from(matches!(t, 17 | 18 | 26 | 27 | 32 | 33)) << 2;
				let offset_2 = u8::from(0b11_0000_1100_0000_0110_0000_0000_0000_0000_u64 & mask != 0) << 2;
				// let offset_1 = u8::from(matches!(t, 8 | 9 | 26 | 27 | 30 | 31)) << 1;
				let offset_1 = u8::from(0b00_1100_1100_0000_0000_0000_0011_0000_0000_u64 & mask != 0) << 1;
				// let offset_0 = u8::from(matches!(t, 0 | 9 | 18 | 27 | 29 | 31 | 33));
				let offset_0 = u8::from(0b10_1010_1000_0000_0100_0000_0010_0000_0001_u64 & mask != 0);
				offset_3 | offset_2 | offset_1 | offset_0
			};

			let mask = 0b1 << offset;
			let was_juusanmen_wait = (i == new_tile_i && counts & mask != 0) | was_juusanmen_wait;
			let counts = counts | mask;
			(counts, was_juusanmen_wait)
		});
	(counts == 0b111_1111_11_11_11_0).then_some(ScorableHand::KokushiMusou { tiles: *tiles, was_juusanmen_wait })
}

fn to_chiitoi(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14]: &[Tile; 14]) -> Option<ScorableHand> {
	let is_chiitoi =
		(t1, t3, t5, t7, t9, t11, t13).eq_ignore_red(&(t2, t4, t6, t8, t10, t12, t14)) &&
		t2.ne_ignore_red(&t3) &&
		t4.ne_ignore_red(&t5) &&
		t6.ne_ignore_red(&t7) &&
		t8.ne_ignore_red(&t9) &&
		t10.ne_ignore_red(&t11) &&
		t12.ne_ignore_red(&t13);
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

#[cfg(test)]
#[coverage(off)]
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
		match meld {
			ScorableHandFourthMeld::Tanki(m) => match m {
				ScorableHandMeld::Ankou([t1, t2, t3]) => [(t1, None), (t2, None), (t3, None)],
				ScorableHandMeld::Anjun([t1, t2, t3]) => [(t1.into(), None), (t2.into(), None), (t3.into(), None)],
				_ => unreachable!(),
			},
			ScorableHandFourthMeld::Shanpon { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1, None), (t2, None), (t3, Some(tsumo_or_ron))],
			ScorableHandFourthMeld::Kanchan { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), None), (t2.into(), Some(tsumo_or_ron)), (t3.into(), None)],
			ScorableHandFourthMeld::Penchan { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), matches!(t1, tn!(7m | 7p | 7s)).then_some(tsumo_or_ron)), (t2.into(), None), (t3.into(), matches!(t3, tn!(3m | 3p | 3s)).then_some(tsumo_or_ron))],
			ScorableHandFourthMeld::RyanmenLow { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), Some(tsumo_or_ron)), (t2.into(), None), (t3.into(), None)],
			ScorableHandFourthMeld::RyanmenHigh { tiles: [t1, t2, t3], tsumo_or_ron } => [(t1.into(), None), (t2.into(), None), (t3.into(), Some(tsumo_or_ron))],
		}
	}

	#[test]
	fn to_meld() {
		for expected in melds_last() {
			let [(t1, t1tr), (t2, t2tr), (t3, t3tr)] = to_ttrs(expected);

			let mut ts = [(t1, t1tr), (t2, t2tr), (t3, t3tr)];
			ts.sort_unstable();
			let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));
			let ts = ts.map(|(t, _)| t);

			let actual = super::to_meld(ts, new_tile_i);
			assert_eq!(actual, Some(expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
		}

		// 124 -> X
		assert_eq!(super::to_meld([t!(1s), t!(2s), t!(4s)], None), None);
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
						ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
						let [m3, m4] = ms;
						(m3, ScorableHandFourthMeld::Tanki(m4))
					}
					else {
						(ma, mb)
					};

				let mut ts = [(t1, None), (t2, None), (t3, None), (t4, t4tr), (t5, t5tr), (t6, t6tr)];
				ts.sort_unstable();
				let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));
				let ts = ts.map(|(t, _)| t);

				let actual: std::vec::Vec<_> = super::SortMelds::new2(ts, new_tile_i).collect();
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
							ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
							let [m2, m3, m4] = ms;
							([m2, m3], ScorableHandFourthMeld::Tanki(m4))
						}
						else {
							let mut ms = [ma, mb];
							ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
							let [m2, m3] = ms;
							([m2, m3], mc)
						};

					let mut ts = [(t1, None), (t2, None), (t3, None), (t4, None), (t5, None), (t6, None), (t7, t7tr), (t8, t8tr), (t9, t9tr)];
					ts.sort_unstable();
					let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));
					let ts = ts.map(|(t, _)| t);

					let actual: std::vec::Vec<_> = super::SortMelds::new3(ts, new_tile_i).collect();
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
								ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
								let [m1, m2, m3, m4] = ms;
								([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
							}
							else {
								let mut ms = [ma, mb, mc];
								ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
								let [m1, m2, m3] = ms;
								([m1, m2, m3], md)
							};

						let mut ts = [(t1, None), (t2, None), (t3, None), (t4, None), (t5, None), (t6, None), (t7, None), (t8, None), (t9, None), (t10, t10tr), (t11, t11tr), (t12, t12tr)];
						ts.sort_unstable();
						let new_tile_i = ts.iter().enumerate().find_map(|(i, (_, tr))| tr.map(|tsumo_or_ron| (i, tsumo_or_ron)));
						let ts = ts.map(|(t, _)| t);

						let actual: std::vec::Vec<_> = super::SortMelds::new4(ts, new_tile_i).collect();
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
		assert!(matches!(ankans.next().unwrap(), make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { ankan E E E E })));
		assert_eq!(ankans.next(), None);
	}

	#[test]
	fn find_daiminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		let h = h.find_daiminkan(t!(E)).unwrap();
		assert!(matches!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E })));
	}

	#[test]
	fn find_shouminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkou E E E });
		let mut shouminkans = h.find_shouminkans(t!(E));
		assert!(matches!(shouminkans.next().unwrap(), Hand(t![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m, G], [make_hand!(@meld { minkan E E E E })])));
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
			assert!(matches!(minkous.next(), Some((Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m], [make_hand!(@meld { minkou 2m 2m 2m })]), allowed_discards)) if allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minkous.size_hint(), (0, Some(0)));
			assert!(minkous.next().is_none());
			assert_eq!(minkous.size_hint(), (0, Some(0)));
		}

		let hs: std::vec::Vec<_> = minkous.collect();
		assert!(matches!(
			&hs[..],
			[
				(Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m], [make_hand!(@meld { minkou 2m 2m 2m })]), allowed_discards),
			] if
				*allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		));
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let minjuns = h.find_minjuns(tn!(4m));

		{
			// 23506m => 5C2 = 10
			assert_eq!(minjuns.size_hint(), (0, Some(10)));
			let mut minjuns = minjuns.clone();
			assert!(matches!(minjuns.next(), Some((Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 2m 3m 4m })]), allowed_discards)) if allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(9)));
			assert!(matches!(minjuns.next(), Some((Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 5m })]), allowed_discards)) if allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(5)));
			assert!(matches!(minjuns.next(), Some((Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 0m })]), allowed_discards)) if allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(4)));
			assert!(matches!(minjuns.next(), Some((Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 5m 6m })]), allowed_discards)) if allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(1)));
			assert!(matches!(minjuns.next(), Some((Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 0m 6m })]), allowed_discards)) if allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
			assert!(minjuns.next().is_none());
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
		}

		let hs: std::vec::Vec<_> = minjuns.collect();
		assert!(matches!(
			&hs[..],
			[
				(Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 2m 3m 4m })]), allowed_discards1),
				(Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 5m })]), allowed_discards2),
				(Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 0m })]), allowed_discards3),
				(Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 5m 6m })]), allowed_discards4),
				(Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 0m 6m })]), allowed_discards5),
			] if
				*allowed_discards1 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] &&
				*allowed_discards2 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] &&
				*allowed_discards3 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] &&
				*allowed_discards4 == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10] &&
				*allowed_discards5 == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]
		));
	}

	#[test]
	fn kuikae() {
		{
			let h = make_hand!(1m 1m 1m E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minkous(t!(1m)).collect();
			for (h, allowed_discards) in hs {
				assert!(matches!(h, Hand(t![1m, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minkou 1m 1m 1m })])));
				assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
			}
		}

		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(2p)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert!(matches!(h, Hand(t![2p, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 1p 2p 3p })])));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1s)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert!(matches!(h, Hand(t![1s, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 1s 2s 3s })])));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1s)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert!(matches!(h, Hand(t![1s, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 1s 2s 3s })])));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(4m)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert!(matches!(h, Hand(t![1m, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 2m 3m 4m })])));
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
			assert!(matches!(
				&hs[..],
				[
					(Hand(t![1m, 4m, 5m, 6m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 2m 3m 4m })]), allowed_discards1),
					(Hand(t![1m, 2m, 4m, 6m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 3m 4m 5m })]), allowed_discards2),
					(Hand(t![1m, 2m, 3m, 4m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 4m 5m 6m })]), allowed_discards3),
				] if
					*allowed_discards1 == [2, 3, 4, 5, 6, 7, 8, 9, 10] &&
					*allowed_discards2 == [0, 1, 3, 4, 5, 6, 7, 8, 9, 10] &&
					*allowed_discards3 == [0, 1, 2, 4, 5, 6, 7, 8, 9, 10]
			));
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(7m)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert!(matches!(h, Hand(t![1m, 2m, 3m, 4m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 5m 6m 7m })])));
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
