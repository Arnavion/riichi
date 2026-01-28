use crate::{
	ArrayVec, ArrayVecIntoCombinations,
	CmpIgnoreRed,
	GameType,
	HandMeldType,
	NumberTile,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandMeldSortCriteria, ScorableHandPair, ScorableHandRegular,
	ShunLowNumber, ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
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
#[derive(Copy)]
#[derive_const(Eq, PartialEq)]
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
#[derive(Copy)]
#[derive_const(Eq, PartialEq)]
pub enum HandMeld {
	/// Closed quad formed by kan.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Ankan(Tile),

	/// Open quad formed by kan.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkan(Tile),

	/// Open triplet formed by pon.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkou(Tile),

	/// Open sequence formed by chii.
	Minjun(ShunLowTileAndHasFiveRed),
}

/// A hand containing some number of tiles and melds when it's not the player's turn.
///
/// This enum is a way to hold all possible stable hand types during a game.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
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
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
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

assert_size_of!(Hand<1, 4>, 9);
assert_size_of!(Hand<2, 4>, 10);
assert_size_of!(Hand<4, 3>, 10);
assert_size_of!(Hand<5, 3>, 11);
assert_size_of!(Hand<7, 2>, 11);
assert_size_of!(Hand<8, 2>, 12);
assert_size_of!(Hand<10, 1>, 12);
assert_size_of!(Hand<11, 1>, 13);
assert_size_of!(Hand<13, 0>, 13);
assert_size_of!(Hand<14, 0>, 14);
assert_size_of!(HandMeld, 2);

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
		find_daiminkan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, append(ms, m_new)))
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

		let pair = ScorableHandPair::new(t1, new_tile)?;
		let [ma, mb, mc, md] = ms.map(Into::into);
		Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, ScorableHandFourthMeld::Tanki(md), pair)))
	}

	/// Returns the [`Tile`] that would complete this hand.
	pub fn tenpai(self) -> Tile {
		// Note that tiles contained in `self` are *not* ignored, even if `self` contains all extant copies of the tile.
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447

		let Self([t1], _) = self;
		t1.remove_red()
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
		let Self(ts, ms) = self;

		let mut ts = append(ts, new_tile);
		SortingNetwork::sort(&mut ts);
		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		let [ma, mb, mc] = ms.map(Into::into);

		Hand4ScorableHands { pairs, ma, mb, mc }
	}

	/// Returns an `Iterator` of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
	pub fn tenpai(self, game_type: GameType) -> Hand4Tenpai {
		// Note that tiles contained in `self` are *not* ignored, even if `self` contains all extant copies of the tile.
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447

		let tiles = Tile::each(game_type).iter();
		let Self(mut ts, _) = self;
		SortingNetwork::sort(&mut ts);
		Hand4Tenpai { tiles, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand4ScorableHands {
	pairs: ScorableHandPairs<5>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
	mc: ScorableHandMeld,
}

assert_size_of!(Hand4ScorableHands, 48);

impl Iterator for Hand4ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (pair, [t1, t2, t3], new_tile_i) = self.pairs.next()?;
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
	ts: [Tile; 4],
}

assert_size_of!(Hand4Tenpai, 24);

impl Iterator for Hand4Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			let ts = insert_sorted(&self.ts, new_tile);
			let new_tile_i = ts.iter().position(|&t| t == new_tile);
			// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
			let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, TsumoOrRon::Tsumo);
			let pairs = ScorableHandPairs::new(ts, new_tile_i);
			for (_, [t1, t2, t3], new_tile_i) in pairs {
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
		let Self(ts, ms) = self;

		let mut ts = append(ts, new_tile);
		ts.sort_unstable();
		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		let [ma, mb] = ms.map(Into::into);

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
		// Note that tiles contained in `self` are *not* ignored, even if `self` contains all extant copies of the tile.
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447

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
	pairs: ScorableHandPairs<8>,
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
	ts: [Tile; 7],
}

assert_size_of!(Hand7Tenpai, 24);

impl Iterator for Hand7Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
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
		let Self(ts, ms) = self;

		let mut ts = append(ts, new_tile);
		ts.sort_unstable();
		let new_tile_i = ts.iter().position(|&t| t == new_tile);
		// SAFETY: `new_tile` was just inserted into `ts` so it must be found.
		let new_tile_i = (unsafe { new_tile_i.unwrap_unchecked() }, tsumo_or_ron);
		let pairs = ScorableHandPairs::new(ts, new_tile_i);

		let [ma] = ms.map(Into::into);

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
		// Note that tiles contained in `self` are *not* ignored, even if `self` contains all extant copies of the tile.
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447

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
	pairs: ScorableHandPairs<11>,
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
	ts: [Tile; 10],
}

assert_size_of!(Hand10Tenpai, 32);

impl Iterator for Hand10Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
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
		let Self(ts, []) = self;

		let kokushi_musou = LookupKokushiMusou::new(&ts).with_new_tile(new_tile);

		let mut ts = append(ts, new_tile);
		ts.sort_unstable();

		let chiitoi = to_chiitoi(&ts);

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
		// Note that tiles contained in `self` are *not* ignored, even if `self` contains all extant copies of the tile.
		// This matches the behavior of Mahjong Soul and apparently multiple other online clients.
		//
		// Ref:
		//
		// - https://old.reddit.com/r/mahjongsoul/comments/1jp59t1/where_the_heck_am_i_supposed_to_get_a_5th_8_from/
		//
		// - https://mahjongsoul.game.yo-star.com/?paipu=190508-4ebd32bc-71a5-4f4f-86a7-16066dfdc896_a925124703 ( https://riichi.wiki/index.php?title=File:Keishiki_ankan.png&oldid=20048 )
		//   from https://riichi.wiki/index.php?title=Karaten&oldid=27447

		let tiles = Tile::each(game_type).iter();
		let Self(mut ts, _) = self;
		let kokushi_musou = LookupKokushiMusou::new(&ts);
		ts.sort_unstable();
		Hand13Tenpai { tiles, kokushi_musou, ts }
	}
}

#[derive(Clone, Debug)]
pub struct Hand13ScorableHands {
	pair: Option<ScorableHandPair>,
	mabcds: Dedup<Melds4>,
	pairs: ScorableHandPairs<14>,
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

			break Some(ScorableHand::Regular(ScorableHandRegular { melds: ([m1, m2, m3], m4), pair }));
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
	kokushi_musou: LookupKokushiMusou,
	ts: [Tile; 13],
}

assert_size_of!(Hand13Tenpai, 48);

impl Iterator for Hand13Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;

			if self.kokushi_musou.clone().with_new_tile(new_tile).is_some() {
				return Some(new_tile);
			}

			let ts = insert_sorted(&self.ts, new_tile);

			if to_chiitoi(&ts).is_some() {
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
		let Self(ts, ms) = self;

		ts.into_iter().enumerate()
			.flat_map(move |(i, new_tile)| {
				let ts = unsafe { except(&ts, [i]) };
				Hand(ts, ms).to_scorable_hands(new_tile, TsumoOrRon::Tsumo)
			})
	}
}

impl HandMeld {
	/// Construct a `HandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub const fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let tile = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Ankan(tile))
	}

	/// Construct a `HandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub const unsafe fn ankan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let tile = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Ankan(tile)
	}

	/// Construct a `HandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub const fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let tile = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Minkan(tile))
	}

	/// Construct a `HandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub const unsafe fn minkan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let tile = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Minkan(tile)
	}

	/// Construct a `HandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub const fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let tile = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Minkou(tile))
	}

	/// Construct a `HandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub const unsafe fn minkou_unchecked(t1: Tile, t2: Tile, t3: Tile) -> Self {
		let tile = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Minkou(tile)
	}

	/// Construct a `HandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Minjun(t))
	}

	/// Construct a `HandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub const unsafe fn minjun_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Self {
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
		let (ts, ty, s) = Tile::parse_run_until::<4>(s, end)?;
		let ty = ty.ok_or(())?;
		Ok((match ts[..] {
			[t1, t2, t3, t4] => {
				let tile = Tile::kan_representative(t1, t2, t3, t4).ok_or(())?;
				match ty {
					HandMeldType::Ankan => Self::Ankan(tile),
					HandMeldType::Shouminkan |
					HandMeldType::MinjunMinkouDaiminkan => Self::Minkan(tile),
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
	pub fn tenpai(self, game_type: GameType) -> HandTenpai {
		match self {
			Self::One(h) => HandTenpai::One(core::iter::once(h.tenpai())),
			Self::Four(h) => HandTenpai::Four(h.tenpai(game_type)),
			Self::Seven(h) => HandTenpai::Seven(h.tenpai(game_type)),
			Self::Ten(h) => HandTenpai::Ten(h.tenpai(game_type)),
			Self::Thirteen(h) => HandTenpai::Thirteen(h.tenpai(game_type)),
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

			// SAFETY: `count` has been checked above to ensure that there are at most four tiles that match `t`.
			// Thus exactly 4 elements will be pushed into `ts_kan`, and exactly NT - 4 elements will be pushed into `ts_rest`.
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
			let [t1, t2, t3, t4] = unsafe { ts_kan.unwrap_unchecked() };
			// SAFETY: `ts_kan` is guaranteed to contain tiles that form a valid kan.
			break Some(Hand(ts_rest, append(ms, unsafe { HandMeld::ankan_unchecked(t1, t2, t3, t4) })));
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
) -> Option<([Tile; N - 3], HandMeld)> {
	let mut existing = ts.into_iter().enumerate().filter(|&(_, t)| t.eq_ignore_red(&new_tile));
	let (i1, t1) = existing.next()?;
	let (i2, t2) = existing.next()?;
	let (i3, t3) = existing.next()?;
	// SAFETY: `i*` are guaranteed to be in ascending order and within the bounds of `ts` by the definition of `.into_iter().enumerate()`.
	let ts = unsafe { except(&ts, [i1, i2, i3]) };
	// SAFETY: `existing` only yields tiles which equal `new_tile`, so all four must form a valid kan.
	let m = unsafe { HandMeld::minkan_unchecked(t1, t2, t3, new_tile) };
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
		// SAFETY: `self.combinations` only yields tiles which equal `new_tile`, so all three must form a valid kou.
		let m = unsafe { HandMeld::minkou_unchecked(t1, t2, self.new_tile) };
		// SAFETY: `i*` are guaranteed to be within the bounds of `self.hand.0` by the implementation of `.into_iter().enumerate()`
		// and to be in ascending order `ArrayVecIntoCombinations`.
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
				SortingNetwork::sort(&mut ts);
				ts
			};

			let Ok(tsl1) = ShunLowTile::try_from(t1) else { continue; };
			let Some(t) = ShunLowTileAndHasFiveRed::new(tsl1, t2, t3) else { continue; };
			let m = HandMeld::Minjun(t);

			// SAFETY: `i*` are guaranteed to be within the bounds of `self.hand.0` by the implementation of `.into_iter().enumerate()`
			// and to be in ascending order `ArrayVecIntoCombinations`.
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
	One(core::iter::Once<Tile>),
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
	T: Clone,
{
	let mut result = [const { core::mem::MaybeUninit::uninit() }; N - DN];

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

	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

#[derive(Clone, Debug)]
struct ScorableHandPairs<const N: usize> {
	arr: [Tile; N],
	new_tile_i: (usize, TsumoOrRon),
	i: core::ops::Range<usize>,
}

impl<const N: usize> ScorableHandPairs<N> {
	fn new(arr: [Tile; N], new_tile_i: (usize, TsumoOrRon)) -> Self {
		let i = 0..(arr.len().saturating_sub(1));
		Self { arr, new_tile_i, i }
	}
}

impl<const N: usize> ScorableHandPairs<N>
where
	[(); N - 2]:,
{
	// # Safety
	//
	// Requires `i < self.arr.len() - 1`.
	unsafe fn next_inner(&mut self, i: usize) -> Option<(ScorableHandPair, [Tile; N - 2], Option<(usize, TsumoOrRon)>)> {
		unsafe { core::hint::assert_unchecked(i < self.arr.len() - 1) };

		let pt1 = self.arr[i];
		let pt2 = self.arr[i + 1];
		let pair = ScorableHandPair::new(pt1, pt2)?;

		let rest = unsafe { except(&self.arr, [i, i + 1]) };

		let new_tile_i =
			if self.new_tile_i.0 < i { Some(self.new_tile_i) }
			else if self.new_tile_i.0 > i + 1 { Some((self.new_tile_i.0 - 2, self.new_tile_i.1)) }
			else { None };

		Some((pair, rest, new_tile_i))
	}
}

impl<const N: usize> Iterator for ScorableHandPairs<N>
where
	[(); N - 2 ]:,
{
	type Item = (ScorableHandPair, [Tile; N - 2], Option<(usize, TsumoOrRon)>);

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

impl<const N: usize> DoubleEndedIterator for ScorableHandPairs<N>
where
	[(); N - 2 ]:,
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

impl<const N: usize> ExactSizeIterator for ScorableHandPairs<N> where Self: Iterator {}

impl<const N: usize> core::iter::FusedIterator for ScorableHandPairs<N> where Self: Iterator {}

unsafe impl<const N: usize> core::iter::TrustedLen for ScorableHandPairs<N> where Self: Iterator {}

fn insert_sorted<T, const N: usize>(s: &[T; N], value: T) -> [T; N + 1]
where
	T: Clone + Ord,
{
	/// SAFETY: Requires `dst.len() == s.len() + 1`.
	unsafe fn insert_sorted_inner<T>(dst: &mut [core::mem::MaybeUninit<T>], s: &[T], value: T) where T: Clone + Ord {
		unsafe { core::hint::assert_unchecked(dst.len() == s.len() + 1); }

		let (Ok(i) | Err(i)) = s.binary_search(&value);
		dst[..i].write_clone_of_slice(&s[..i]);
		dst[i].write(value);
		dst[i + 1..].write_clone_of_slice(&s[i..]);
	}

	let mut result = [const { core::mem::MaybeUninit::uninit() }; N + 1];
	unsafe { insert_sorted_inner(&mut result, s, value); }
	// SAFETY: `insert_sorted_inner` initializes all elements.
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

const fn to_kou(tile: Tile, new_tile_i: Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld {
	if let Some((_, tsumo_or_ron)) = new_tile_i {
		ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron }
	}
	else {
		ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(tile))
	}
}

// SAFETY: `new_tile_i` must be `None` or `Some((0..=2, _))`.
const unsafe fn to_shun(tile: ShunLowTileAndHasFiveRed, new_tile_i: Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld {
	match new_tile_i {
		None => ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun(tile)),
		Some((0, tsumo_or_ron)) =>
			if tile.remove_red().number() == ShunLowNumber::Seven {
				ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron }
			}
			else {
				ScorableHandFourthMeld::RyanmenLow { tile, tsumo_or_ron }
			},
		Some((1, tsumo_or_ron)) => ScorableHandFourthMeld::Kanchan { tile, tsumo_or_ron },
		Some((2, tsumo_or_ron)) =>
			if tile.remove_red().number() == ShunLowNumber::One {
				ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron }
			}
			else {
				ScorableHandFourthMeld::RyanmenHigh { tile, tsumo_or_ron }
			},
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

// SAFETY: `new_tile_i` must be `None` or `Some((0..=2, _))`.
const unsafe fn to_meld(t1: Tile, t2: Tile, t3: Tile, new_tile_i: Option<(usize, TsumoOrRon)>) -> Option<ScorableHandFourthMeld> {
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
type Melds1AndRest<const N: usize> = core::array::IntoIter<(ScorableHandFourthMeld, [Tile; N - 3], Option<(usize, TsumoOrRon)>), 4>;

fn to_meld_and_rest<const N: usize>(ts: [Tile; N], new_tile_i: Option<(usize, TsumoOrRon)>) -> Melds1AndRest<N>
where
	[(); N - 3]:,
{
	fn to_meld_and_rest_inner<const N: usize, TRest>(
		ts: [Tile; N],
		new_tile_i: Option<(usize, TsumoOrRon)>,
		t1_is_new: bool,
		t2_expected: TRest,
		t3_expected: TRest,
		t_rest_f: impl Fn(Tile) -> Result<TRest, ()>,
		mut meld_f: impl FnMut(TRest, TRest, Option<(usize, TsumoOrRon)>) -> ScorableHandFourthMeld,
		meld_and_rests: &mut ArrayVec<(ScorableHandFourthMeld, [Tile; N - 3], Option<(usize, TsumoOrRon)>), 4>,
	)
	where
		TRest: CmpIgnoreRed + Copy,
	{
		let mut found_non_tanki = false;
		let mut found_tanki = t1_is_new;

		let mut find_t2 = find_tile_f(new_tile_i, t1_is_new, t2_expected, &t_rest_f, 1);
		for (i2, &t2) in ts[1..(N - 1)].iter().enumerate() {
			match find_t2(i2, t2) {
				FindTile::Found(i2, t2, t2_is_new) => {
					let mut find_t3 = find_tile_f(new_tile_i, t1_is_new || t2_is_new, t3_expected, &t_rest_f, 1 + i2);
					for (i3, &t3) in ts[(1 + i2)..].iter().enumerate() {
						match find_t3(i3, t3) {
							FindTile::Found(i3, t3, _) => {
								let (new_tile_i_this, new_tile_i_rest) = extract_new_tile_i(new_tile_i, i2, i3);
								let meld = meld_f(t2, t3, new_tile_i_this);
								let result = if matches!(meld, ScorableHandFourthMeld::Tanki(_)) { &mut found_tanki } else { &mut found_non_tanki };
								if !core::mem::replace(result, true) {
									let rest = unsafe { except(&ts, [0, i2, i3]) };
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
	mas: Dedup<Melds1AndRest<6>>,
}

impl Melds2 {
	fn new(ts: [Tile; 6], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mas = Dedup::new(to_meld_and_rest(ts, new_tile_i));
		Self { mas }
	}
}

impl Iterator for Melds2 {
	type Item = (ScorableHandMeld, ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, [t1, t2, t3], new_tile_i) = self.mas.next()?;
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

impl core::iter::FusedIterator for Melds2 where Dedup<Melds1AndRest<6>>: core::iter::FusedIterator {}

/// Finds two melds from the given tiles.
///
/// When `N == 6`, using `Melds2` is more efficient.
#[derive(Clone, Debug, Default)]
struct Melds2AndRest<const N: usize>
where
	Melds1AndRest<{ N - 3 }>:,
{
	// TODO(rustup): This would be better as `ma: Option<ScorableHandFourthMeld>, mbs: Melds1AndRest<{ N - 3 }>`, but that causes an ICE.
	// Ref: https://github.com/rust-lang/rust/issues/132960
	ma_and_mbs: Option<(ScorableHandFourthMeld, Melds1AndRest<{ N - 3 }>)>,
	mas: Dedup<Melds1AndRest<N>>,
}

impl<const N: usize> Melds2AndRest<N>
where
	Melds1AndRest<{ N - 3 }>:,
{
	fn new(ts: [Tile; N], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mas = Dedup::new(to_meld_and_rest(ts, new_tile_i));
		Self {
			ma_and_mbs: None,
			mas,
		}
	}
}

impl<const N: usize> Iterator for Melds2AndRest<N>
where
	Melds1AndRest<{ N - 3 }>: Iterator<Item = (ScorableHandFourthMeld, [Tile; (N - 3) - 3], Option<(usize, TsumoOrRon)>)>,
{
	type Item = (ScorableHandMeld, ScorableHandFourthMeld, [Tile; (N - 3) - 3], Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, mbs) =
				if let Some(ma_and_mbs) = &mut self.ma_and_mbs {
					ma_and_mbs
				}
				else {
					let (ma, ts, new_tile_i) = self.mas.next()?;
					let mbs = to_meld_and_rest(ts, new_tile_i);
					self.ma_and_mbs.insert((ma, mbs))
				};

			let Some((mb, ts, new_tile_i)) = mbs.next() else {
				self.ma_and_mbs = None;
				continue;
			};

			let (ma, mb) = sort_melds2(*ma, mb);
			break Some((ma, mb, ts, new_tile_i));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.mas.size_hint() == (0, Some(0)) && let Some((_, mbs)) = &self.ma_and_mbs {
			let (_, hi) = mbs.size_hint();
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
#[derive(Clone, Debug, Default)]
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
	type Item = ([ScorableHandMeld; 2], ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, mb, [t1, t2, t3], new_tile_i) = self.mabs.next()?;
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

impl core::iter::FusedIterator for Melds3 where Dedup<Melds2AndRest<9>>: core::iter::FusedIterator {}

/// Finds three melds from the given tiles.
///
/// When `N == 9`, using `Melds3` is more efficient.
#[derive(Clone, Debug, Default)]
struct Melds3AndRest<const N: usize>
where
	Melds1AndRest<{ (N - 3) - 3 }>:,
{
	// TODO(rustup): This would be better as `mab: Option<(ScorableHandMeld, ScorableHandFourthMeld)>, mcs: Melds1AndRest<{ (N - 3) - 3 }>`, but that causes an ICE.
	// Ref: https://github.com/rust-lang/rust/issues/132960
	mab_and_mcs: Option<(ScorableHandMeld, ScorableHandFourthMeld, Melds1AndRest<{ (N - 3) - 3 }>)>,
	mabs: Dedup<Melds2AndRest<N>>,
}

impl<const N: usize> Melds3AndRest<N>
where
	Melds1AndRest<{ (N - 3) - 3 }>:,
{
	fn new(ts: [Tile; N], new_tile_i: Option<(usize, TsumoOrRon)>) -> Self {
		let mabs = Dedup::new(Melds2AndRest::new(ts, new_tile_i));
		Self {
			mab_and_mcs: None,
			mabs,
		}
	}
}

impl<const N: usize> Iterator for Melds3AndRest<N>
where
	Melds1AndRest<{ (N - 3) - 3 }>: Iterator<Item = (ScorableHandFourthMeld, [Tile; ((N - 3) - 3) - 3], Option<(usize, TsumoOrRon)>)>,
{
	type Item = ([ScorableHandMeld; 2], ScorableHandFourthMeld, [Tile; ((N - 3) - 3) - 3], Option<(usize, TsumoOrRon)>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (ma, mb, mcs) =
				if let Some(mab_and_mcs) = &mut self.mab_and_mcs {
					mab_and_mcs
				}
				else {
					let (ma, mb, ts, new_tile_i) = self.mabs.next()?;
					let mcs = to_meld_and_rest(ts, new_tile_i);
					self.mab_and_mcs.insert((ma, mb, mcs))
				};

			let Some((mc, ts, new_tile_i)) = mcs.next() else {
				self.mab_and_mcs = None;
				continue;
			};

			let (mab, mc) = sort_melds3(*ma, *mb, mc);
			break Some((mab, mc, ts, new_tile_i));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.mabs.size_hint() == (0, Some(0)) && let Some((_, _, mcs)) = &self.mab_and_mcs {
			let (_, hi) = mcs.size_hint();
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
#[derive(Clone, Debug, Default)]
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
	type Item = ([ScorableHandMeld; 3], ScorableHandFourthMeld);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let ([ma, mb], mc, [t1, t2, t3], new_tile_i) = self.mabcs.next()?;
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

impl core::iter::FusedIterator for Melds4 where Dedup<Melds3AndRest<12>>: core::iter::FusedIterator {}

fn sort_melds2(ma: ScorableHandFourthMeld, mb: ScorableHandFourthMeld) -> (ScorableHandMeld, ScorableHandFourthMeld) {
	match (ma, mb) {
		(ScorableHandFourthMeld::Tanki(ma), ScorableHandFourthMeld::Tanki(mb)) => {
			let [ma, mb] = core::cmp::minmax_by_key(ma, mb, ScorableHandMeldSortCriteria::new);
			(ma, ScorableHandFourthMeld::Tanki(mb))
		},

		(ScorableHandFourthMeld::Tanki(ma), mb) |
		(mb, ScorableHandFourthMeld::Tanki(ma)) =>
			(ma, mb),

		// At most one meld can be non-tanki
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn sort_melds3(ma: ScorableHandMeld, mb: ScorableHandFourthMeld, mc: ScorableHandFourthMeld) -> ([ScorableHandMeld; 2], ScorableHandFourthMeld) {
	match (mb, mc) {
		(ScorableHandFourthMeld::Tanki(mb), ScorableHandFourthMeld::Tanki(mc)) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb));

			let [mb, mc] = core::cmp::minmax_by_key(mb, mc, ScorableHandMeldSortCriteria::new);
			let mab = core::cmp::minmax_by_key(ma, mb, ScorableHandMeldSortCriteria::new);
			(mab, ScorableHandFourthMeld::Tanki(mc))
		},

		(ScorableHandFourthMeld::Tanki(mb), mc) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb));

			([ma, mb], mc)
		},

		(mc, ScorableHandFourthMeld::Tanki(mb)) => {
			let mab = core::cmp::minmax_by_key(ma, mb, ScorableHandMeldSortCriteria::new);
			(mab, mc)
		},

		// At most one meld can be non-tanki
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn sort_melds4(ma: ScorableHandMeld, mb: ScorableHandMeld, mc: ScorableHandFourthMeld, md: ScorableHandFourthMeld) -> ([ScorableHandMeld; 3], ScorableHandFourthMeld) {
	debug_assert!(ScorableHandMeldSortCriteria::new(&ma) <= ScorableHandMeldSortCriteria::new(&mb));

	match (mc, md) {
		(ScorableHandFourthMeld::Tanki(mc), ScorableHandFourthMeld::Tanki(md)) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&mc));

			let [mc, md] = core::cmp::minmax_by_key(mc, md, ScorableHandMeldSortCriteria::new);
			let [mb, mc] = core::cmp::minmax_by_key(mb, mc, ScorableHandMeldSortCriteria::new);
			let [ma, mb] = core::cmp::minmax_by_key(ma, mb, ScorableHandMeldSortCriteria::new);
			([ma, mb, mc], ScorableHandFourthMeld::Tanki(md))
		},

		(ScorableHandFourthMeld::Tanki(mc), md) => {
			debug_assert!(ScorableHandMeldSortCriteria::new(&mb) <= ScorableHandMeldSortCriteria::new(&mc));

			([ma, mb, mc], md)
		},

		(md, ScorableHandFourthMeld::Tanki(mc)) => {
			let [mb, mc] = core::cmp::minmax_by_key(mb, mc, ScorableHandMeldSortCriteria::new);
			let [ma, mb] = core::cmp::minmax_by_key(ma, mb, ScorableHandMeldSortCriteria::new);
			([ma, mb, mc], md)
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

impl<I> const Default for Dedup<I> where I: [const] Default + Iterator {
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

#[derive(Clone, Debug)]
struct LookupKokushiMusou {
	set: Tile34Set,
	duplicate: core::mem::MaybeUninit<Tile>,
}

impl LookupKokushiMusou {
	fn new(tiles: &[Tile; 13]) -> Self {
		let mut set = Tile34Set::default();
		set.insert(tiles[0]);
		let mut duplicate = core::mem::MaybeUninit::uninit();
		for &t in &tiles[1..] {
			if !set.insert(t) {
				duplicate.write(t);
			}
		}
		Self { set, duplicate }
	}

	fn with_new_tile(mut self, new_tile: Tile) -> Option<ScorableHand> {
		const EXPECTED_SET: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R };

		if !self.set.insert(new_tile) {
			self.duplicate.write(new_tile);
		}
		(self.set == EXPECTED_SET).then(|| {
			let duplicate = unsafe { self.duplicate.assume_init() };
			let was_juusanmen_wait = new_tile == duplicate;
			ScorableHand::KokushiMusou(ScorableHandKokushiMusou { duplicate, was_juusanmen_wait })
		})
	}
}

fn to_chiitoi(ts: &[Tile; 14]) -> Option<ScorableHand> {
	// Ref: https://rust.godbolt.org/z/cnY9G46dx

	let ps = cfg_select! {
		target_arch = "x86_64" => {{
			// `core::simd` generates terrible code on RV, so use it for x86_64 only.

			let ts = unsafe { &*<*const [Tile; 14]>::cast::<[u8; 14]>(ts) };
			let ts = core::simd::Simd::from_array(*ts);
			let ts_shifted = ts.extract::<1, 13>();
			let ts = ts.extract::<0, 13>();

			let adjacents_are_eq = ts ^ ts_shifted;
			let adjacents_are_eq = core::simd::cmp::SimdPartialOrd::simd_lt(adjacents_are_eq, core::simd::Simd::splat(2));
			let adjacents_are_eq = adjacents_are_eq.to_bitmask();

			let pairs = ts | ts_shifted;
			let pairs = pairs.resize::<14>(0);
			let pairs = unsafe { core::mem::transmute::<core::simd::Simd<u8, 14>, core::simd::Simd<u16, 7>>(pairs) };
			let pairs = core::simd::num::SimdUint::cast::<u8>(pairs);
			let pairs = pairs.to_array();

			(adjacents_are_eq == 0x1555).then_some(pairs)
		}},

		all(target_arch = "riscv64", target_feature = "v") => {{
			// The above `core::simd` impl for x86_64 generates extremely terrible code on RV+v.
			//
			// The scalar impl below this one does auto-vectorize on RV+v but very badly - it generates a large amount of code that does ops with
			// `vl = 4` instead of `vl = 14`.
			//
			// So we do it manually with inline asm.

			let pairs: u64;
			let adjacents_are_eq: u64;
			unsafe {
				core::arch::asm!(
					// let ts = unsafe { &*<*const [Tile; 14]>::cast::<[u8; 14]>(ts) };
					// let ts = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 14, e8, m1, ta, ma",
					"vle8.v v8, ({ts})",

					// let ts_shifted = ts.extract::<1, 13>();
					// let ts = ts.extract::<0, 13>();
					"vsetivli zero, 13, e8, m1, ta, ma",
					"vslidedown.vi v9, v8, 1",

					// let eq = ts ^ ts_shifted;
					"vxor.vv v10, v8, v9",
					// let eq = core::simd::cmp::SimdPartialOrd::simd_lt(eq, core::simd::Simd::splat(2));
					"vmsleu.vi v10, v10, 1",

					// let pairs = ts | ts_shifted;
					"vor.vv v8, v8, v9",
					// let pairs = pairs.resize::<14>(0);
					// let pairs = unsafe { core::mem::transmute::<core::simd::Simd<u8, 14>, core::simd::Simd<u16, 7>>(pairs) };
					// let pairs = core::simd::num::SimdUint::cast::<u8>(pairs);
					"vsetivli zero, 7, e8, m1, ta, ma",
					// Note: Per the ISA spec, the canonical way to do this would be `vncvt.x.x.w v8, v8`, ie `vnsrl.wx v8, v8, zero`,
					// But compilers prefer to do it with zero immediate instead of zero integer register to avoid cross-register file interaction.
					//
					// Ref: https://inbox.sourceware.org/gcc-patches/20250207162212.66994-1-vineetg@rivosinc.com/T/
					// Ref: https://inbox.sourceware.org/gcc-patches/20250208043433.86154-1-vineetg@rivosinc.com/T/
					// Ref: https://reviews.llvm.org/D132041
					"vnsrl.wi v8, v8, 0",

					"vsetvli zero, zero, e64, m1, ta, ma",
					// let adjacents_are_eq = eq.to_bitmask();
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
			(adjacents_are_eq & 0x1FFF == 0x1555).then_some(pairs)
		}},

		_ => {{
			// Scalar impl is optimal on RV-v.

			let mut pairs = [0_u8; 7];
			let mut valid = true;
			for (i, &[a, b]) in ts.as_chunks().0.iter().enumerate() {
				pairs[i] = a as u8 | b as u8;
				valid &= a.eq_ignore_red(&b);
			}
			for &[a, b] in ts[1..].as_chunks().0 {
				valid &= a.ne_ignore_red(&b);
			}
			valid.then_some(pairs)
		}},
	};

	ps.map(|ps| {
		// SAFETY:
		//
		// - All `u8`s in `Result` are guaranteed to be valid `Tile` values, since every `a` and `b` that went into them was either identical
		//   or one was a `Five` and the other was a `FiveRed`. Thus transmuting each `u8` to `Tile` is guaranteed to produce a valid `Tile`.
		//
		// - `ScorableHandPair` is `repr(transparent)` around `Tile` which is `repr(transparent)` around `u8`.
		//   Thus transmuting `[u8; 7]` to `[ScorableHandPair; 7]` is sound.
		let ps = unsafe { core::mem::transmute::<[u8; 7], [ScorableHandPair; 7]>(ps) };
		ScorableHand::Chiitoi(ScorableHandChiitoi(ps))
	})
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
				ScorableHandMeld::Ankou(t) => [(t, None), (t, None), (t, None)],
				ScorableHandMeld::Anjun(t) => {
					let (t1, t2, t3) = t.shun();
					[(t1.into(), None), (t2.into(), None), (t3.into(), None)]
				},
				_ => unreachable!(),
			},

			ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron } => [(tile, None), (tile, None), (tile, Some(tsumo_or_ron))],

			ScorableHandFourthMeld::Kanchan { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				[(t1.into(), None), (t2.into(), Some(tsumo_or_ron)), (t3.into(), None)]
			},

			ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				[(t1.into(), matches!(t1, tn!(7m | 7p | 7s)).then_some(tsumo_or_ron)), (t2.into(), None), (t3.into(), matches!(t3, tn!(3m | 3p | 3s)).then_some(tsumo_or_ron))]
			},

			ScorableHandFourthMeld::RyanmenLow { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				[(t1.into(), Some(tsumo_or_ron)), (t2.into(), None), (t3.into(), None)]
			},

			ScorableHandFourthMeld::RyanmenHigh { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				[(t1.into(), None), (t2.into(), None), (t3.into(), Some(tsumo_or_ron))]
			},
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
						ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
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

				let actual: std::vec::Vec<_> = super::Dedup::new(Melds2::new(ts, new_tile_i)).collect();
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
			let mut used: Tile34MultiSet = Default::default();
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

				for mc in melds.into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last) {
					let [(t7, t7tr), (t8, t8tr), (t9, t9tr)] = to_ttrs(mc);

					let mut used = used.clone();
					if used.try_extend([t7, t8, t9]).is_err() {
						continue;
					}

					let expected =
						if let ScorableHandFourthMeld::Tanki(mc) = mc {
							let mut ms = [ma, mb, mc];
							ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
							let [m2, m3, m4] = ms;
							([m2, m3], ScorableHandFourthMeld::Tanki(m4))
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
					let ts = ts.map(|(t, _)| t);

					let actual: std::vec::Vec<_> = super::Dedup::new(super::Melds3::new(ts, new_tile_i)).collect();
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
			let mut used: Tile34MultiSet = Default::default();
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

					for md in melds.into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last) {
						let [(t10, t10tr), (t11, t11tr), (t12, t12tr)] = to_ttrs(md);

						let mut used = used.clone();
						if used.try_extend([t10, t11, t12]).is_err() {
							continue;
						}

						let expected =
							if let ScorableHandFourthMeld::Tanki(md) = md {
								let mut ms = [ma, mb, mc, md];
								ms.sort_unstable_by_key(ScorableHandMeldSortCriteria::new);
								let [m1, m2, m3, m4] = ms;
								([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
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
						let ts = ts.map(|(t, _)| t);

						let actual: std::vec::Vec<_> = super::Dedup::new(super::Melds4::new(ts, new_tile_i)).collect();
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
		assert_eq!(shouminkans.next().unwrap(), Hand(t![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m, G], [make_hand!(@meld { minkan E E E E })]));
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
			assert!(matches!(minkous.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m], [make_hand!(@meld { minkou 2m 2m 2m })]) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minkous.size_hint(), (0, Some(0)));
			assert!(minkous.next().is_none());
			assert_eq!(minkous.size_hint(), (0, Some(0)));
		}

		let hs: std::vec::Vec<_> = minkous.collect();
		assert_eq!(hs.len(), 1);
		assert!(hs[0].0 == Hand(t![1m, 1m, 1m, 3m, 3m, 3m, 4m, 4m, 4m, 5m, 5m], [make_hand!(@meld { minkou 2m 2m 2m })]) && hs[0].1 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let minjuns = h.find_minjuns(tn!(4m));

		{
			// 23506m => 5C2 = 10
			assert_eq!(minjuns.size_hint(), (0, Some(10)));
			let mut minjuns = minjuns.clone();
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 2m 3m 4m })]) && allowed_discards == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(9)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 5m })]) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(5)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 0m })]) && allowed_discards == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(4)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 5m 6m })]) && allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(1)));
			assert!(matches!(minjuns.next(), Some((h, allowed_discards)) if h == Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 0m 6m })]) && allowed_discards == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]));
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
			assert!(minjuns.next().is_none());
			assert_eq!(minjuns.size_hint(), (0, Some(0)));
		}

		let hs: std::vec::Vec<_> = minjuns.collect();
		assert_eq!(hs.len(), 5);
		assert!(hs[0].0 == Hand(t![1m, 5m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 2m 3m 4m })]) && hs[0].1 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert!(hs[1].0 == Hand(t![1m, 2m, 0m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 5m })]) && hs[1].1 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert!(hs[2].0 == Hand(t![1m, 2m, 5m, 6m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 3m 4m 0m })]) && hs[2].1 == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		assert!(hs[3].0 == Hand(t![1m, 2m, 3m, 0m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 5m 6m })]) && hs[3].1 == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]);
		assert!(hs[4].0 == Hand(t![1m, 2m, 3m, 5m, 7m, 8m, E, E, E, G, G], [make_hand!(@meld { minjun 4m 0m 6m })]) && hs[4].1 == [0, 1, 2, 3, 5, 6, 7, 8, 9, 10]);
	}

	#[test]
	fn kuikae() {
		{
			let h = make_hand!(1m 1m 1m E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minkous(t!(1m)).collect();
			for (h, allowed_discards) in hs {
				assert_eq!(h, Hand(t![1m, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minkou 1m 1m 1m })]));
				assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
			}
		}

		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(2p)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![2p, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 1p 2p 3p })]));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1s)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1s, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 1s 2s 3s })]));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(1s)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1s, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 1s 2s 3s })]));
			assert_eq!(*allowed_discards, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(4m)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1m, E, E, E, S, S, S, W, W, W, N], [make_hand!(@meld { minjun 2m 3m 4m })]));
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
			assert!(matches!(&hs[0], (h, allowed_discards) if *h == Hand(t![1m, 4m, 5m, 6m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 2m 3m 4m })]) && *allowed_discards == [2, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert!(matches!(&hs[1], (h, allowed_discards) if *h == Hand(t![1m, 2m, 4m, 6m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 3m 4m 5m })]) && *allowed_discards == [0, 1, 3, 4, 5, 6, 7, 8, 9, 10]));
			assert!(matches!(&hs[2], (h, allowed_discards) if *h == Hand(t![1m, 2m, 3m, 4m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 4m 5m 6m })]) && *allowed_discards == [0, 1, 2, 4, 5, 6, 7, 8, 9, 10]));
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let hs: std::vec::Vec<_> = h.find_minjuns(tn!(7m)).collect();
			let [(h, allowed_discards)] = &hs[..] else { panic!(); };
			assert_eq!(*h, Hand(t![1m, 2m, 3m, 4m, E, E, E, S, S, S, W], [make_hand!(@meld { minjun 5m 6m 7m })]));
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
