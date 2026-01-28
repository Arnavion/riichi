use crate::{
	ArrayVec, ArrayVecIntoCombinations,
	CmpIgnoreRed,
	except,
	GameType,
	HandMeldType,
	NumberTile,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
	ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile, Tile34MultiSet, Tile34MultiSetElement, Tile34Set, TileMultiSetIntoIter, TsumoOrRon,
	decompose::{Keys, Lookup, LookupForNewTile},
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
		// SAFETY: `i` is guaranteed to be within the bounds of `ts` by the assignment of `t_discard`.
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
		let lookup = Lookup::new(Keys::default().push_all(ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);
		let [ma, mb, mc] = ms.map(Into::into);
		Hand4ScorableHands { lookup, ma, mb, mc }
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
		let Self(ts, _) = self;
		let keys = Keys::default().push_all(ts);
		Hand4Tenpai { tiles, keys }
	}
}

#[derive(Clone, Debug)]
pub struct Hand4ScorableHands {
	lookup: LookupForNewTile<0>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
	mc: ScorableHandMeld,
}

assert_size_of!(Hand4ScorableHands, 112);

impl Iterator for Hand4ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		let ([], md, pair) = self.lookup.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, self.mb, self.mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.lookup.size_hint()
	}
}

impl core::iter::FusedIterator for Hand4ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand4Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	keys: Keys<4>,
}

assert_size_of!(Hand4Tenpai, 40);

impl Iterator for Hand4Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			if Lookup::<1>::new(self.keys.clone().push(new_tile)).next().is_some() {
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
		let lookup = Lookup::new(Keys::default().push_all(ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);
		let [ma, mb] = ms.map(Into::into);
		Hand7ScorableHands { lookup, ma, mb }
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
		let Self(ts, _) = self;
		let keys = Keys::default().push_all(ts);
		Hand7Tenpai { tiles, keys }
	}
}

#[derive(Clone, Debug)]
pub struct Hand7ScorableHands {
	lookup: LookupForNewTile<1>,
	ma: ScorableHandMeld,
	mb: ScorableHandMeld,
}

assert_size_of!(Hand7ScorableHands, 120);

impl Iterator for Hand7ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		let ([mc], md, pair) = self.lookup.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, self.mb, mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.lookup.size_hint()
	}
}

impl core::iter::FusedIterator for Hand7ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand7Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	keys: Keys<7>,
}

assert_size_of!(Hand7Tenpai, 40);

impl Iterator for Hand7Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			if Lookup::<2>::new(self.keys.clone().push(new_tile)).next().is_some() {
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
		let lookup = Lookup::new(Keys::default().push_all(ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);
		let [ma] = ms.map(Into::into);
		Hand10ScorableHands { lookup, ma }
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
		let Self(ts, _) = self;
		let keys = Keys::default().push_all(ts);
		Hand10Tenpai { tiles, keys }
	}
}

#[derive(Clone, Debug)]
pub struct Hand10ScorableHands {
	lookup: LookupForNewTile<2>,
	ma: ScorableHandMeld,
}

assert_size_of!(Hand10ScorableHands, 136);

impl Iterator for Hand10ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		let ([mb, mc], md, pair) = self.lookup.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular::new(self.ma, mb, mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.lookup.size_hint()
	}
}

impl core::iter::FusedIterator for Hand10ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand10Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	keys: Keys<10>,
}

assert_size_of!(Hand10Tenpai, 40);

impl Iterator for Hand10Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;
			if Lookup::<3>::new(self.keys.clone().push(new_tile)).next().is_some() {
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
		let lookup = Lookup::new(Keys::default().push_all(ts).push(new_tile));
		let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);

		let kokushi_musou = LookupKokushiMusou::new(&ts).with_new_tile(new_tile);

		let chiitoi = match lookup_chiitoi_with_pairs(&ts) {
			Some((ps, t)) =>
				if let Some(p7) = ScorableHandPair::new(t, new_tile) {
					let Err(i) = ps.binary_search(&p7) else {
						// SAFETY: `lookup_chiitoi_with_pairs` is guaranteed to return a `t` that would not form the same pair as any of `ps`.
						unsafe { core::hint::unreachable_unchecked(); }
					};
					let mut pairs = [const { core::mem::MaybeUninit::uninit() }; 7];
					pairs[..i].write_copy_of_slice(&ps[..i]);
					pairs[i].write(p7);
					pairs[i + 1..].write_copy_of_slice(&ps[i..]);
					// SAFETY: Inserting an element into a `[; 6]` initializes all elements of the resulting `[; 7]`.
					let pairs = unsafe { core::mem::MaybeUninit::array_assume_init(pairs) };
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
		let Self(ts, _) = self;
		let kokushi_musou = LookupKokushiMusou::new(&ts);
		let chiitoi = lookup_chiitoi(&ts);
		let keys = Keys::default().push_all(ts);
		Hand13Tenpai { tiles, kokushi_musou, chiitoi, keys }
	}
}

#[derive(Clone, Debug)]
pub struct Hand13ScorableHands {
	lookup: LookupForNewTile<3>,
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

		let ([ma, mb, mc], md, pair) = self.lookup.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, md, pair)))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let extra = usize::from(self.kokushi_musou.is_some()) + usize::from(self.chiitoi.is_some());
		let (lo, hi) = self.lookup.size_hint();
		let lo = lo + extra;
		let hi = hi.and_then(|hi| hi.checked_add(extra));
		(lo, hi)
	}
}

impl core::iter::FusedIterator for Hand13ScorableHands {}

#[derive(Clone, Debug)]
pub struct Hand13Tenpai {
	tiles: core::slice::Iter<'static, Tile>,
	kokushi_musou: LookupKokushiMusou,
	chiitoi: Option<Tile>,
	keys: Keys<13>,
}

assert_size_of!(Hand13Tenpai, 56);

impl Iterator for Hand13Tenpai {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let new_tile = *self.tiles.next()?;

			if self.kokushi_musou.clone().with_new_tile(new_tile).is_some() {
				return Some(new_tile);
			}

			if let Some(t) = self.chiitoi && t.eq_ignore_red(&new_tile) {
				return Some(new_tile);
			}

			if Lookup::<4>::new(self.keys.clone().push(new_tile)).next().is_some() {
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
				// SAFETY: `i` is guaranteed to be within the bounds of `ts` by the definition of `.into_iter().enumerate()`.
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
	// SAFETY: N + 1 > N and `[T; _]` has the same alignment as `T`.
	unsafe { result.as_mut_ptr().cast::<[T; N]>().write(arr); }
	result[N].write(element);
	// SAFETY: Appending an element to a `[; N]` initializes all elements of the resulting `[; N + 1]`.
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

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
			// SAFETY: Pigeonhole principle.
			let duplicate = unsafe { self.duplicate.assume_init() };
			let was_juusanmen_wait = new_tile == duplicate;
			ScorableHand::KokushiMusou(ScorableHandKokushiMusou { duplicate, was_juusanmen_wait })
		})
	}
}

fn lookup_chiitoi(ts: &[Tile; 13]) -> Option<Tile> {
	let (is_valid, t) = cfg_select! {
		// TODO(rustup): The `core::simd` version has a bunch of inefficiencies compared to this manual impl,
		// such as multiple `vmerge.vim`s since `core::simd` cannot represent masked `vadd.vi`,
		// and having to use so many vregs that it has to spill them to stack multiple times.
		all(target_arch = "riscv64", target_feature = "v") => {{
			let t: isize;
			let num_pairs: u64;

			unsafe {
				core::arch::asm!(
					// let ts /* : v24:v24 */ = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 13, e8, m1, ta, ma",
					"vle8.v v24, ({ts})",

					// let offsets /* : v8:v8 */ = ts >> 1;
					"vsrl.vi v8, v24, 1",

					// let mut counts /* : v12:v15 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vmv.v.i v12, 0",

					// let id /* : v16:v19 */ = core::simd::Simd::<u8, 34>::from_array(core::array::from_fn(|i| i as u8));
					"vid.v v16",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[0]);
					"vrgather.vi v20, v8, 0",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[1]);
					"vrgather.vi v20, v8, 1",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[2]);
					"vrgather.vi v20, v8, 2",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[3]);
					"vrgather.vi v20, v8, 3",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[4]);
					"vrgather.vi v20, v8, 4",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[5]);
					"vrgather.vi v20, v8, 5",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[6]);
					"vrgather.vi v20, v8, 6",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[7]);
					"vrgather.vi v20, v8, 7",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[8]);
					"vrgather.vi v20, v8, 8",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[9]);
					"vrgather.vi v20, v8, 9",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[10]);
					"vrgather.vi v20, v8, 10",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[11]);
					"vrgather.vi v20, v8, 11",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[12]);
					"vrgather.vi v20, v8, 12",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",

					// let single_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(1));
					"vmseq.vi v0, v12, 1",
					// let t = single_is.first_set().unwrap();
					"vfirst.m {t}, v0",

					// let pair_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));
					"vmseq.vi v0, v12, 2",
					// let num_pairs = pair_is.to_bitmask().count_ones();
					"vcpop.m {num_pairs}, v0",

					out("v0") _,
					out("v8") _,
					out("v12") _,
					out("v13") _,
					out("v14") _,
					out("v15") _,
					out("v16") _,
					out("v17") _,
					out("v18") _,
					out("v19") _,
					out("v20") _,
					out("v21") _,
					out("v22") _,
					out("v23") _,
					out("v24") _,

					thirty_four = in(reg) 34_usize,
					e8x34_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					ts = in(reg) ts.as_ptr(),
					t = lateout(reg) t,
					num_pairs = lateout(reg) num_pairs,
					options(nostack),
				);
			}

			(num_pairs == 6, (t as u8) << 1)
		}},

		_ => {{
			let mut first = 0_u64;
			let mut second = 0_u64;
			let mut invalid = 0_u64;
			for &t in ts {
				let t = t as u8;
				let offset = t >> 1;
				let mask = 0b1_u64 << offset;
				let first_mask = first & mask;
				let second_mask = second & mask;
				first |= mask;
				second |= first_mask;
				invalid |= second_mask;
			}

			#[expect(clippy::cast_possible_truncation)]
			let t = ((first ^ second).trailing_zeros() as u8) << 1;

			(invalid | (u64::from(first.count_ones()) ^ 7) | (u64::from(second.count_ones()) ^ 6) == 0, t)
		}},
	};

	is_valid.then(|| {
		// SAFETY: Since `is_valid` is true, `ts` is guaranteed to have contained six pairs and one unpaired tile,
		// and `t` is guaranteed to be that tile.
		unsafe { core::mem::transmute::<u8, Tile>(t) }
	})
}

fn lookup_chiitoi_with_pairs(ts: &[Tile; 13]) -> Option<([ScorableHandPair; 6], Tile)> {
	cfg_select! {
		// TODO(rustup): The `core::simd` version has a bunch of inefficiencies compared to this manual impl,
		// such as multiple `vmerge.vim`s since `core::simd` cannot represent masked `vadd.vi` or `vor.vv`,
		// and having to use so many vregs that it has to spill them to stack multiple times.
		all(target_arch = "riscv64", target_feature = "v") => {{
			let t: isize;
			let num_pairs: u64;
			let pair_representatives: u64;

			unsafe {
				core::arch::asm!(
					// let ts /* : v24:v24 */ = core::simd::Simd::from_array(*ts);
					"vsetivli zero, 13, e8, m1, ta, ma",
					"vle8.v v24, ({ts})",

					// let offsets /* : v8:v8 */ = ts >> 1;
					"vsrl.vi v8, v24, 1",

					// let mut counts /* : v12:v15 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vmv.v.i v12, 0",
					// let mut pair_representatives /* : v28:v31 */ = core::simd::Simd::<u8, 34>::splat(0);
					"vmv.v.i v28, 0",

					// let id /* : v16:v19 */ = core::simd::Simd::<u8, 34>::from_array(core::array::from_fn(|i| i as u8));
					"vid.v v16",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[0]);
					"vrgather.vi v20, v8, 0",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[0]);
					"vrgather.vi v20, v24, 0",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[1]);
					"vrgather.vi v20, v8, 1",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[1]);
					"vrgather.vi v20, v24, 1",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[2]);
					"vrgather.vi v20, v8, 2",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[2]);
					"vrgather.vi v20, v24, 2",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[3]);
					"vrgather.vi v20, v8, 3",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[3]);
					"vrgather.vi v20, v24, 3",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[4]);
					"vrgather.vi v20, v8, 4",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[4]);
					"vrgather.vi v20, v24, 4",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[5]);
					"vrgather.vi v20, v8, 5",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[5]);
					"vrgather.vi v20, v24, 5",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[6]);
					"vrgather.vi v20, v8, 6",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[6]);
					"vrgather.vi v20, v24, 6",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[7]);
					"vrgather.vi v20, v8, 7",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[7]);
					"vrgather.vi v20, v24, 7",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[8]);
					"vrgather.vi v20, v8, 8",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[8]);
					"vrgather.vi v20, v24, 8",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[9]);
					"vrgather.vi v20, v8, 9",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[9]);
					"vrgather.vi v20, v24, 9",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[10]);
					"vrgather.vi v20, v8, 10",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[10]);
					"vrgather.vi v20, v24, 10",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[11]);
					"vrgather.vi v20, v8, 11",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[11]);
					"vrgather.vi v20, v24, 11",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let offset /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(offsets[12]);
					"vrgather.vi v20, v8, 12",
					// let mask /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(offset, id);
					"vmseq.vv v0, v20, v16",
					// counts += core::simd::Simd::load_select_or_default(core::simd::Simd::<u8, 34>::splat(1).as_array(), mask);
					"vadd.vi v12, v12, 1, v0.t",
					// let t /* : v20:v23 */ = core::simd::Simd::<u8, 34>::splat(ts[12]);
					"vrgather.vi v20, v24, 12",
					// pair_representatives |= core::simd::Simd::load_select_or_default(t, mask);
					"vor.vv v28, v28, v20, v0.t",

					// let single_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(1));
					"vmseq.vi v0, v12, 1",
					// let t = single_is.first_set().unwrap();
					"vfirst.m {t}, v0",

					// let pair_is /* : v0:v0 */ = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));
					"vmseq.vi v0, v12, 2",
					// let num_pairs = pair_is.to_bitmask().count_ones();
					"vcpop.m {num_pairs}, v0",

					// let pair_representatives /* : v20:v23 */ = vcompress(pair_representatives, pair_is);
					"vcompress.vm v20, v28, v0",
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vmv.x.s {pair_representatives}, v20",

					out("v0") _,
					out("v8") _,
					out("v12") _,
					out("v13") _,
					out("v14") _,
					out("v15") _,
					out("v16") _,
					out("v17") _,
					out("v18") _,
					out("v19") _,
					out("v20") _,
					out("v21") _,
					out("v22") _,
					out("v23") _,
					out("v24") _,
					out("v28") _,
					out("v29") _,
					out("v30") _,
					out("v31") _,

					thirty_four = in(reg) 34_usize,
					e8x34_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					ts = in(reg) ts.as_ptr(),
					t = lateout(reg) t,
					num_pairs = lateout(reg) num_pairs,
					pair_representatives = lateout(reg) pair_representatives,
					options(nostack),
				);
			}

			(num_pairs == 6).then(|| {
				let t = (t as u8) << 1;
				// SAFETY: Since `num_pairs` is 6, `ts` is guaranteed to have contained six pairs and one unpaired tile,
				// and `t` is guaranteed to be that tile.
				let t = unsafe { core::mem::transmute::<u8, Tile>(t) };
				let ps = pair_representatives.to_le_bytes();
				let ps = [ps[0], ps[1], ps[2], ps[3], ps[4], ps[5]];
				// SAFETY: The pairs are guaranteed to be valid tiles themselves since they were formed by ORing tiles
				// that were equal to each other (after ignoring the "red" bit).
				let ps = unsafe { core::mem::transmute::<[u8; 6], [Tile; 6]>(ps) };
				let ps = ps.map(ScorableHandPair);
				(ps, t)
			})
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
				let mask = 0b1_u64 << offset;
				let first_mask = first & mask;
				let second_mask = second & mask;
				first |= mask;
				second |= first_mask;
				invalid |= second_mask;
			}

			if invalid | (u64::from(first.count_ones()) ^ 7) | (u64::from(second.count_ones()) ^ 6) != 0 {
				return None;
			}

			#[expect(clippy::cast_possible_truncation)]
			let t = ((first ^ second).trailing_zeros() as u8) << 1;
			// SAFETY: At this point after the above comparisons, `ts` is guaranteed to have contained six pairs and one unpaired tile,
			// and `t` is guaranteed to be that tile.
			let t = unsafe { core::mem::transmute::<u8, Tile>(t) };

			let ps = cfg_select! {
				all(target_arch = "x86_64", target_feature = "avx512vbmi2") => {{
					// TODO(rustup): Use `core::simd` once it supports register compress.
					//
					// Ref: https://github.com/rust-lang/portable-simd/issues/240
					let pair_representatives = core::simd::Simd::<u8, 64>::load_or_default(&pair_representatives);
					let ps = unsafe { core::arch::x86_64::_mm512_maskz_compress_epi8(second, pair_representatives.into()) };
					let ps = core::simd::Simd::from(ps);
					let ps = ps.to_array();
					[ps[0], ps[1], ps[2], ps[3], ps[4], ps[5]]
				}},

				_ => {{
					let mut ps = [const { core::mem::MaybeUninit::uninit() }; 6];
					let mut second = second;
					let mut offset = 0;
					for p in &mut ps {
						let i = second.trailing_zeros();
						second >>= i + 1;

						offset += i as usize;
						// SAFETY: `second` is a mask of the indices into `pair_representatives` which contain valid pairs.
						unsafe { core::hint::assert_unchecked(offset < pair_representatives.len()); }
						let pair_representative = pair_representatives[offset];
						p.write(pair_representative);
						offset += 1;
					}
					// SAFETY: The loop above only terminates when all elements of `ps` have been initialized.
					unsafe { core::mem::MaybeUninit::array_assume_init(ps) }
				}},
			};

			// SAFETY: The pairs are guaranteed to be valid tiles themselves since they were formed by ORing tiles
			// that were equal to each other (after ignoring the "red" bit).
			let ps = unsafe { core::mem::transmute::<[u8; 6], [Tile; 6]>(ps) };
			let ps = ps.map(ScorableHandPair);
			Some((ps, t))
		}},
	}
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use super::*;

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

		{
			let h = make_hand!(1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh);
			let actual_tenpai_tiles: std::vec::Vec<_> = h.tenpai(GameType::Yonma).collect();
			assert_eq!(actual_tenpai_tiles, t![S,]);
		}
	}
}
