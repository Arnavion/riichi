use crate::{
	append, ArrayVec,
	HandMeldType,
	Number, NumberSuit, NumberTile, NumberTileClassified,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
	ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile,
	Tile34MultiSet, Tile34Set, Tile34SetIntoIter,
	Tile37CountedMultiSet, Tile37MultiSet, Tile37Set,
	TsumoOrRon,
	decompose::{Lookup, LookupForNewTile, LookupForTenhou, lookup_tenpai},
};

/// A hand containing some number of tiles and melds.
///
/// This time is parameterized by the number of tiles `NT` and the number of melds `NM`.
/// Chii / pon / kan calls consume the type and return a new one with a different `NT` and `NM`.
/// If you want to hold all possible hands in a single type, use the [`HandStable`] and [`HandTentative`] enums.
///
/// It is possible to construct `Hand`s with arbitrary number of tiles and melds. However, operations like
/// [`find_minjuns`][Self::find_minjuns], [`discard`][Self::discard], [`into_scorable_hands`][Self::into_scorable_hands], etc
/// are only defined on specific instantiations of `Hand` that would appear in a game. See the implementations of `From`
/// for [`HandStable`] and [`HandTentative`].
///
/// # Safety
///
/// This type expects that its fields are consistent. This means:
///
/// - All [`HandMeld`]s are themselves consistent. See its docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive_const(Eq, PartialEq)]
pub struct Hand<const NT: usize, const NM: usize>(
	pub Tile37CountedMultiSet<NT>,
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
#[derive_const(Clone, Eq, PartialEq)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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

assert_size_of!(Hand<1, 4>, 28);
assert_size_of!(Hand<2, 4>, 28);
assert_size_of!(Hand<4, 3>, 28);
assert_size_of!(Hand<5, 3>, 28);
assert_size_of!(Hand<7, 2>, 24);
assert_size_of!(Hand<8, 2>, 24);
assert_size_of!(Hand<10, 1>, 24);
assert_size_of!(Hand<11, 1>, 24);
assert_size_of!(Hand<13, 0>, 20);
assert_size_of!(Hand<14, 0>, 20);
assert_size_of!(HandMeld, 2);

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandStable: From<Self>,
{
	/// Draw the given tile into this stable hand to form a tentative hand.
	pub fn draw(self, new_tile: Tile) -> Option<Hand<{ NT + 1 }, NM>> {
		let Self(ts, ms) = self;
		let ts = ts.insert(new_tile)?;
		Some(Hand(ts, ms))
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NM + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<{ ((NT - 1) - 1) - 1 }, { NM + 1 }>> {
		let Self(ts, ms) = self;
		find_daiminkan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, append(ms, m_new)))
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> Minkous<NT, NM>
	where
		[(); (NT - 1) - 1]:,
	{
		Minkous::new(self, new_tile)
	}

	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> Minjuns<NT, NM>
	where
		[(); (NT - 1) - 1]:,
	{
		Minjuns::new(self, new_tile)
	}
}

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandTentative: From<Hand<NT, NM>>,
{
	/// Discard the given tile from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile.
	/// If the given tile is not present in this hand, then this function returns `None`.
	pub fn discard(self, tile: Tile) -> Option<Hand<{ NT - 1 }, NM>> {
		let Self(ts, ms) = self;
		let ts = ts.remove(tile)?;
		Some(Hand(ts, ms))
	}

	/// Find all possible ankans (quad via kan call on a quad held in the hand).
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_ankans(self) -> Ankans<NT, NM> {
		Ankans::new(self)
	}

	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub const fn find_shouminkans(self) -> Shouminkans<NT, NM> {
		Shouminkans::new(self)
	}
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<const NT: usize, const NM: usize> Clone for Hand<NT, NM> {
	fn clone(&self) -> Self {
		Self(self.0.clone(), self.1)
	}
}

impl<const NT: usize, const NM: usize> core::fmt::Debug for Hand<NT, NM>
where
	Self: core::fmt::Display,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl<const NT: usize, const NM: usize> core::fmt::Display for Hand<NT, NM> {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self(ts, ms) = self;

		let mut ts = ts.clone().into_iter();
		if let Some((t1, count)) = ts.next() {
			write!(f, "{t1}")?;
			for _ in 1..count.get() {
				write!(f, " {t1}")?;
			}
			for (t, count) in ts {
				for _ in 0..count.get() {
					write!(f, " {t}")?;
				}
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
	/// Add the given drawn / called tile to this hand and convert it into a [`ScorableHandRegular`] if one exists.
	///
	/// Note that a `ScorableHandRegular` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHandRegular`.
	///
	/// Returns `None` if a scorable hand cannot be formed with the new tile.
	pub fn into_scorable_hand(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Option<ScorableHandRegular> {
		let Self(ts, ms) = self;

		_ = ts.clone().insert(new_tile)?;

		let t1 = ts.into_iter().next();
		let (t1, _) = unsafe { t1.unwrap_unchecked() };

		let pair = ScorableHandPair::new(t1, new_tile)?;
		let [ma, mb, mc, md] = ms.map(Into::into);
		Some(ScorableHandRegular::new(ma, mb, mc, ScorableHandFourthMeld::tanki(md), pair, tsumo_or_ron))
	}

	/// Returns a set of all tiles that would complete this hand.
	pub fn tenpai(self) -> Tile37Set {
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
		let t1 = ts.into_iter().next();
		let (t1, _) = unsafe { t1.unwrap_unchecked() };
		let mut result = Tile37Set::default();
		result.insert(t1.remove_red());
		if let Some(t_red) = t1.make_red() {
			result.insert(t_red);
		}
		result
	}
}

macro_rules! hand_into_scorable_hands {
	(@count) => { 0 };
	(@count $ma:tt) => { 1 };
	(@count $ma:tt $mb:tt) => { 2 };
	(@count $ma:tt $mb:tt $mc:tt) => { 3 };

	($(
		Hand<$nt:literal, $nm:literal>::fn into_scorable_hands() -> #[size_of = $size:literal] struct $iter:ident { [$($m_existing:ident),*] + [$($m_new:ident),*] },
	)*) => {
		$(
			impl Hand<$nt, $nm> {
				/// Add the given drawn / called tile to this hand and convert it into an [`Iterator`] of [`ScorableHandRegular`]s.
				///
				/// Note that a `ScorableHandRegular` is defined as a hand that has a winning shape,
				/// but does not necessarily have any yaku and so may not necessarily win the round.
				/// This is because the determination of whether a hand can win or not depends on external factors
				/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHandRegular`.
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
				pub fn into_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> $iter {
					let Self(ts, ms) = self;
					let lookup = ts.insert(new_tile).map_or_default(|ts| {
						let lookup = Lookup::new(&ts);
						LookupForNewTile::new(lookup, new_tile, tsumo_or_ron)
					});
					let mut ms = ms.map(Into::into);
					SortingNetwork::sort(&mut ms);
					let [$($m_existing),*] = ms;
					$iter { lookup, $($m_existing),* }
				}
			}

			#[doc = concat!("An [`Iterator`] of [`ScorableHand`]s that can be created from the original [`Hand<", stringify!($nt), ", ", stringify!($nm), ">`] and the given drawn / called tile.")]
			#[derive(Clone, Debug)]
			pub struct $iter {
				lookup: LookupForNewTile<{ ($nt - 4) / 3 }>,
				$($m_existing : ScorableHandMeld ,)*
			}

			assert_size_of!($iter, $size);

			impl Iterator for $iter {
				type Item = ScorableHandRegular;

				fn next(&mut self) -> Option<Self::Item> {
					let ([$($m_new),*], md, pair) = self.lookup.next()?;
					let (m1, m2, m3, m4) =
						if let Some(md) = md.to_tanki() {
							let mut ms = [$(self.$m_existing ,)* $($m_new ,)* md];
							merge_sorted::<_, { hand_into_scorable_hands!(@count $($m_existing)*) }, { hand_into_scorable_hands!(@count $($m_new)* md) }>(&mut ms);
							let [m1, m2, m3, m4] = ms;
							(m1, m2, m3, ScorableHandFourthMeld::tanki(m4))
						}
						else {
							let mut ms = [$(self.$m_existing ,)* $($m_new),*];
							merge_sorted::<_, { hand_into_scorable_hands!(@count $($m_existing)*) }, { hand_into_scorable_hands!(@count $($m_new)*) }>(&mut ms);
							let [m1, m2, m3] = ms;
							(m1, m2, m3, md)
						};
					Some(ScorableHandRegular { pair, m1, m2, m3, m4 })
				}

				fn size_hint(&self) -> (usize, Option<usize>) {
					self.lookup.size_hint()
				}
			}

			impl core::iter::FusedIterator for $iter {}
		)*
	};
}

hand_into_scorable_hands! {
	Hand<4, 3>::fn into_scorable_hands() -> #[size_of = 56] struct Hand4ScorableHands { [ma, mb, mc] + [] },
	Hand<7, 2>::fn into_scorable_hands() -> #[size_of = 64] struct Hand7ScorableHands { [ma, mb] + [mc] },
	Hand<10, 1>::fn into_scorable_hands() -> #[size_of = 80] struct Hand10ScorableHands { [ma] + [mb, mc] },
}

macro_rules! hand_tenpai {
	($(
		Hand<$nt:literal, $nm:literal>::fn tenpai() -> Tile37Set,
	)*) => {
		$(
			impl Hand<$nt, $nm> {
				/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
				///
				/// If the hand is not in tenpai then there is no such tile, so the set will be empty.
				pub fn tenpai(self) -> Tile37Set {
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
					lookup_tenpai(ts)
				}
			}
		)*
	};
}

hand_tenpai! {
	Hand<4, 3>::fn tenpai() -> Tile37Set,
	Hand<7, 2>::fn tenpai() -> Tile37Set,
	Hand<10, 1>::fn tenpai() -> Tile37Set,
}

impl Hand<13, 0> {
	/// Add the given drawn / called tile to this hand and convert it into an [`Iterator`] of [`ScorableHand`]s.
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
	pub fn into_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Hand13ScorableHands {
		let Self(ts13, []) = self;

		let (kokushi_musou_or_chiitoi, lookup) = ts13.clone().insert(new_tile).map_or_default(|ts14| {
			let kokushi_musou = ScorableHandKokushiMusou::new(&ts13, new_tile, tsumo_or_ron);
			let chiitoi =
				if let Some((pairs, wait)) = to_chiitoi(&ts13) && let Some(p7) = ScorableHandPair::new(wait, new_tile) {
					Some(ScorableHandChiitoi { pairs, p7, tsumo_or_ron })
				}
				else {
					None
				};
			let kokushi_musou_or_chiitoi = match (kokushi_musou, chiitoi) {
				// SAFETY: A hand cannot be both kokushi musou and chiitoi.
				(Some(_), Some(_)) => unsafe { core::hint::unreachable_unchecked(); },
				(Some(h), None) => Some(ScorableHand::KokushiMusou(h)),
				(None, Some(h)) => Some(ScorableHand::Chiitoi(h)),
				(None, None) => None,
			};

			let lookup = Lookup::new(&ts14);
			let lookup = LookupForNewTile::new(lookup, new_tile, tsumo_or_ron);

			(kokushi_musou_or_chiitoi, lookup)
		});

		Hand13ScorableHands { kokushi_musou_or_chiitoi, lookup }
	}

	/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then there is no such tile, so the set will be empty.
	pub fn tenpai(self) -> Tile37Set {
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

		let mut result = lookup_tenpai(ts.clone());

		match ToKokushiMusou::new(&ts) {
			ToKokushiMusou::Invalid => (),
			ToKokushiMusou::Single { wait, .. } => { result.insert(wait); },
			ToKokushiMusou::Any => result |= Tile37Set::TERMINALS_AND_HONORS,
		}

		if let ToChiitoiInner::SingleUnpaired { unpaired, .. } = ToChiitoiInner::new(ts.as_ref()) {
			result.insert(unpaired.remove_red());
			if let Some(unpaired) = unpaired.make_red() && !ts.contains(unpaired) {
				result.insert(unpaired);
			}
		}

		result
	}
}

/// An [`Iterator`] of [`ScorableHand`]s that can be created from the original [`Hand<13, 0>`] and the given drawn / called tile.
#[derive(Clone, Debug)]
pub struct Hand13ScorableHands {
	kokushi_musou_or_chiitoi: Option<ScorableHand>,
	lookup: LookupForNewTile<3>,
}

assert_size_of!(Hand13ScorableHands, 104);

impl Iterator for Hand13ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou_or_chiitoi.take() {
			return Some(h);
		}

		let ([m1, m2, m3], m4, pair) = self.lookup.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular { pair, m1, m2, m3, m4 }))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let extra = usize::from(self.kokushi_musou_or_chiitoi.is_some());
		let (lo, hi) = self.lookup.size_hint();
		(extra + lo, hi.map(|hi| extra + hi))
	}
}

impl core::iter::FusedIterator for Hand13ScorableHands {}

impl Hand<14, 0> {
	/// Convert this hand into an [`Iterator`] of [`ScorableHand`]s by considering each tile as a new tile.
	///
	/// This is used for rulesets where tenhou can be won by considering any tile of the starting hand as the new tile.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	/// For the same reason, the order of elements in the iterator is arbitrary and does not correspond to the scorable hands' scores.
	/// Of course, in this case the hand already has the yaku of tenhou at least.
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
	pub fn into_scorable_hands(self) -> Hand14ScorableHands {
		let Self(ts, []) = self;

		let kokushi_musou = ToKokushiMusou::tenhou(&ts);
		let chiitoi = tenhou_to_chiitoi(&ts);
		let kokushi_musou_or_chiitoi = match (kokushi_musou, chiitoi) {
			// SAFETY: A hand cannot be both kokushi musou and chiitoi.
			(Some(_), Some(_)) => unsafe { core::hint::unreachable_unchecked(); },
			(Some(h), None) => Some(ScorableHand::KokushiMusou(h)),
			(None, Some(h)) => Some(ScorableHand::Chiitoi(h)),
			(None, None) => None,
		};

		let regular = LookupForTenhou::new(&ts);

		Hand14ScorableHands {
			kokushi_musou_or_chiitoi,
			regular,
		}
	}
}

#[derive(Clone, Debug)]
pub struct Hand14ScorableHands {
	kokushi_musou_or_chiitoi: Option<ScorableHand>,
	regular: LookupForTenhou,
}

assert_size_of!(Hand14ScorableHands, 128);

impl Iterator for Hand14ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou_or_chiitoi.take() {
			return Some(h);
		}

		let ([m1, m2, m3], m4, pair) = self.regular.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular { pair, m1, m2, m3, m4 }))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let extra = usize::from(self.kokushi_musou_or_chiitoi.is_some());
		let (regular_lo, regular_hi) = self.regular.size_hint();
		(extra + regular_lo, regular_hi.and_then(|regular_hi| extra.checked_add(regular_hi)))
	}
}

impl core::iter::FusedIterator for Hand14ScorableHands {}

impl HandMeld {
	/// Construct a `HandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub const fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Ankan(t))
	}

	/// Construct a `HandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub const fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Minkan(t))
	}

	/// Construct a `HandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub const fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Minkou(t))
	}

	/// Construct a `HandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Minjun(t))
	}

	/// Parses a meld from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
	/// See `extended-mpsz.md` in the root of this repo.
	///
	/// Note that this library does not retain information about which tile was called or which player it was called from.
	/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
	/// but the order of the tiles and the position of the marker within the meld
	/// (which identify the tile that was called and who it was called from) are ignored.
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
		match *self {
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
/// See `extended-mpsz.md` in the root of this repo.
///
/// Note that `HandMeld` does not retain information about which tile was called or which player it was called from.
/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
/// but the order of the tiles and the position of the marker within the meld
/// (which identify the tile that was called and who it was called from) are ignored.
impl core::str::FromStr for HandMeld {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (result, _) = Self::parse_until(s.as_ref(), None)?;
		Ok(result)
	}
}

impl HandStable {
	/// Draw the given tile into this stable hand to form a tentative hand.
	pub fn draw(self, new_tile: Tile) -> Option<HandTentative> {
		Some(match self {
			Self::One(h) => h.draw(new_tile)?.into(),
			Self::Four(h) => h.draw(new_tile)?.into(),
			Self::Seven(h) => h.draw(new_tile)?.into(),
			Self::Ten(h) => h.draw(new_tile)?.into(),
			Self::Thirteen(h) => h.draw(new_tile)?.into(),
		})
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
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
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
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> HandMinjuns {
		match self {
			Self::One(_) => HandMinjuns::One,
			Self::Four(h) => HandMinjuns::Four(h.find_minjuns(new_tile)),
			Self::Seven(h) => HandMinjuns::Seven(h.find_minjuns(new_tile)),
			Self::Ten(h) => HandMinjuns::Ten(h.find_minjuns(new_tile)),
			Self::Thirteen(h) => HandMinjuns::Thirteen(h.find_minjuns(new_tile)),
		}
	}

	/// Add the given drawn / called tile to this hand and convert it into an [`Iterator`] of [`ScorableHand`]s.
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
	pub fn into_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> HandScorableHands {
		match self {
			Self::One(h) => HandScorableHands::One(h.into_scorable_hand(new_tile, tsumo_or_ron).into_iter()),
			Self::Four(h) => HandScorableHands::Four(h.into_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Seven(h) => HandScorableHands::Seven(h.into_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Ten(h) => HandScorableHands::Ten(h.into_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Thirteen(h) => HandScorableHands::Thirteen(h.into_scorable_hands(new_tile, tsumo_or_ron)),
		}
	}

	/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then there is no such tile, so the set will be empty.
	pub fn tenpai(self) -> Tile37Set {
		match self {
			Self::One(h) => h.tenpai(),
			Self::Four(h) => h.tenpai(),
			Self::Seven(h) => h.tenpai(),
			Self::Ten(h) => h.tenpai(),
			Self::Thirteen(h) => h.tenpai(),
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
/// See `extended-mpsz.md` in the root of this repo.
///
/// Note that [`HandMeld`] does not retain information about which tile was called or which player it was called from.
/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
/// but the order of the tiles and the position of the marker within the meld
/// (which identify the tile that was called and who it was called from) are ignored.
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
/// assert_eq!(h, HandStable::Seven(make_hand!(4m 4m 7m 7m 1p E E { minjun 7m 6m 8m } { minjun 5s 4s 6s })));
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
/// assert_eq!(h, HandStable::Seven(make_hand!(1p 3p 0p 9p 7s 8s 9s { minkan Wh Wh Wh Wh } { minjun 5p 4p 6p })));
/// ```
impl core::str::FromStr for HandStable {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (ts, ts_type, s) = Tile::parse_run_until::<13>(s.as_ref(), Some(b' '))?;
		if ts_type.is_some() {
			return Err(());
		}

		Ok(match ts[..] {
			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] => {
				if !s.is_empty() {
					return Err(());
				}
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13]).ok_or(())?,
					[],
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10] => {
				let (m1, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]).ok_or(())?,
					[m1],
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5, t6, t7]).ok_or(())?,
					[m1, m2],
				).into()
			},

			[t1, t2, t3, t4] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4]).ok_or(())?,
					[m1, m2, m3],
				).into()
			},

			[t1] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m4, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1]).ok_or(())?,
					[m1, m2, m3, m4],
				).into()
			},

			_ => return Err(()),
		})
	}
}

impl HandTentative {
	/// Discard the given tile from this hand.
	///
	/// Returns the hand resulting from the discard of that tile.
	/// If the given tile is not present in this hand, then this function returns `None`.
	pub fn discard(self, tile: Tile) -> Option<HandStable> {
		match self {
			Self::Two(h) => { let h = h.discard(tile)?; Some(h.into()) },
			Self::Five(h) => { let h = h.discard(tile)?; Some(h.into()) },
			Self::Eight(h) => { let h = h.discard(tile)?; Some(h.into()) },
			Self::Eleven(h) => { let h = h.discard(tile)?; Some(h.into()) },
			Self::Fourteen(h) => { let h = h.discard(tile)?; Some(h.into()) },
		}
	}

	/// Finds all possible ankans (quad via kan call on a quad in the hand).
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
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
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
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

/// Parses a `HandTentative` from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
/// See `extended-mpsz.md` in the root of this repo.
///
/// Note that [`HandMeld`] does not retain information about which tile was called or which player it was called from.
/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
/// but the order of the tiles and the position of the marker within the meld
/// (which identify the tile that was called and who it was called from) are ignored.
///
/// Also, since the result of this parse is a `HandTentative`, the input string should include the newly drawn tile.
/// For example, in a hand that has not made any calls, the input string should specify 14 tiles, not 13.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{
/// #     HandTentative,
/// #     make_hand,
/// # };
/// #
/// // chii, chii
/// let h: HandTentative = "4477m1p11z2z 7-68m 5-46s".parse().unwrap();
/// assert_eq!(h, HandTentative::Eight(make_hand!(4m 4m 7m 7m 1p E E S { minjun 7m 6m 8m } { minjun 5s 4s 6s })));
///
/// // pon
/// let h: HandTentative = "35m3378p3467s2z 2-22m".parse().unwrap();
/// assert_eq!(h, HandTentative::Eleven(make_hand!(3m 5m 3p 3p 7p 8p 3s 4s 6s 7s S { minkou 2m 2m 2m })));
///
/// // chii, shouminkan
/// let h: HandTentative = "3377p678s2z 2-34s 2=222m".parse().unwrap();
/// assert_eq!(h, HandTentative::Eight(make_hand!(3p 3p 7p 7p 6s 7s 8s S { minjun 2s 3s 4s } { minkan 2m 2m 2m 2m })));
///
/// // daiminkan, chii
/// let h: HandTentative = "1309p789s2z 5555-z 5-46p".parse().unwrap();
/// assert_eq!(h, HandTentative::Eight(make_hand!(1p 3p 0p 9p 7s 8s 9s S { minkan Wh Wh Wh Wh } { minjun 5p 4p 6p })));
/// ```
impl core::str::FromStr for HandTentative {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (ts, ts_type, s) = Tile::parse_run_until::<14>(s.as_ref(), Some(b' '))?;
		if ts_type.is_some() {
			return Err(());
		}

		Ok(match ts[..] {
			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14] => {
				if !s.is_empty() {
					return Err(());
				}
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14]).ok_or(())?,
					[],
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] => {
				let (m1, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]).ok_or(())?,
					[m1],
				).into()
			},

			[t1, t2, t3, t4, t5, t6, t7, t8] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5, t6, t7, t8]).ok_or(())?,
					[m1, m2],
				).into()
			},

			[t1, t2, t3, t4, t5] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2, t3, t4, t5]).ok_or(())?,
					[m1, m2, m3],
				).into()
			},

			[t1, t2] => {
				let (m1, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m2, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m3, s) = HandMeld::parse_until(s, Some(b' '))?;
				let (m4, _) = HandMeld::parse_until(s, None)?;
				Hand(
					Tile37CountedMultiSet::new(&[t1, t2]).ok_or(())?,
					[m1, m2, m3, m4],
				).into()
			},

			_ => return Err(()),
		})
	}
}

macro_rules! hand_enum_from {
	($($nt:expr, $nm:expr => $ty:tt :: $variant:ident ,)*) => {
		$(
			const impl From<Hand<$nt, $nm>> for $ty {
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

/// An [`Iterator`] of [`Hand<{ NT - 4 }, { NM + 1 }>`] values formed by creating an ankan in the given hand.
#[derive(Debug)]
pub struct Ankans<const NT: usize, const NM: usize> {
	ts: Tile37MultiSet,
	ms: [HandMeld; NM],
	tiles: Tile34SetIntoIter,
}

impl<const NT: usize, const NM: usize> Ankans<NT, NM> {
	fn new(Hand(ts, ms): Hand<NT, NM>) -> Self {
		let ts = Tile37MultiSet::from(ts);
		let tiles = Tile34Set::atleast_four(&Tile34MultiSet::from(ts.clone()));
		Self {
			ts,
			ms,
			tiles: tiles.into_iter(),
		}
	}
}

impl<const NT: usize, const NM: usize> Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
{
	fn next_inner(&mut self, t_kan: Tile) -> Hand<{ NT - 4 }, { NM + 1 }> {
		fn m(ts: &mut Tile37MultiSet, t_kan: Tile) -> HandMeld {
			let count_t_kan = ts.remove_all(t_kan);
			let t_red = t_kan.make_red().unwrap_or(t_kan);
			let count_t_red = ts.remove_all(t_red);
			debug_assert_eq!(count_t_kan + count_t_red, 4);

			let m = HandMeld::ankan(t_kan, t_kan, t_kan, t_red);
			m.unwrap()
		}

		// Note: `ts` and `ms` are copies of `self.ts` and `self.ms`, because we want to yield new hands, not mutate the original one.
		let (mut ts, ms) = (self.ts.clone(), self.ms);

		let m = m(&mut ts, t_kan);

		let ts = ts.try_into();
		// SAFETY: Exactly 4 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		Hand(ts, append(ms, m))
	}
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<const NT: usize, const NM: usize> Clone for Ankans<NT, NM> {
	fn clone(&self) -> Self {
		Self {
			ts: self.ts.clone(),
			ms: self.ms,
			tiles: self.tiles.clone(),
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
		let t_kan = self.tiles.next()?;
		let h = self.next_inner(t_kan);
		Some(h)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.tiles.size_hint()
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		let t_kan = self.tiles.next_back()?;
		let h = self.next_inner(t_kan);
		Some(h)
	}
}

impl<const NT: usize, const NM: usize> ExactSizeIterator for Ankans<NT, NM>
where
	Self: Iterator,
{
	fn len(&self) -> usize {
		self.tiles.len()
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Ankans<NT, NM>
where
	Self: Iterator,
{}

unsafe impl<const NT: usize, const NM: usize> core::iter::TrustedLen for Ankans<NT, NM>
where
	Self: Iterator,
{}

/// An [`Iterator`] of [`HandStable`] values formed by creating an ankan in the given hand.
#[derive(Debug)]
#[derive_const(Clone)]
pub enum HandAnkans {
	Two,
	Five(Ankans<5, 3>),
	Eight(Ankans<8, 2>),
	Eleven(Ankans<11, 1>),
	Fourteen(Ankans<14, 0>),
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

impl DoubleEndedIterator for HandAnkans {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self {
			Self::Two => None,
			Self::Five(inner) => inner.next_back().map(Into::into),
			Self::Eight(inner) => inner.next_back().map(Into::into),
			Self::Eleven(inner) => inner.next_back().map(Into::into),
			Self::Fourteen(inner) => inner.next_back().map(Into::into),
		}
	}
}

impl ExactSizeIterator for HandAnkans {
	fn len(&self) -> usize {
		match self {
			Self::Two => 0,
			Self::Five(inner) => inner.len(),
			Self::Eight(inner) => inner.len(),
			Self::Eleven(inner) => inner.len(),
			Self::Fourteen(inner) => inner.len(),
		}
	}
}

impl core::iter::FusedIterator for HandAnkans {}

unsafe impl core::iter::TrustedLen for HandAnkans {}

fn find_daiminkan<const N: usize>(
	ts: Tile37CountedMultiSet<N>,
	new_tile: Tile,
) -> Option<(Tile37CountedMultiSet<{ ((N - 1) - 1) - 1 }>, HandMeld)> {
	let new_tile = new_tile.remove_red();

	let mut ts = Tile37MultiSet::from(ts);

	let count_new_tile = ts.remove_all(new_tile);
	let new_tile_red = new_tile.make_red().unwrap_or(new_tile);
	let count_new_tile_red = ts.remove_all(new_tile_red);

	if count_new_tile + count_new_tile_red != 3 {
		return None;
	}

	let ts = ts.try_into();
	// SAFETY: Exactly 3 elements were removed from `ts`.
	let ts = unsafe { ts.unwrap_unchecked() };

	let m = HandMeld::minkan(new_tile, new_tile, new_tile, new_tile_red);
	let m = unsafe { m.unwrap_unchecked() };

	Some((ts, m))
}

/// An [`Iterator`] of [`Hand<{ NT - 1 }, NM>`] values formed by creating a shouminkan in the given hand.
#[derive_const(Clone)]
#[derive(Debug)]
pub struct Shouminkans<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	i: u8,
}

impl<const NT: usize, const NM: usize> Shouminkans<NT, NM> {
	const fn new(hand: Hand<NT, NM>) -> Self {
		Self { hand, i: 0 }
	}
}

impl<const NT: usize, const NM: usize> Iterator for Shouminkans<NT, NM>
where
	[(); NT - 1]:,
{
	type Item = Hand<{ NT - 1 }, NM>;

	fn next(&mut self) -> Option<Self::Item> {
		// Note: `ts` and `ms` are copies of `self.hand`, because we want to yield new hands, not mutate `self.hand`.
		let Hand(ts, mut ms) = self.hand.clone();

		loop {
			let m = ms.get_mut(usize::from(self.i))?;
			self.i += 1;
			let HandMeld::Minkou(t) = *m else { continue; };
			let (t4, ts) =
				if let t_non_red = t.remove_red() && let Some(ts) = ts.clone().remove(t_non_red) {
					(t_non_red, ts)
				}
				else if let Some(t_red) = t.make_red() && let Some(ts) = ts.clone().remove(t_red) {
					(t_red, ts)
				}
				else {
					continue;
				};
			let m_ = HandMeld::minkan(t, t, t, t4);
			// SAFETY: Three tiles of a kou with a fourth tile that is equal to the kou's tiles necessarily form a valid kan.
			*m = unsafe { m_.unwrap_unchecked() };
			return Some(Hand(ts, ms));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		(0, Some(self.hand.1.len() - usize::from(self.i)))
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Shouminkans<NT, NM>
where
	[(); NT - 1]:,
{}

/// An [`Iterator`] of [`HandStable`] values formed by creating an shouminkan in the given hand.
#[derive(Debug)]
#[derive_const(Clone)]
pub enum HandShouminkans {
	Two(Shouminkans<2, 4>),
	Five(Shouminkans<5, 3>),
	Eight(Shouminkans<8, 2>),
	Eleven(Shouminkans<11, 1>),
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

impl core::iter::FusedIterator for HandShouminkans {}

/// An [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`] values formed by creating a minkou in the given hand using the given new tile.
/// Along with the `Hand`, the iterator element contains a set of tiles in the resulting hand that are allowed to be discarded.
/// Tiles that are not present in this list are not allowed to be discarded due to kuikae-nashi.
#[derive(Clone, Debug)]
pub struct Minkous<const NT: usize, const NM: usize>
where
	[(); (NT - 1) - 1]:,
{
	ms: [HandMeld; NM],
	new_tile: Tile,
	t_ts1: Option<(Tile, Tile37CountedMultiSet<{ (NT - 1) - 1 }>)>,
	t_ts2: Option<(Tile, Tile37CountedMultiSet<{ (NT - 1) - 1 }>)>,
}

impl<const NT: usize, const NM: usize> Minkous<NT, NM>
where
	[(); (NT - 1) - 1]:,
{
	fn new(Hand(ts, ms): Hand<NT, NM>, new_tile: Tile) -> Self {
		let t1 = new_tile.remove_red();
		let (t_ts1, t_ts2) =
			if let Some(ts) = ts.remove(t1) {
				let t_ts1 = ts.clone().remove(t1).map(|ts| {
					let t = Tile::kou_representative(t1, t1, new_tile);
					(t.unwrap(), ts)
				});
				let t_ts2 =
					if let Some(t_red) = new_tile.make_red() {
						ts.remove(t_red).map(|ts| {
							let t = Tile::kou_representative(t1, t_red, new_tile);
							(t.unwrap(), ts)
						})
					}
					else {
						None
					};
				(t_ts1, t_ts2)
			}
			else {
				(None, None)
			};
		Self {
			ms,
			new_tile,
			t_ts1,
			t_ts2,
		}
	}
}

impl<const NT: usize, const NM: usize> Minkous<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	fn next_inner(&mut self, t: Tile, ts: Tile37CountedMultiSet<{ (NT - 1) - 1 }>) -> Option<(Hand<{ (NT - 1) - 1 }, { NM + 1 }>, Tile37Set)> {
		fn allowed_discards(ts: &Tile37MultiSet, new_tile: Tile) -> Option<Tile37Set> {
			let mut allowed_discards = Tile37Set::from(ts);
			allowed_discards.remove_ignore_red(new_tile);
			(!allowed_discards.is_empty()).then_some(allowed_discards)
		}

		let allowed_discards = allowed_discards(ts.as_ref(), self.new_tile)?;
		Some((Hand(ts, append(self.ms, HandMeld::Minkou(t))), allowed_discards))
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minkous<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	type Item = (Hand<{ (NT - 1) - 1 }, { NM + 1 }>, Tile37Set);

	fn next(&mut self) -> Option<Self::Item> {
		if let Some((t, ts)) = self.t_ts1.take() && let Some((hand, allowed_discards)) = self.next_inner(t, ts) {
			return Some((hand, allowed_discards));
		}
		if let Some((t, ts)) = self.t_ts2.take() && let Some((hand, allowed_discards)) = self.next_inner(t, ts) {
			return Some((hand, allowed_discards));
		}
		None
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let hi = usize::from(self.t_ts1.is_some()) + usize::from(self.t_ts2.is_some());
		(0, Some(hi))
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Minkous<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		if let Some((t, ts)) = self.t_ts2.take() && let Some((hand, allowed_discards)) = self.next_inner(t, ts) {
			return Some((hand, allowed_discards));
		}
		if let Some((t, ts)) = self.t_ts1.take() && let Some((hand, allowed_discards)) = self.next_inner(t, ts) {
			return Some((hand, allowed_discards));
		}
		None
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minkous<NT, NM>
where
	[(); (NT - 1) - 1]:,
	Self: Iterator,
{}

/// An [`Iterator`] of [`HandTentative`] values formed by creating a minkou in the given hand using the given new tile.
/// Along with the `HandTentative`, the iterator element contains a set of tiles in the resulting hand that are allowed to be discarded.
/// Tiles that are not present in this list are not allowed to be discarded due to kuikae-nashi.
#[derive(Clone, Debug)]
pub enum HandMinkous {
	One,
	Four(Minkous<4, 3>),
	Seven(Minkous<7, 2>),
	Ten(Minkous<10, 1>),
	Thirteen(Minkous<13, 0>),
}

impl Iterator for HandMinkous {
	type Item = (HandTentative, Tile37Set);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Seven(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Ten(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
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

impl DoubleEndedIterator for HandMinkous {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Seven(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Ten(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Thirteen(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
		}
	}
}

impl core::iter::FusedIterator for HandMinkous {}

/// An [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`] values formed by creating a minjun in the given hand using the given new tile.
/// Along with the `Hand`, the iterator element contains a set of tiles in the resulting hand that are allowed to be discarded.
/// Tiles that are not present in this list are not allowed to be discarded due to kuikae-nashi.
#[derive(Clone, Debug)]
pub struct Minjuns<const NT: usize, const NM: usize>
where
	[(); (NT - 1) - 1]:,
{
	ms: [HandMeld; NM],
	inner: core::array::IntoIter<(Tile37CountedMultiSet<{ (NT - 1) - 1 }>, ShunLowTileAndHasFiveRed, Tile37Set), 5>,
}

impl<const NT: usize, const NM: usize> Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
{
	fn new(Hand(ts, ms): Hand<NT, NM>, new_tile: NumberTile) -> Self {
		fn new_inner(
			ts: &Tile37MultiSet,
			new_tile: NumberTile,
		) -> (NumberSuit, u64, [u8; 9], [u32; 9], [Option<NumberTile>; 9]) {
			// |  first   |  second  |  third   | -> | other1  | other2  | new_tile
			// +==========+==========+==========+====+=========+=========+==========
			// | tm2      | tm1      | new_tile | -> | tm2     | tm1     | 34506789
			// | tm2      | tm1_red  | new_tile | -> | tm2     | tm1_red | 6
			// | tm2_red  | tm1      | new_tile | -> | tm2_red | tm1     | 7
			// | tm1      | new_tile | t1       | -> | tm1     | t1      | 23450678
			// | tm1      | new_tile | t1_red   | -> | tm1     | t1_red  | 4
			// | tm1_red  | new_tile | t1       | -> | tm1_red | t1      | 6
			// | new_tile | t1       | t2       | -> | t1      | t2      | 12345067
			// | new_tile | t1       | t2_red   | -> | t1      | t2_red  | 3
			// | new_tile | t1_red   | t2       | -> | t1_red  | t2      | 4
			const IS_VALID: [u16; 9] = {
				let mut result = [0_u16; 9];
				let mut i = 0;
				while i < result.len() {
					let number = i + 1;
					result[i] =
						(u16::from(number >= 3)) |
						(u16::from(number == 6) << 1) |
						(u16::from(number == 7) << 2) |
						(u16::from(number >= 2 && number <= 8) << 3) |
						(u16::from(number == 4) << 4) |
						(u16::from(number == 6) << 5) |
						(u16::from(number <= 7) << 6) |
						(u16::from(number == 3) << 7) |
						(u16::from(number == 4) << 8);
					i += 1;
				}
				result
			};

			let NumberTileClassified { number, suit } = new_tile.into();
			let suit_start = new_tile as u8 - number as u8;

			let new_tile_non_red = Tile::from(new_tile).remove_red();

			let t_other1s =
				t_others(
					new_tile_non_red,
					// new_tile - t_other1
					[-4, -4, -4, -2, -2, -2, 2, 2, 2],
					// t_other1.is_red()
					[false, false, true, false, false, true, false, false, true],
				);
			let t_other2s =
				t_others(
					new_tile_non_red,
					// new_tile - t_other2
					[-2, -2, -2, 2, 2, 2, 4, 4, 4],
					// t_other2.is_red()
					[false, true, false, false, true, false, false, true, false],
				);
			let shun_representatives =
				t_other1s.extract::<0, 6>().resize::<9>(new_tile as u8) |
				((t_other1s | t_other2s | core::simd::Simd::splat(new_tile as u8)) & core::simd::Simd::splat(0b1));
			let shun_representatives = shun_representatives.to_array();

			let counts = core::simd::Simd::splat(ts.to_suits()[suit as usize]);
			let counts_offsets_other1 = counts_offsets(t_other1s, suit_start);
			let counts_offsets_other2 = counts_offsets(t_other2s, suit_start);
			let counts_other1 = (counts >> counts_offsets_other1) & core::simd::Simd::splat(0b111);
			let counts_other2 = (counts >> counts_offsets_other2) & core::simd::Simd::splat(0b111);

			let is_valid =
				core::simd::cmp::SimdPartialOrd::simd_gt(counts_other1, core::simd::Simd::splat(0)).cast::<i8>() &
				core::simd::cmp::SimdPartialOrd::simd_gt(counts_other2, core::simd::Simd::splat(0)).cast::<i8>();
			let is_valid = is_valid.to_bitmask();
			let is_valid = is_valid & u64::from(IS_VALID[(number as usize) >> 1]);
			unsafe { core::hint::assert_unchecked(is_valid <= 0b111111111); }

			let counts =
				counts -
				(core::simd::Simd::splat(0b1) << counts_offsets_other1) -
				(core::simd::Simd::splat(0b1) << counts_offsets_other2);
			let counts = counts.to_array();

			let cannot_discards = {
				let lo = (number >= Number::Four).then(|| unsafe { core::mem::transmute::<u8, NumberTile>(new_tile_non_red as u8 - 6) });
				let hi = (number <= Number::Six).then(|| unsafe { core::mem::transmute::<u8, NumberTile>(new_tile_non_red as u8 + 6) });
				[lo, lo, lo, None, None, None, hi, hi, hi]
			};

			(suit, is_valid, shun_representatives, counts, cannot_discards)
		}

		fn t_others(new_tile_non_red: Tile, offsets: [i8; 9], red: [bool; 9]) -> core::simd::Simd<u8, 9> {
			let offsets = core::simd::Simd::from_array(offsets);
			let red = core::simd::Mask::<i8, _>::from_array(red);
			let ts = core::simd::num::SimdInt::cast::<u8>(core::simd::Simd::splat(new_tile_non_red as i8) + offsets);
			ts | core::simd::Select::select(red, core::simd::Simd::splat(0b1), core::simd::Simd::splat(0b0))
		}

		fn counts_offsets(ts: core::simd::Simd<u8, 9>, suit_start: u8) -> core::simd::Simd<u32, 9> {
			let ns = ts - core::simd::Simd::splat(suit_start);
			let offsets =
				(ns >> 1) +
				(((ns - core::simd::Simd::splat(Number::One as u8)) + core::simd::Simd::splat(0b10000 - Number::FiveRed as u8)) >> 4);
			let offsets = offsets * core::simd::Simd::splat(3);
			core::simd::num::SimdUint::cast::<u32>(offsets)
		}

		fn allowed_discards(ts: &Tile37MultiSet, new_tile: NumberTile, cannot_discard: Option<NumberTile>) -> Option<Tile37Set> {
			let mut allowed_discards = Tile37Set::from(ts);
			allowed_discards.remove_ignore_red(new_tile.into());
			if let Some(cannot_discard) = cannot_discard {
				allowed_discards.remove_ignore_red(cannot_discard.into());
			}
			(!allowed_discards.is_empty()).then_some(allowed_discards)
		}

		let (suit, mut is_valid, shun_representatives, counts, cannot_discards) = new_inner(ts.as_ref(), new_tile);

		let mut inner = ArrayVec::new();
		while let Some(i) = is_valid.lowest_one() {
			is_valid &= !(0b1 << i);
			let i = i as usize;
			let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(shun_representatives[i]) };
			let ts = unsafe { ts.with_two_removed_from_suit(suit, counts[i]) };
			if let Some(allowed_discards) = allowed_discards(ts.as_ref(), new_tile, cannot_discards[i]) {
				let result = inner.push((ts, t, allowed_discards));
				unsafe { result.unwrap_unchecked(); }
			}
		}

		Self {
			ms,
			inner: inner.into_iter(),
		}
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	type Item = (Hand<{ (NT - 1) - 1 }, { NM + 1 }>, Tile37Set);

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, t, allowed_discards) = self.inner.next()?;
		Some((Hand(ts, append(self.ms, HandMeld::Minjun(t))), allowed_discards))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, t, allowed_discards) = self.inner.next_back()?;
		Some((Hand(ts, append(self.ms, HandMeld::Minjun(t))), allowed_discards))
	}
}

impl<const NT: usize, const NM: usize> ExactSizeIterator for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	Self: Iterator,
{
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	Self: Iterator,
{}

unsafe impl<const NT: usize, const NM: usize> core::iter::TrustedLen for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	Self: Iterator,
{}

/// An [`Iterator`] of [`HandTentative`] values formed by creating a minjun in the given hand using the given new tile.
/// Along with the `HandTentative`, the iterator element contains a set of tiles in the resulting hand that are allowed to be discarded.
/// Tiles that are not present in this list are not allowed to be discarded due to kuikae-nashi.
#[derive(Clone, Debug)]
pub enum HandMinjuns {
	One,
	Four(Minjuns<4, 3>),
	Seven(Minjuns<7, 2>),
	Ten(Minjuns<10, 1>),
	Thirteen(Minjuns<13, 0>),
}

impl Iterator for HandMinjuns {
	type Item = (HandTentative, Tile37Set);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Seven(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Ten(inner) => inner.next().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
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

impl DoubleEndedIterator for HandMinjuns {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self {
			Self::One => None,
			Self::Four(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Seven(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Ten(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
			Self::Thirteen(inner) => inner.next_back().map(|(hand, allowed_discards)| (hand.into(), allowed_discards)),
		}
	}
}

impl core::iter::FusedIterator for HandMinjuns {}

/// An [`Iterator`] of [`ScorableHand`]s that can be created from the original [`HandStable`] and the given drawn / called tile.
#[derive(Clone, Debug)]
pub enum HandScorableHands {
	One(core::option::IntoIter<ScorableHandRegular>),
	Four(Hand4ScorableHands),
	Seven(Hand7ScorableHands),
	Ten(Hand10ScorableHands),
	Thirteen(Hand13ScorableHands),
}

impl Iterator for HandScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			Self::One(inner) => Some(ScorableHand::Regular(inner.next()?)),
			Self::Four(inner) => Some(ScorableHand::Regular(inner.next()?)),
			Self::Seven(inner) => Some(ScorableHand::Regular(inner.next()?)),
			Self::Ten(inner) => Some(ScorableHand::Regular(inner.next()?)),
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

#[derive(Copy)]
#[derive_const(Clone)]
pub(crate) enum ToKokushiMusou {
	Invalid,
	Single { wait: Tile, duplicate: Tile },
	Any,
}

#[derive(Copy)]
#[derive_const(Clone)]
enum ToKokushiMusouInner {
	Invalid,
	Single { wait: Tile },
	Any,
}

impl ToKokushiMusou {
	pub(crate) fn new(ts: &Tile37CountedMultiSet<13>) -> Self {
		let (wait, duplicate) = Self::new_inner(ts.as_ref());
		match wait {
			ToKokushiMusouInner::Invalid => Self::Invalid,
			ToKokushiMusouInner::Single { wait } => {
				// SAFETY: Pigeonhole principle. To get here, twelve unique tiles were found
				// and the thirteenth tile was one of those twelve and thus written to `duplicate`.
				let duplicate = unsafe { duplicate.assume_init() };
				Self::Single { wait, duplicate }
			},
			ToKokushiMusouInner::Any => Self::Any,
		}
	}

	pub(crate) fn with_new_tile(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Option<ScorableHandKokushiMusou> {
		match self {
			Self::Invalid => None,
			Self::Single { wait, duplicate } => (wait == new_tile).then_some(ScorableHandKokushiMusou { duplicate, t14: new_tile, tsumo_or_ron }),
			Self::Any => Tile34Set::TERMINALS_AND_HONORS.contains(new_tile).then_some(ScorableHandKokushiMusou { duplicate: new_tile, t14: new_tile, tsumo_or_ron }),
		}
	}

	fn tenhou(ts: &Tile37CountedMultiSet<14>) -> Option<ScorableHandKokushiMusou> {
		let (wait, duplicate) = Self::new_inner(ts.as_ref());
		matches!(wait, ToKokushiMusouInner::Any).then(|| {
			// SAFETY: Pigeonhole principle. To get here, thirteen unique tiles were found
			// and the fourteenth tile was one of those thirteen and thus written to `duplicate`.
			let duplicate = unsafe { duplicate.assume_init() };
			ScorableHandKokushiMusou { duplicate, t14: duplicate, tsumo_or_ron: TsumoOrRon::Tsumo }
		})
	}

	fn new_inner(ts: &Tile37MultiSet) -> (ToKokushiMusouInner, core::mem::MaybeUninit<Tile>) {
		const TILES: [Tile; 13] = t![1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R];
		const LSB: u64 = 0o1_111_111_111_111;

		let mut duplicate = core::mem::MaybeUninit::uninit();

		let counts = ts.to_suits();
		if (counts[0] | counts[1] | counts[2]) & 0o0777777770 != 0 {
			return (ToKokushiMusouInner::Invalid, duplicate);
		}

		let counts =
			u64::from(counts[0] & 0b111) | (u64::from(counts[0] >> 27) << 3) |
			(u64::from(counts[1] & 0b111) << 6) | (u64::from(counts[1] >> 27) << 9) |
			(u64::from(counts[2] & 0b111) << 12) | (u64::from(counts[2] >> 27) << 15) |
			(u64::from(counts[3]) << 18);

		let b0 = counts & LSB;
		let b1 = (counts >> 1) & LSB;
		let b2 = (counts >> 2) & LSB;

		let gt1 = b1 | b2;
		if let Some(first_duplicate) = gt1.lowest_one() {
			let first_duplicate = (first_duplicate / 3) as usize;
			duplicate.write(TILES[first_duplicate]);
		}

		let eq0 = !(b0 | b1 | b2) & LSB;
		let wait =
			if let Some(first_missing) = eq0.lowest_one() {
				if eq0.is_power_of_two() {
					let first_missing = (first_missing / 3) as usize;
					ToKokushiMusouInner::Single { wait: TILES[first_missing] }
				}
				else {
					ToKokushiMusouInner::Invalid
				}
			}
			else {
				ToKokushiMusouInner::Any
			};

		(wait, duplicate)
	}
}

fn to_chiitoi(ts: &Tile37CountedMultiSet<13>) -> Option<([ScorableHandPair; 6], Tile)> {
	let ToChiitoiInner::SingleUnpaired { red_fives, pair_is, unpaired } = ToChiitoiInner::new(ts.as_ref()) else { return None; };
	let mut ps = [const { core::mem::MaybeUninit::uninit() }; 6];
	// SAFETY: Requirements satisfied by construction in `ToChiitoiInner::new`.
	unsafe { chiitoi_extract_pair_representatives(&mut ps, red_fives, pair_is); }
	let ps = unsafe { core::mem::MaybeUninit::array_assume_init(ps) };
	Some((ps, unpaired))
}

fn tenhou_to_chiitoi(ts: &Tile37CountedMultiSet<14>) -> Option<ScorableHandChiitoi> {
	let ToChiitoiInner::AllPaired { red_fives, pair_is } = ToChiitoiInner::new(ts.as_ref()) else { return None; };
	let mut ps = [const { core::mem::MaybeUninit::uninit() }; 7];
	// SAFETY: Requirements satisfied by construction in `ToChiitoiInner::new`.
	unsafe { chiitoi_extract_pair_representatives(&mut ps, red_fives, pair_is); }
	let [p1, p2, p3, p4, p5, p6, p7] = unsafe { core::mem::MaybeUninit::array_assume_init(ps) };
	Some(ScorableHandChiitoi { pairs: [p1, p2, p3, p4, p5, p6], p7, tsumo_or_ron: TsumoOrRon::Tsumo })
}

#[derive(Copy)]
#[derive_const(Clone)]
enum ToChiitoiInner {
	Invalid,
	SingleUnpaired { red_fives: [u8; 3], pair_is: u64, unpaired: Tile },
	AllPaired { red_fives: [u8; 3], pair_is: u64 },
}

impl ToChiitoiInner {
	fn new(ts: &Tile37MultiSet) -> Self {
		const LSB: u32 = 0o111_111_111;

		let ts34 = Tile34MultiSet::from(ts.clone());
		let counts = ts34.to_suits_simd();
		let counts_b0 = counts & core::simd::Simd::splat(LSB);
		let eq2 = {
			let b1 = (counts >> 1) & core::simd::Simd::splat(LSB);
			let b2 = (counts >> 2) & core::simd::Simd::splat(LSB);
			!counts_b0 & b1 & !b2
		};
		let num_pairs = core::simd::num::SimdUint::reduce_sum(core::simd::num::SimdUint::count_ones(eq2));

		if num_pairs != 6 && num_pairs != 7 {
			return Self::Invalid;
		}

		let red_fives = t![0m, 0p, 0s].map(|t| ts.get(t));

		let mut pair_is = eq2;
		for p in pair_is.as_mut_array() {
			*p = p.extract_bits(LSB);
		}
		let pair_is = core::simd::num::SimdUint::cast::<u64>(pair_is) << core::simd::Simd::from_array([0, 9, 18, 27]);
		let pair_is = core::simd::num::SimdUint::reduce_or(pair_is);

		if num_pairs == 7 {
			return Self::AllPaired { red_fives, pair_is };
		}

		// SAFETY: Since `num_pairs` is 6, `ts` is guaranteed to have contained six pairs and one unpaired tile.
		// Thus exactly one suit is guaranteed to have an odd number of tiles, ie a count with bit 0 set.
		let suit = core::simd::cmp::SimdPartialEq::simd_ne(counts_b0, core::simd::Simd::splat(0));
		let suit = suit.first_set();
		let suit = unsafe { suit.unwrap_unchecked() };
		// Micro-optimization: `first_set` asserts this bound already, except on the x86_64 specialized path,
		// so on x86_64 rustc ends up emitting a bounds check unless we assert it ourselves.
		unsafe { core::hint::assert_unchecked(suit < counts_b0.len()); }
		let offset = counts_b0[suit].trailing_zeros();
		#[expect(clippy::cast_possible_truncation)]
		let unpaired = (((suit as u8) * 9 + (offset / 3) as u8) << 1) + t!(1m) as u8;
		let unpaired = unsafe { core::mem::transmute::<u8, Tile>(unpaired) };
		let unpaired =
			if ts.contains(unpaired) { unpaired }
			else if let Some(unpaired) = unpaired.make_red() && ts.contains(unpaired) { unpaired }
			else { unsafe { core::hint::unreachable_unchecked(); } };
		Self::SingleUnpaired { red_fives, pair_is, unpaired }
	}
}

/// # Safety
///
/// Requires `pair_is <= (1 << 35) - 1` and `pair_is.count_ones() == result.len()`.
unsafe fn chiitoi_extract_pair_representatives(
	result: &mut [core::mem::MaybeUninit<ScorableHandPair>],
	red_fives: [u8; 3],
	pair_is: u64,
) {
	// TODO(rustup): Use `core::simd` once it supports register compress.
	//
	// Ref: https://github.com/rust-lang/portable-simd/issues/240

	#[cfg(not(all(target_arch = "riscv64", target_feature = "v")))]
	const PAIR_REPRESENTATIVES: [u8; 34] = {
		let mut result = [0_u8; 34];
		let mut i = 0;
		while i < result.len() {
			#[expect(clippy::cast_possible_truncation)]
			{
				result[i] = (i as u8) << 1;
			}
			i += 1;
		}
		result
	};

	cfg_select! {
		all(target_arch = "x86_64", target_feature = "avx512vbmi2") => {{
			let pair_representatives = core::simd::Simd::<u8, 64>::load_or_default(&PAIR_REPRESENTATIVES);
			let red_mask =
				(u64::from(red_fives[0]) << Tile::offset(t!(5m))) |
				(u64::from(red_fives[1]) << Tile::offset(t!(5p))) |
				(u64::from(red_fives[2]) << Tile::offset(t!(5s)));
			let red_mask = core::simd::Mask::<i8, _>::from_bitmask(red_mask);
			let pair_representatives = pair_representatives | core::simd::Select::select(red_mask, core::simd::Simd::splat(0b1), core::simd::Simd::splat(0b0));
			let ps = unsafe { core::arch::x86_64::_mm512_maskz_compress_epi8(pair_is, pair_representatives.into()) };
			let ps = core::simd::Simd::from(ps);
			let ps = ps.to_array();
			// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
			let result = unsafe { core::slice::from_raw_parts_mut(<*mut core::mem::MaybeUninit<ScorableHandPair>>::cast::<core::mem::MaybeUninit<u8>>(result.as_mut_ptr()), result.len()) };
			result.write_copy_of_slice(&ps[..result.len()]);
		}},

		all(target_arch = "riscv64", target_feature = "v") => {{
			let red_mask =
				(u64::from(red_fives[0]) << Tile::offset(t!(5m))) |
				(u64::from(red_fives[1]) << Tile::offset(t!(5p))) |
				(u64::from(red_fives[2]) << Tile::offset(t!(5s)));
			let ps: u64;
			unsafe {
				core::arch::asm!(
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vmv.s.x v0, {red_mask}",
					"vmv.s.x v1, {pair_is}",
					"vsetvli zero, {thirty_four}, e8, m{e8x34_lmul}, ta, mu",
					"vid.v v8",
					"vsll.vi v8, v8, 1",
					"vor.vi v8, v8, 1, v0.t",
					"vcompress.vm v12, v8, v1",
					"vsetivli zero, 1, e64, m1, ta, ma",
					"vmv.x.s {ps}, v12",

					red_mask = in(reg) red_mask,
					pair_is = in(reg) pair_is,
					thirty_four = in(reg) 34,
					e8x34_lmul = const cfg_select! {
						target_feature = "zvl512b" => 1,
						target_feature = "zvl256b" => 2,
						_ => 4,
					},
					ps = lateout(reg) ps,
					out("v0") _,
					out("v1") _,
					out("v8") _,
					out("v9") _,
					out("v10") _,
					out("v11") _,
					out("v12") _,
					out("v13") _,
					out("v14") _,
					out("v15") _,
					options(nomem, nostack, pure),
				);
			}
			let ps = ps.to_le_bytes();
			// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
			let result = unsafe { core::slice::from_raw_parts_mut(<*mut core::mem::MaybeUninit<ScorableHandPair>>::cast::<core::mem::MaybeUninit<u8>>(result.as_mut_ptr()), result.len()) };
			result.write_copy_of_slice(&ps[..result.len()]);
		}},

		_ => {{
			let mut pair_representatives = PAIR_REPRESENTATIVES;
			pair_representatives[usize::from(Tile::offset(t!(0m)))] |= red_fives[0];
			pair_representatives[usize::from(Tile::offset(t!(0p)))] |= red_fives[1];
			pair_representatives[usize::from(Tile::offset(t!(0s)))] |= red_fives[2];

			let mut pair_is = pair_is;
			for p in result {
				// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
				let i = pair_is.lowest_one();
				let i = unsafe { i.unwrap_unchecked() };
				pair_is &= !(0b1 << i);

				let i = i as usize;
				// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
				unsafe { core::hint::assert_unchecked(i < pair_representatives.len()); }
				let pair_representative = pair_representatives[i];
				// SAFETY: `pair_is` is a mask of the indices into `pair_representatives` which contain valid pairs.
				let pair_representative = unsafe { core::mem::transmute::<u8, Tile>(pair_representative) };
				p.write(ScorableHandPair(pair_representative));
			}
		}},
	}
}

/// Merge two individually sorted subslices into one sorted slice.
///
/// Requires that `s[..N1]` is sorted and `s[N1..]` is sorted, otherwise resulting array might not be sorted.
fn merge_sorted<T, const N1: usize, const N2: usize>(s: &mut [T; N1 + N2])
where
	T: Ord,
{
	unsafe fn minmax_mut<T>(p1: *mut T, p2: *mut T)
	where
		T: Ord,
	{
		let v1 = unsafe { core::ptr::read(p1) };
		let v2 = unsafe { core::ptr::read(p2) };
		let [v1, v2] = core::cmp::minmax(v1, v2);
		unsafe { core::ptr::write(p1, v1); }
		unsafe { core::ptr::write(p2, v2); }
	}

	if N1 <= N2 {
		for i in (0..N1).rev() {
			let s = &mut s[i..];
			for i in 0..N2 {
				unsafe { minmax_mut(&raw mut s[i], &raw mut s[i + 1]); }
			}
		}
	}
	else {
		for i in 0..N2 {
			let s = &mut s[i..];
			for i in (0..N1).rev() {
				unsafe { minmax_mut(&raw mut s[i], &raw mut s[i + 1]); }
			}
		}
	}
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	#[test]
	fn find_ankans() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		let mut ankans = h.draw(t!(E)).unwrap().find_ankans();
		assert_eq!(ankans.next().unwrap(), make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { ankan E E E E }));
		core::assert_matches!(ankans.next(), None);
	}

	#[test]
	fn find_daiminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		let h = h.find_daiminkan(t!(E)).unwrap();
		assert_eq!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E }));
	}

	#[test]
	fn find_shouminkans1() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkou E E E });
		let mut shouminkans = h.draw(t!(E)).unwrap().find_shouminkans();
		assert_eq!(shouminkans.next().unwrap(), make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E }));
		core::assert_matches!(shouminkans.next(), None);
	}

	#[test]
	fn find_shouminkans2() {
		let h = make_hand!(1m { minjun 1p 2p 3p } { minjun 4p 5p 6p } { minjun 7p 8p 9p } { minkou 5s 5s 0s });
		let mut shouminkans = h.draw(t!(5s)).unwrap().find_shouminkans();
		assert_eq!(shouminkans.next().unwrap(), make_hand!(1m { minjun 1p 2p 3p } { minjun 4p 5p 6p } { minjun 7p 8p 9p } { minkan 5s 5s 5s 0s }));
		core::assert_matches!(shouminkans.next(), None);
	}

	#[test]
	fn find_shouminkans3() {
		let h = make_hand!(1m { minjun 1p 2p 3p } { minjun 4p 5p 6p } { minjun 7p 8p 9p } { minkou 5s 5s 5s });
		let mut shouminkans = h.draw(t!(0s)).unwrap().find_shouminkans();
		assert_eq!(shouminkans.next().unwrap(), make_hand!(1m { minjun 1p 2p 3p } { minjun 4p 5p 6p } { minjun 7p 8p 9p } { minkan 5s 5s 5s 0s }));
		core::assert_matches!(shouminkans.next(), None);
	}

	#[test]
	fn find_minkous1() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(2m));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 3m 3m 3m 4m 4m 4m 5m 5m { minkou 2m 2m 2m }),
			t37set![1m, 3m, 4m, 5m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous2() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(5m));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 5m }),
			t37set![1m, 2m, 3m, 4m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous3() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(0m));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 0m }),
			t37set![1m, 2m, 3m, 4m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous4() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 0m);
		let mut minkous = h.find_minkous(t!(5m));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 0m }),
			t37set![1m, 2m, 3m, 4m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous5() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m 5m 5m);
		let mut minkous = h.find_minkous(t!(0m));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }),
			t37set![1m, 2m, 3m, 4m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous6() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m 5m 0m);
		let mut minkous = h.find_minkous(t!(5m));
		assert_eq!(minkous.size_hint(), (0, Some(2)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 0m { minkou 5m 5m 5m }),
			t37set![1m, 2m, 3m, 4m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }),
			t37set![1m, 2m, 3m, 4m],
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let mut minjuns = h.find_minjuns(tn!(4m));
		assert_eq!(minjuns.size_hint(), (5, Some(5)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 5m 0m 6m 7m 8m E E E G G { minjun 4m 2m 3m }),
			t37set![5m, 0m, 6m, 7m, 8m, E, G],
		));
		assert_eq!(minjuns.size_hint(), (4, Some(4)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 0m 6m 7m 8m E E E G G { minjun 4m 3m 5m }),
			t37set![1m, 2m, 0m, 6m, 7m, 8m, E, G],
		));
		assert_eq!(minjuns.size_hint(), (3, Some(3)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 5m 6m 7m 8m E E E G G { minjun 4m 3m 0m }),
			t37set![1m, 2m, 5m, 6m, 7m, 8m, E, G],
		));
		assert_eq!(minjuns.size_hint(), (2, Some(2)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 3m 0m 7m 8m E E E G G { minjun 4m 5m 6m }),
			t37set![1m, 2m, 3m, 0m, 8m, E, G],
		));
		assert_eq!(minjuns.size_hint(), (1, Some(1)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 3m 5m 7m 8m E E E G G { minjun 4m 0m 6m }),
			t37set![1m, 2m, 3m, 5m, 8m, E, G],
		));
		assert_eq!(minjuns.size_hint(), (0, Some(0)));
		core::assert_matches!(minjuns.next(), None);
		assert_eq!(minjuns.size_hint(), (0, Some(0)));
	}

	#[test]
	fn kuikae() {
		{
			let h = make_hand!(1m 1m 1m E E E S S S W W W N);
			let mut minkous = h.find_minkous(t!(1m));
			assert_eq!(minkous.next().unwrap(), (
				make_hand!(1m E E E S S S W W W N { minkou 1m 1m 1m }),
				t37set![E, E, E, S, S, S, W, W, W, N],
			));
			core::assert_matches!(minkous.next(), None);
		}

		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(2p));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(2p E E E S S S W W W N { minjun 2p 1p 3p }),
				t37set![E, E, E, S, S, S, W, W, W, N],
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }),
				t37set![E, E, E, S, S, S, W, W, W, N],
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }),
				t37set![E, E, E, S, S, S, W, W, W, N],
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(4m));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m E E E S S S W W W N { minjun 4m 2m 3m }),
				t37set![E, E, E, S, S, S, W, W, W, N],
			));
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
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 4m 5m 6m E E E S S S W { minjun 4m 2m 3m }),
				t37set![5m, 6m, E, S, W],
			));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 2m 4m 6m E E E S S S W { minjun 4m 3m 5m }),
				t37set![1m, 2m, 6m, E, S, W],
			));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 2m 3m 4m E E E S S S W { minjun 4m 5m 6m }),
				t37set![1m, 2m, 3m, E, S, W],
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let mut minjuns = h.find_minjuns(tn!(7m));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 2m 3m 4m E E E S S S W { minjun 7m 5m 6m }),
				t37set![1m, 2m, 3m, E, S, W],
			));
			core::assert_matches!(minjuns.next(), None);
		}
	}

	#[test]
	fn tenpai() {
		{
			let h = make_hand!(5p 6p 0s 6s 7s 8s 8s Wh Wh Wh { minkou R R R });
			assert_eq!(h.tenpai(), t37set![4p, 7p]);
		}

		{
			let h = make_hand!(4m 5m 6p 7p 8p 1s 2s 3s 4s 5s 6s 8s 8s);
			assert_eq!(h.tenpai(), t37set![3m, 6m]);
		}

		{
			let h = make_hand!(1m 1m 4p 4p { minkou N N N } { minkou 3p 3p 3p } { minkou R R R });
			assert_eq!(h.tenpai(), t37set![1m, 4p]);
		}

		{
			let h = make_hand!(1m 1m 4m 5m 6m 3p 4p 4p 0p 6p 1s 2s 3s);
			assert_eq!(h.tenpai(), t37set![2p, 5p]);
		}

		{
			let h = make_hand!(4m 4m 1p 2p 3p 0p 5p 1s 2s 3s { minjun 1m 2m 3m });
			assert_eq!(h.tenpai(), t37set![4m, 5p]);
		}

		{
			let h = make_hand!(3p 3p 4p 4p 0p 5p 7p 8p 8p 8p 9p G G);
			assert_eq!(h.tenpai(), t37set![8p, G]);
		}

		{
			let h = make_hand!(4m 0m 6m 7m 7m 4s 0s 6s 7s 8s { minjun 4p 5p 6p });
			assert_eq!(h.tenpai(), t37set![3s, 6s, 9s]);
		}

		{
			let h = make_hand!(1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m);
			assert_eq!(h.tenpai(), t37set![1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m]);
		}

		{
			let h = make_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R);
			assert_eq!(h.tenpai(), t37set![1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R]);
		}

		{
			let h = make_hand!(1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh);
			assert_eq!(h.tenpai(), t37set![S]);
		}

		// Red five
		{
			let h = make_hand!(1m 1m 2m 2m 2m 3m 3m 3m 4p 5p 5p 5p 6p);
			assert_eq!(h.tenpai(), t37set![1m, 4m, 0p]);
		}

		// Red five
		{
			let h = make_hand!(5m 5m 0m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			assert_eq!(h.tenpai(), t37set![5m, 6m, 7m, 8m]);
		}

		// Red five
		{
			let h = make_hand!(5m 5m 5m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			assert_eq!(h.tenpai(), t37set![0m, 6m, 7m, 8m]);
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand. Not considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 1m 1m 1m 3m 4m 5m 3p 4p 5p 3s 4s 5s);
			assert_eq!(h.tenpai(), t37set![]);
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand, but only 1x 1m in unmelded tiles. Considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 3m 4m 5m 3p 4p 5p 3s 4s 5s { minkou 1m 1m 1m });
			assert_eq!(h.tenpai(), t37set![1m]);
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
			assert_eq!(h.tenpai(), t37set![8p]);
		}
	}

	#[test]
	fn merge_sorted() {
		fn inner<const N1: usize, const N2: usize>(input: [u8; N1 + N2]) {
			let mut actual = input;
			super::merge_sorted::<_, N1, N2>(&mut actual);
			let mut expected = input;
			expected.sort_unstable();
			assert_eq!(actual, expected, "{input:?} sorted to {actual:?} instead of {expected:?}");
		}

		inner::<0, 1>([0]);
		inner::<1, 0>([0]);

		inner::<0, 2>([0, 1]);
		inner::<1, 1>([0, 1]);
		inner::<1, 1>([1, 0]);
		inner::<2, 0>([0, 1]);

		inner::<0, 3>([0, 1, 2]);
		inner::<1, 2>([0, 1, 2]);
		inner::<1, 2>([1, 0, 2]);
		inner::<1, 2>([2, 0, 1]);
		inner::<2, 1>([0, 1, 2]);
		inner::<2, 1>([0, 2, 1]);
		inner::<2, 1>([1, 2, 0]);
		inner::<3, 0>([0, 1, 2]);

		inner::<0, 4>([0, 1, 2, 3]);
		inner::<1, 3>([0, 1, 2, 3]);
		inner::<1, 3>([1, 0, 2, 3]);
		inner::<1, 3>([2, 0, 1, 3]);
		inner::<1, 3>([3, 0, 1, 2]);
		inner::<2, 2>([0, 1, 2, 3]);
		inner::<2, 2>([0, 2, 1, 3]);
		inner::<2, 2>([0, 3, 1, 2]);
		inner::<2, 2>([1, 2, 0, 3]);
		inner::<2, 2>([1, 3, 0, 2]);
		inner::<2, 2>([2, 3, 0, 1]);
		inner::<3, 1>([0, 1, 2, 3]);
		inner::<3, 1>([0, 1, 3, 2]);
		inner::<3, 1>([0, 2, 3, 1]);
		inner::<3, 1>([1, 2, 3, 0]);
		inner::<4, 0>([0, 1, 2, 3]);
	}
}
