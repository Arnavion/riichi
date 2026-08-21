use crate::{
	ArrayVec,
	HandMeldType,
	NumberTile,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
	ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile,
	Tile27Set,
	Tile34MultiSet, Tile34Set, Tile34SetIntoIter,
	Tile37CountedMultiSet, Tile37MultiSet, Tile37MultiSetIntoIter, Tile37Set,
	TsumoOrRon,
	decompose::{Lookup, LookupForNewTile},
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
	pub fn find_shouminkans(self) -> Shouminkans<NT, NM> {
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
	Hand<NT, NM>: core::fmt::Display,
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
		let t1 = ts.into_iter().next();
		let (t1, _) = unsafe { t1.unwrap_unchecked() };

		let pair = ScorableHandPair::new(t1, new_tile)?;
		let [ma, mb, mc, md] = ms.map(Into::into);
		Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, ScorableHandFourthMeld::tanki(md), pair)))
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

macro_rules! hand_to_scorable_hands {
	($(
		Hand<$nt:literal, $nm:literal>::fn to_scorable_hands() -> #[size_of = $size:literal] struct $iter:ident { [$($m_existing:ident),*] + [$($m_new:ident),*] },
	)*) => {
		$(
			impl Hand<$nt, $nm> {
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
				pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> $iter {
					let Self(ts, ms) = self;
					let lookup = ts.insert(new_tile).map(|ts| {
						let lookup = Lookup::new(&ts);
						LookupForNewTile::new(lookup, new_tile, tsumo_or_ron)
					}).unwrap_or_default();
					let [$($m_existing),*] = ms.map(Into::into);
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
				type Item = ScorableHand;

				fn next(&mut self) -> Option<Self::Item> {
					let ([$($m_new),*], md, pair) = self.lookup.next()?;
					Some(ScorableHand::Regular(ScorableHandRegular::new($(self. $m_existing ,)* $($m_new ,)* md, pair)))
				}

				fn size_hint(&self) -> (usize, Option<usize>) {
					self.lookup.size_hint()
				}
			}

			impl core::iter::FusedIterator for $iter {}
		)*
	};
}

hand_to_scorable_hands! {
	Hand<4, 3>::fn to_scorable_hands() -> #[size_of = 112] struct Hand4ScorableHands { [ma, mb, mc] + [] },
	Hand<7, 2>::fn to_scorable_hands() -> #[size_of = 120] struct Hand7ScorableHands { [ma, mb] + [mc] },
	Hand<10, 1>::fn to_scorable_hands() -> #[size_of = 144] struct Hand10ScorableHands { [ma] + [mb, mc] },
}

macro_rules! hand_tenpai {
	($(
		Hand<$nt:literal, $nm:literal>::fn tenpai() -> Tile37Set,
	)*) => {
		$(
			impl Hand<$nt, $nm> {
				/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
				///
				/// If the hand is not in tenpai then then there is no such tile, so the set will be empty.
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
					let mut result = ts.as_ref().tenpai();
					result.retain(|new_tile| {
						// TODO(rustup): Workaround for const-eval error if it's inlined as `Lookup::<{ ($nt - 1) / 3 }>`
						const WORKAROUND: usize = ($nt - 1) / 3;

						ts.clone().insert(new_tile).is_some_and(|ts| Lookup::<WORKAROUND>::new(&ts).len() > 0)
					});
					result
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
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Hand13ScorableHands {
		let Self(ts, []) = self;

		let kokushi_musou = ToKokushiMusou::new(&ts).with_new_tile(new_tile);
		let chiitoi =
			if let Some((ps, wait)) = to_chiitoi(&ts) && let Some(p7) = ScorableHandPair::new(wait, new_tile) {
				// `ps` is in sorted order and is guaranteed to not contain any pair that is the same as the one formed by `wait`.
				// So `ps` will contain all elements less than `p7` followed by all elements greater than `p7`.

				let ps = core::simd::Simd::from_array(ps.map(|p| p.0 as u8));
				let ps = ps.resize::<7>(t!(R) as u8);
				let lt = core::simd::cmp::SimdPartialOrd::simd_lt(ps, core::simd::Simd::splat(p7.0 as u8));

				let ps_shifted = ps.shift_elements_right::<1>(t!(1m) as u8);
				let pairs = core::simd::Select::select(lt, ps, ps_shifted);

				let insert_mask = core::simd::Mask::<i8, _>::from_bitmask(lt.to_bitmask() + 1);
				let pairs = core::simd::Select::select(insert_mask, core::simd::Simd::splat(p7.0 as u8), pairs);

				let pairs = pairs.to_array();
				// SAFETY: All elements of `ps` and `ps_shifted` are valid `Tile`s.
				let pairs = unsafe { core::mem::transmute::<[u8; 7], [Tile; 7]>(pairs) };
				let pairs = pairs.map(ScorableHandPair);

				Some(ScorableHandChiitoi(pairs))
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

		let lookup = ts.insert(new_tile).map(|ts| {
			let lookup = Lookup::new(&ts);
			LookupForNewTile::new(lookup, new_tile, tsumo_or_ron)
		}).unwrap_or_default();

		Hand13ScorableHands { kokushi_musou_or_chiitoi, lookup }
	}

	/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the set will be empty.
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

		let mut result = ts.as_ref().tenpai();

		result.retain(|new_tile| ts.clone().insert(new_tile).is_some_and(|ts| Lookup::<4>::new(&ts).len() > 0));

		match ToKokushiMusou::new(&ts) {
			ToKokushiMusou::Invalid => (),
			ToKokushiMusou::Single { wait, .. } => { result.insert(wait); },
			ToKokushiMusou::Any => result |= Tile34Set::KOKUSHI_MUSOU_VALID.into(),
		}

		if let Some((_, wait)) = to_chiitoi(&ts) {
			result.insert(wait);
			if let Some(wait) = wait.make_red() && !ts.contains(wait) {
				result.insert(wait);
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

assert_size_of!(Hand13ScorableHands, 152);

impl Iterator for Hand13ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou_or_chiitoi.take() {
			return Some(h);
		}

		let ([ma, mb, mc], md, pair) = self.lookup.next()?;
		Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, md, pair)))
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
	pub fn to_scorable_hands(self) -> Hand14ScorableHands {
		let Self(ts, []) = self;
		let lookup = Lookup::new(&ts);

		let kokushi_musou = ToKokushiMusou::tenhou(&ts);
		let chiitoi = tenhou_to_chiitoi(&ts);
		let kokushi_musou_or_chiitoi = match (kokushi_musou, chiitoi) {
			// SAFETY: A hand cannot be both kokushi musou and chiitoi.
			(Some(_), Some(_)) => unsafe { core::hint::unreachable_unchecked(); },
			(Some(h), None) => Some(ScorableHand::KokushiMusou(h)),
			(None, Some(h)) => Some(ScorableHand::Chiitoi(h)),
			(None, None) => None,
		};

		Hand14ScorableHands {
			kokushi_musou_or_chiitoi,
			inner: Default::default(),
			ts: ts.into_iter(),
			lookup,
		}
	}
}

#[derive(Clone, Debug)]
pub struct Hand14ScorableHands {
	kokushi_musou_or_chiitoi: Option<ScorableHand>,
	inner: LookupForNewTile<3>,
	ts: Tile37MultiSetIntoIter,
	lookup: Lookup<4>,
}

assert_size_of!(Hand14ScorableHands, 232);

impl Iterator for Hand14ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou_or_chiitoi.take() {
			return Some(h);
		}

		loop {
			let Some(([ma, mb, mc], md, pair)) = self.inner.next() else {
				let (new_tile, _) = self.ts.next()?;
				self.inner = LookupForNewTile::new(self.lookup.clone(), new_tile, TsumoOrRon::Tsumo);
				continue;
			};
			return Some(ScorableHand::Regular(ScorableHandRegular::new(ma, mb, mc, md, pair)));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let extra = usize::from(self.kokushi_musou_or_chiitoi.is_some());
		let (inner_lo, _) = self.inner.size_hint();
		(extra + inner_lo, None)
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
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> HandScorableHands {
		match self {
			Self::One(h) => HandScorableHands::One(h.to_scorable_hand(new_tile).into_iter()),
			Self::Four(h) => HandScorableHands::Four(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Seven(h) => HandScorableHands::Seven(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Ten(h) => HandScorableHands::Ten(h.to_scorable_hands(new_tile, tsumo_or_ron)),
			Self::Thirteen(h) => HandScorableHands::Thirteen(h.to_scorable_hands(new_tile, tsumo_or_ron)),
		}
	}

	/// Returns an [`Iterator`] of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then then there is no such tile, so the iterator will not yield any elements.
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
#[derive_const(Clone)]
pub struct Ankans<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	tiles: Tile34SetIntoIter,
}

impl<const NT: usize, const NM: usize> Ankans<NT, NM> {
	fn new(hand: Hand<NT, NM>) -> Self {
		let tiles = Tile34Set::from(Tile37Set::from(Tile37MultiSet::from(hand.0.clone())));
		Self {
			hand,
			tiles: tiles.into_iter(),
		}
	}
}

impl<const NT: usize, const NM: usize> Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
{
	fn next_inner(&mut self, t_kan: Tile) -> Option<Hand<{ NT - 4 }, { NM + 1 }>> {
		// Note: `ts` and `ms` are copies of `self.hand`, because we want to yield new hands, not mutate `self.hand`.
		let Hand(ts, ms) = self.hand.clone();

		let mut ts = Tile37MultiSet::from(ts);

		let count_t_kan = ts.remove_all(t_kan);
		let t_red = t_kan.make_red().unwrap_or(t_kan);
		let count_t_red = ts.remove_all(t_red);

		if count_t_kan + count_t_red != 4 {
			return None;
		}

		let ts = ts.try_into();
		// SAFETY: Exactly 4 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let m = HandMeld::ankan(t_kan, t_kan, t_kan, t_red);
		let m = unsafe { m.unwrap_unchecked() };

		Some(Hand(ts, append(ms, m)))
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
			let t_kan = self.tiles.next()?;
			if let Some(h) = self.next_inner(t_kan) {
				return Some(h);
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.tiles.size_hint();
		(0, hi)
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		loop {
			let t_kan = self.tiles.next_back()?;
			if let Some(h) = self.next_inner(t_kan) {
				return Some(h);
			}
		}
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Ankans<NT, NM>
where
	[(); NT - 4]:,
	[(); NM + 1]:,
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

impl core::iter::FusedIterator for HandAnkans {}

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
	fn new(hand: Hand<NT, NM>) -> Self {
		Self { hand, i: 0 }
	}
}

impl<const NT: usize, const NM: usize> Iterator for Shouminkans<NT, NM>
where
	[(); NT - 1]:,
{
	type Item = Hand<{ NT - 1 }, NM>;

	fn next(&mut self) -> Option<Self::Item> {
		// Note: This modifies the meld in a copy of `self.hand`, not `self.hand` itself,
		// because every Iterator element should be a modification on top of the original hand.
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
					(unsafe { t.unwrap_unchecked() }, ts)
				});
				let t_ts2 =
					if let Some(t_red) = new_tile.make_red() {
						ts.remove(t_red).map(|ts| {
							let t = Tile::kou_representative(t1, t_red, new_tile);
							(unsafe { t.unwrap_unchecked() }, ts)
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
		let mut allowed_discards = Tile37Set::from(Tile37MultiSet::from(ts.clone()));
		allowed_discards.remove_ignore_red(self.new_tile);
		(!allowed_discards.is_empty()).then(|| (Hand(ts, append(self.ms, HandMeld::Minkou(t))), allowed_discards))
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minkous<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	type Item = (Hand<{ (NT - 1) - 1 }, { NM + 1 }>, Tile37Set);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (t, ts) = self.t_ts1.take().or_else(|| self.t_ts2.take())?;
			if let Some((hand, allowed_discards)) = self.next_inner(t, ts) {
				return Some((hand, allowed_discards));
			}
		}
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
		loop {
			let (t, ts) = self.t_ts2.take().or_else(|| self.t_ts1.take())?;
			if let Some((hand, allowed_discards)) = self.next_inner(t, ts) {
				return Some((hand, allowed_discards));
			}
		}
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
	new_tile: NumberTile,
	inner: core::array::IntoIter<(ShunLowTileAndHasFiveRed, Option<NumberTile>, Tile37CountedMultiSet<{ (NT - 1) - 1 }>), 5>,
}

impl<const NT: usize, const NM: usize> Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
{
	fn new(Hand(ts, ms): Hand<NT, NM>, new_tile: NumberTile) -> Self {
		const INVALID: u8 = tn!(9s) as u8 + 1;

		fn new_inner(new_tile: NumberTile) -> [u8; 8] {
			const HAS_PREVIOUS_TWO: Tile27Set = t27set! {
				3m, 4m, 5m, 6m, 7m, 8m, 9m,
				3p, 4p, 5p, 6p, 7p, 8p, 9p,
				3s, 4s, 5s, 6s, 7s, 8s, 9s,
			};
			const HAS_NEXT_TWO: Tile27Set = t27set! {
				1m, 2m, 3m, 4m, 5m, 6m, 7m,
				1p, 2p, 3p, 4p, 5p, 6p, 7p,
				1s, 2s, 3s, 4s, 5s, 6s, 7s,
			};

			let ts_consider = {
				let ts_consider = core::simd::Simd::splat((new_tile as u8 & !0b1).cast_signed());
				let ts_consider = ts_consider + core::simd::Simd::from_array([-4, -4, -2, -2, 2, 2, 4, 4]);
				core::simd::num::SimdInt::cast::<u8>(ts_consider)
			};

			let is_valid = {
				let new_tile = core::simd::Simd::splat(new_tile as u8 - tn!(1m) as u8);
				let masks = core::simd::Simd::splat(1_u64) << core::simd::num::SimdUint::cast::<u64>(new_tile >> 1);
				core::simd::cmp::SimdPartialEq::simd_ne(
					masks & core::simd::Simd::from_array([
						HAS_PREVIOUS_TWO.present,
						HAS_PREVIOUS_TWO.present,
						Tile27Set::HAS_PREVIOUS.present,
						Tile27Set::HAS_PREVIOUS.present,
						Tile27Set::HAS_NEXT.present,
						Tile27Set::HAS_NEXT.present,
						HAS_NEXT_TWO.present,
						HAS_NEXT_TWO.present,
					]),
					core::simd::Simd::splat(0),
				)
			};

			let is_five = {
				let masks = core::simd::Simd::splat(1_u64) << core::simd::num::SimdUint::cast::<u64>((ts_consider - core::simd::Simd::splat(tn!(1m) as u8)) >> 1);
				core::simd::cmp::SimdPartialEq::simd_ne(
					masks & core::simd::Simd::from_array([0, Tile27Set::FIVES.present, 0, Tile27Set::FIVES.present, 0, Tile27Set::FIVES.present, 0, Tile27Set::FIVES.present]),
					core::simd::Simd::splat(0),
				)
			};
			let ts_consider = ts_consider | core::simd::Select::select(is_five, core::simd::Simd::splat(0b1), core::simd::Simd::splat(0b0));

			let is_valid = is_valid & (is_five | core::simd::Mask::from_array([true, false, true, false, true, false, true, false]));

			let ts_consider = core::simd::Select::select(is_valid, ts_consider, core::simd::Simd::splat(INVALID));
			ts_consider.to_array()
		}

		fn new_tile_high<const NT: usize>(t1: u8, t2: u8, new_tile: NumberTile, ts: Tile37CountedMultiSet<NT>) -> Option<(ShunLowTileAndHasFiveRed, Option<NumberTile>, Tile37CountedMultiSet<{ (NT - 1) - 1 }>)>
		where
			[(); (NT - 1) - 1]:,
		{
			if t1 == INVALID || t2 == INVALID { return None; }
			let t1 = unsafe { core::mem::transmute::<u8, ShunLowTile>(t1) };
			let t2 = unsafe { core::mem::transmute::<u8, NumberTile>(t2) };
			let ts = ts.remove(t1.into())?.remove(t2.into())?;
			let t = ShunLowTileAndHasFiveRed::new(t1, t2, new_tile);
			let t = unsafe { t.unwrap_unchecked() };
			Some((t, NumberTile::from(t1).previous_in_sequence(), ts))
		}

		fn new_tile_middle<const NT: usize>(t1: u8, new_tile: NumberTile, t3: u8, ts: Tile37CountedMultiSet<NT>) -> Option<(ShunLowTileAndHasFiveRed, Option<NumberTile>, Tile37CountedMultiSet<{ (NT - 1) - 1 }>)>
		where
			[(); (NT - 1) - 1]:,
		{
			if t1 == INVALID || t3 == INVALID { return None; }
			let t1 = unsafe { core::mem::transmute::<u8, ShunLowTile>(t1) };
			let t3 = unsafe { core::mem::transmute::<u8, NumberTile>(t3) };
			let ts = ts.remove(t1.into())?.remove(t3.into())?;
			let t = ShunLowTileAndHasFiveRed::new(t1, new_tile, t3);
			let t = unsafe { t.unwrap_unchecked() };
			Some((t, None, ts))
		}

		fn new_tile_low<const NT: usize>(new_tile: NumberTile, t2: u8, t3: u8, ts: Tile37CountedMultiSet<NT>) -> Option<(ShunLowTileAndHasFiveRed, Option<NumberTile>, Tile37CountedMultiSet<{ (NT - 1) - 1 }>)>
		where
			[(); (NT - 1) - 1]:,
		{
			if t2 == INVALID || t3 == INVALID { return None; }
			let new_tile = ShunLowTile::try_from(new_tile);
			let new_tile = unsafe { new_tile.unwrap_unchecked() };
			let t2 = unsafe { core::mem::transmute::<u8, NumberTile>(t2) };
			let t3 = unsafe { core::mem::transmute::<u8, NumberTile>(t3) };
			let ts = ts.remove(t2.into())?.remove(t3.into())?;
			let t = ShunLowTileAndHasFiveRed::new(new_tile, t2, t3);
			let t = unsafe { t.unwrap_unchecked() };
			Some((t, t3.next_in_sequence(), ts))
		}

		let [tm2, tm2_red, tm1, tm1_red, t1, t1_red, t2, t2_red] = new_inner(new_tile);
		let minjuns: ArrayVec<_, _> = [
			new_tile_high(tm2, tm1, new_tile, ts.clone()),
			new_tile_high(tm2, tm1_red, new_tile, ts.clone()),
			new_tile_high(tm2_red, tm1, new_tile, ts.clone()),
			new_tile_middle(tm1, new_tile, t1, ts.clone()),
			new_tile_middle(tm1, new_tile, t1_red, ts.clone()),
			new_tile_middle(tm1_red, new_tile, t1, ts.clone()),
			new_tile_low(new_tile, t1, t2, ts.clone()),
			new_tile_low(new_tile, t1, t2_red, ts.clone()),
			new_tile_low(new_tile, t1_red, t2, ts),
		].into_iter().flatten().collect();
		Self {
			ms,
			new_tile,
			inner: minjuns.into_iter(),
		}
	}
}

impl<const NT: usize, const NM: usize> Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	fn next_inner(
		&mut self,
		t: ShunLowTileAndHasFiveRed,
		cannot_discard: Option<NumberTile>,
		ts: Tile37CountedMultiSet<{ (NT - 1) - 1 }>,
	) -> Option<(Hand<{ (NT - 1) - 1 }, { NM + 1 }>, Tile37Set)> {
		let mut allowed_discards = Tile37Set::from(Tile37MultiSet::from(ts.clone()));
		allowed_discards.remove_ignore_red(self.new_tile.into());
		if let Some(cannot_discard) = cannot_discard {
			allowed_discards.remove_ignore_red(cannot_discard.into());
		}
		(!allowed_discards.is_empty()).then(|| (Hand(ts, append(self.ms, HandMeld::Minjun(t))), allowed_discards))
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	type Item = (Hand<{ (NT - 1) - 1 }, { NM + 1 }>, Tile37Set);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let (t, cannot_discard, ts) = self.inner.next()?;
			if let Some((hand, allowed_discards)) = self.next_inner(t, cannot_discard, ts) {
				return Some((hand, allowed_discards));
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (_, hi) = self.inner.size_hint();
		(0, hi)
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Minjuns<NT, NM>
where
	[(); (NT - 1) - 1]:,
	[(); NM + 1]:,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		loop {
			let (t, cannot_discard, ts) = self.inner.next_back()?;
			if let Some((hand, allowed_discards)) = self.next_inner(t, cannot_discard, ts) {
				return Some((hand, allowed_discards));
			}
		}
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minjuns<NT, NM>
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

fn append<T, const N: usize>(arr: [T; N], element: T) -> [T; N + 1] {
	let mut result = [const { core::mem::MaybeUninit::uninit() }; N + 1];
	// SAFETY: N + 1 > N and `[T; _]` has the same alignment as `T`.
	unsafe { result.as_mut_ptr().cast::<[T; N]>().write(arr); }
	result[N].write(element);
	// SAFETY: Appending an element to a `[; N]` initializes all elements of the resulting `[; N + 1]`.
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

#[derive(Clone, Copy, Debug)]
enum ToKokushiMusou {
	Invalid,
	Single { wait: Tile, duplicate: Tile },
	Any,
}

impl ToKokushiMusou {
	fn new(ts: &Tile37CountedMultiSet<13>) -> Self {
		let Some((duplicate, remaining)) = Self::new_inner(ts.as_ref()) else { return Self::Invalid; };

		let mut remaining = remaining.into_iter();
		let wait = remaining.next();
		if remaining.next().is_some() { return Self::Invalid; }
		if let Some(wait) = wait {
			// SAFETY: Pigeonhole principle. To get here, twelve elements were removed from `waits`,
			// and the thirteenth tile in `ts` was one of those twelve and thus written to `duplicate`.
			let duplicate = unsafe { duplicate.assume_init() };
			Self::Single { wait, duplicate }
		}
		else {
			Self::Any
		}
	}

	fn with_new_tile(self, new_tile: Tile) -> Option<ScorableHandKokushiMusou> {
		match self {
			Self::Invalid => None,
			Self::Single { wait, duplicate } => (wait == new_tile).then_some(ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: false }),
			Self::Any => Tile34Set::KOKUSHI_MUSOU_VALID.contains(new_tile).then_some(ScorableHandKokushiMusou { duplicate: new_tile, was_juusanmen_wait: true }),
		}
	}

	fn tenhou(ts: &Tile37CountedMultiSet<14>) -> Option<ScorableHandKokushiMusou> {
		let (duplicate, remaining) = Self::new_inner(ts.as_ref())?;
		remaining.is_empty().then(|| {
			// SAFETY: Pigeonhole principle. To get here, thirteen elements were removed from `waits`,
			// and the fourteenth tile in `ts` was one of those thirteen and thus written to `duplicate`.
			let duplicate = unsafe { duplicate.assume_init() };
			ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: true }
		})
	}

	fn new_inner(ts: &Tile37MultiSet) -> Option<(core::mem::MaybeUninit<Tile>, Tile34Set)> {
		const MASKS: core::simd::Simd<u64, 13> = core::simd::Simd::from_array([
			0b1 << 0, 0b1 << 8,
			0b1 << 9, 0b1 << 17,
			0b1 << 18, 0b1 << 26,
			0b1 << 27, 0b1 << 28, 0b1 << 29, 0b1 << 30, 0b1 << 31, 0b1 << 32, 0b1 << 33,
		]);

		let counts = ts.to_suits_simd();

		let counts_numbers = counts.extract::<0, 3>();

		if core::simd::num::SimdUint::reduce_or(counts_numbers) & 0b000_111_111_111_111_111_111_111_111_000 != 0 {
			return None;
		}

		let counts_kokushi_numbers = core::simd::simd_swizzle!(counts_numbers, [
			0, 0, 1, 1, 2, 2,
		]);
		let counts_kokushi_numbers = counts_kokushi_numbers >> core::simd::Simd::from_array([
			0, 27,
			0, 27,
			0, 27,
		]);
		let counts_kokushi_numbers = core::simd::num::SimdUint::cast::<u8>(counts_kokushi_numbers);

		let counts_kokushi_honors = core::simd::simd_swizzle!(counts, [
			3, 3, 3, 3, 3, 3, 3,
		]);
		let counts_kokushi_honors = counts_kokushi_honors >> core::simd::Simd::from_array([
			0, 3, 6, 9, 12, 15, 18,
		]);
		let counts_kokushi_honors = core::simd::num::SimdUint::cast::<u8>(counts_kokushi_honors);

		let counts = core::simd::simd_swizzle!(counts_kokushi_numbers.resize(0), counts_kokushi_honors, [
			0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13,
		]);
		let counts = counts & core::simd::Simd::splat(0b111);

		let mut duplicate = core::mem::MaybeUninit::uninit();
		let gt1 = core::simd::cmp::SimdPartialOrd::simd_gt(counts, core::simd::Simd::splat(1));
		if let Some(first_gt1) = gt1.first_set() {
			#[expect(clippy::cast_possible_truncation)]
			let t = first_gt1 as u8;
			let t = (t << 1) + t!(1m) as u8 + u8::from(t >= 1) * 14 + u8::from(t >= 3) * 14 + u8::from(t >= 5) * 14;
			let t = unsafe { core::mem::transmute::<u8, Tile>(t) };
			duplicate.write(t);
		}

		let mut waits = Tile34Set::KOKUSHI_MUSOU_VALID;
		let gt0 = core::simd::cmp::SimdPartialOrd::simd_gt(counts, core::simd::Simd::splat(0));
		let masks = core::simd::Select::select(gt0, MASKS, core::simd::Simd::splat(0));
		waits.present &= !core::simd::num::SimdUint::reduce_or(masks);

		Some((duplicate, waits))
	}
}

#[allow(clippy::needless_pass_by_value)]
fn to_chiitoi(ts: &Tile37CountedMultiSet<13>) -> Option<([ScorableHandPair; 6], Tile)> {
	let (pair_representatives, pair_is, wait) = cfg_select! {
		use_core_simd => {{
			let counts = Tile34MultiSet::from(Tile37MultiSet::from(ts.clone())).to_counts_simd();

			let pair_is = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));

			let num_pairs = core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(pair_is, core::simd::Simd::splat(1_u8), core::simd::Simd::splat(0_u8)));
			if num_pairs != 6 {
				return None;
			}

			#[expect(clippy::cast_possible_truncation)]
			let mut pair_representatives = core::simd::Select::select(
				pair_is,
				core::simd::Simd::from_array(core::array::from_fn(|i| ((i as u8) << 1) + t!(1m) as u8)),
				core::simd::Simd::splat(0),
			);
			pair_representatives[(t!(0m) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0m)));
			pair_representatives[(t!(0p) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0p)));
			pair_representatives[(t!(0s) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0s)));

			let single_is = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(1));
			let wait = single_is.first_set();
			// SAFETY: Since `num_pairs` is 6, `ts` is guaranteed to have contained six pairs and one unpaired tile,
			// and `wait` is guaranteed to be that tile.
			let wait = unsafe { wait.unwrap_unchecked() };
			#[expect(clippy::cast_possible_truncation)]
			let wait = ((wait as u8) << 1) + t!(1m) as u8;
			// SAFETY: At this point after the above comparisons, `ts` is guaranteed to have contained six pairs and one unpaired tile,
			// and `wait` is guaranteed to be that tile.
			let wait = unsafe { core::mem::transmute::<u8, Tile>(wait) };

			(pair_representatives.to_array(), pair_is.to_bitmask(), wait)
		}},

		_ => {{
			let (diff, pair_is, pair_representatives) = to_chiitoi_scalar_inner(ts.as_ref())?;

			let mut diff = diff.into_iter();
			let wait = diff.next()?;
			if diff.next().is_some() {
				return None;
			}

			(pair_representatives, pair_is, wait)
		}},
	};

	let mut ps = [const { core::mem::MaybeUninit::uninit() }; 6];
	chiitoi_extract_pair_representatives(&mut ps, &pair_representatives, pair_is);
	let ps = unsafe { core::mem::MaybeUninit::array_assume_init(ps) };

	Some((ps, wait))
}

#[allow(clippy::needless_pass_by_value)]
fn tenhou_to_chiitoi(ts: &Tile37CountedMultiSet<14>) -> Option<ScorableHandChiitoi> {
	let (pair_representatives, pair_is) = cfg_select! {
		use_core_simd => {{
			let counts = Tile34MultiSet::from(Tile37MultiSet::from(ts.clone())).to_counts_simd();

			let pair_is = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::<u8, 34>::splat(2));

			let num_pairs = core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(pair_is, core::simd::Simd::splat(1_u8), core::simd::Simd::splat(0_u8)));
			if num_pairs != 7 {
				return None;
			}

			#[expect(clippy::cast_possible_truncation)]
			let mut pair_representatives = core::simd::Select::select(
				pair_is,
				core::simd::Simd::from_array(core::array::from_fn(|i| ((i as u8) << 1) + t!(1m) as u8)),
				core::simd::Simd::splat(0),
			);
			pair_representatives[(t!(0m) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0m)));
			pair_representatives[(t!(0p) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0p)));
			pair_representatives[(t!(0s) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0s)));

			(pair_representatives.to_array(), pair_is.to_bitmask())
		}},

		_ => {{
			let (diff, pair_is, pair_representatives) = to_chiitoi_scalar_inner(ts.as_ref())?;
			if !diff.is_empty() {
				return None;
			}

			(pair_representatives, pair_is)
		}},
	};

	let mut ps = [const { core::mem::MaybeUninit::uninit() }; 7];
	chiitoi_extract_pair_representatives(&mut ps, &pair_representatives, pair_is);
	let ps = unsafe { core::mem::MaybeUninit::array_assume_init(ps) };
	Some(ScorableHandChiitoi(ps))
}

#[cfg(not(use_core_simd))]
fn to_chiitoi_scalar_inner(ts: &Tile37MultiSet) -> Option<(Tile34Set, u64, [u8; 34])> {
	let ts34 = Tile34MultiSet::from(ts.clone());
	let atleast_one = Tile34Set::from(&ts34);
	let atleast_two = Tile34Set::atleast_two(&ts34);
	let atleast_three = Tile34Set::atleast_three(&ts34);
	if !atleast_three.is_empty() {
		return None;
	}

	let mut pair_representatives = [0_u8; 34];
	for t in atleast_two.clone() {
		let t = t as u8;
		let offset = usize::from((t - t!(1m) as u8) >> 1);
		unsafe { core::hint::assert_unchecked(offset < pair_representatives.len()); }
		pair_representatives[offset] = t as u8;
	}
	pair_representatives[(t!(0m) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0m)));
	pair_representatives[(t!(0p) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0p)));
	pair_representatives[(t!(0s) as usize - t!(1m) as usize) >> 1] |= u8::from(ts.contains(t!(0s)));

	Some((atleast_one ^ atleast_two.clone(), atleast_two.present, pair_representatives))
}

fn chiitoi_extract_pair_representatives(
	result: &mut [core::mem::MaybeUninit<ScorableHandPair>],
	pair_representatives: &[u8; 34],
	pair_is: u64,
) {
	// TODO(rustup): Use `core::simd` once it supports register compress.
	//
	// Ref: https://github.com/rust-lang/portable-simd/issues/240

	cfg_select! {
		all(target_arch = "x86_64", target_feature = "avx512vbmi2") => {{
			let pair_representatives = core::simd::Simd::<u8, 64>::load_or_default(pair_representatives);
			let ps = unsafe { core::arch::x86_64::_mm512_maskz_compress_epi8(pair_is, pair_representatives.into()) };
			let ps = core::simd::Simd::from(ps);
			let ps = ps.to_array();
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
#[coverage(off)]
mod tests {
	extern crate std;

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
			t37set! { 1m, 3m, 4m, 5m },
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
			t37set! { 1m, 2m, 3m, 4m },
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
			t37set! { 1m, 2m, 3m, 4m },
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
			t37set! { 1m, 2m, 3m, 4m },
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
			t37set! { 1m, 2m, 3m, 4m },
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
			t37set! { 1m, 2m, 3m, 4m },
		));
		assert_eq!(minkous.size_hint(), (0, Some(1)));
		assert_eq!(minkous.next().unwrap(), (
			make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }),
			t37set! { 1m, 2m, 3m, 4m },
		));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let mut minjuns = h.find_minjuns(tn!(4m));
		assert_eq!(minjuns.size_hint(), (0, Some(5)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 5m 0m 6m 7m 8m E E E G G { minjun 2m 3m 4m }),
			t37set! { 5m, 0m, 6m, 7m, 8m, E, G },
		));
		assert_eq!(minjuns.size_hint(), (0, Some(4)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 0m 6m 7m 8m E E E G G { minjun 3m 4m 5m }),
			t37set! { 1m, 2m, 0m, 6m, 7m, 8m, E, G },
		));
		assert_eq!(minjuns.size_hint(), (0, Some(3)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 5m 6m 7m 8m E E E G G { minjun 3m 4m 0m }),
			t37set! { 1m, 2m, 5m, 6m, 7m, 8m, E, G },
		));
		assert_eq!(minjuns.size_hint(), (0, Some(2)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 3m 0m 7m 8m E E E G G { minjun 4m 5m 6m }),
			t37set! { 1m, 2m, 3m, 0m, 8m, E, G },
		));
		assert_eq!(minjuns.size_hint(), (0, Some(1)));
		assert_eq!(minjuns.next().unwrap(), (
			make_hand!(1m 2m 3m 5m 7m 8m E E E G G { minjun 4m 0m 6m }),
			t37set! { 1m, 2m, 3m, 5m, 8m, E, G },
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
				t37set! { E, E, E, S, S, S, W, W, W, N },
			));
			core::assert_matches!(minkous.next(), None);
		}

		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(2p));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(2p E E E S S S W W W N { minjun 1p 2p 3p }),
				t37set! { E, E, E, S, S, S, W, W, W, N },
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }),
				t37set! { E, E, E, S, S, S, W, W, W, N },
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }),
				t37set! { E, E, E, S, S, S, W, W, W, N },
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(4m));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m E E E S S S W W W N { minjun 2m 3m 4m }),
				t37set! { E, E, E, S, S, S, W, W, W, N },
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
				make_hand!(1m 4m 5m 6m E E E S S S W { minjun 2m 3m 4m }),
				t37set! { 5m, 6m, E, S, W },
			));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 2m 4m 6m E E E S S S W { minjun 3m 4m 5m }),
				t37set! { 1m, 2m, 6m, E, S, W },
			));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 2m 3m 4m E E E S S S W { minjun 4m 5m 6m }),
				t37set! { 1m, 2m, 3m, E, S, W },
			));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let mut minjuns = h.find_minjuns(tn!(7m));
			assert_eq!(minjuns.next().unwrap(), (
				make_hand!(1m 2m 3m 4m E E E S S S W { minjun 5m 6m 7m }),
				t37set! { 1m, 2m, 3m, E, S, W },
			));
			core::assert_matches!(minjuns.next(), None);
		}
	}

	#[test]
	fn tenpai() {
		{
			let h = make_hand!(5p 6p 0s 6s 7s 8s 8s Wh Wh Wh { minkou R R R });
			assert_eq!(h.tenpai(), t37set! { 4p, 7p });
		}

		{
			let h = make_hand!(4m 5m 6p 7p 8p 1s 2s 3s 4s 5s 6s 8s 8s);
			assert_eq!(h.tenpai(), t37set! { 3m, 6m });
		}

		{
			let h = make_hand!(1m 1m 4p 4p { minkou N N N } { minkou 3p 3p 3p } { minkou R R R });
			assert_eq!(h.tenpai(), t37set! { 1m, 4p });
		}

		{
			let h = make_hand!(1m 1m 4m 5m 6m 3p 4p 4p 0p 6p 1s 2s 3s);
			assert_eq!(h.tenpai(), t37set! { 2p, 5p });
		}

		{
			let h = make_hand!(4m 4m 1p 2p 3p 0p 5p 1s 2s 3s { minjun 1m 2m 3m });
			assert_eq!(h.tenpai(), t37set! { 4m, 5p });
		}

		{
			let h = make_hand!(3p 3p 4p 4p 0p 5p 7p 8p 8p 8p 9p G G);
			assert_eq!(h.tenpai(), t37set! { 8p, G });
		}

		{
			let h = make_hand!(4m 0m 6m 7m 7m 4s 0s 6s 7s 8s { minjun 4p 5p 6p });
			assert_eq!(h.tenpai(), t37set! { 3s, 6s, 9s });
		}

		{
			let h = make_hand!(1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m);
			assert_eq!(h.tenpai(), t37set! { 1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m });
		}

		{
			let h = make_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R);
			assert_eq!(h.tenpai(), t37set! { 1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R });
		}

		{
			let h = make_hand!(1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh);
			assert_eq!(h.tenpai(), t37set! { S, });
		}

		// Red five
		{
			let h = make_hand!(1m 1m 2m 2m 2m 3m 3m 3m 4p 5p 5p 5p 6p);
			assert_eq!(h.tenpai(), t37set! { 1m, 4m, 0p });
		}

		// Red five
		{
			let h = make_hand!(5m 5m 0m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			assert_eq!(h.tenpai(), t37set! { 5m, 6m, 7m, 8m });
		}

		// Red five
		{
			let h = make_hand!(5m 5m 5m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			assert_eq!(h.tenpai(), t37set! { 0m, 6m, 7m, 8m });
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand. Not considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 1m 1m 1m 3m 4m 5m 3p 4p 5p 3s 4s 5s);
			assert_eq!(h.tenpai(), t37set! {});
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand, but only 1x 1m in unmelded tiles. Considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 3m 4m 5m 3p 4p 5p 3s 4s 5s { minkou 1m 1m 1m });
			assert_eq!(h.tenpai(), t37set! { 1m, });
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
			assert_eq!(h.tenpai(), t37set! { 8p, });
		}
	}
}
