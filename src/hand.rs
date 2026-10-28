use crate::{
	ADD1, append, ArrayVec,
	extract_bits32,
	HandMeldType,
	KanKouToiTile,
	Number, NumberSuit, NumberTile, NumberTileClassified,
	ScorableHand, ScorableHandChiitoi, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair, ScorableHandRegular,
	ShunLowTile, ShunTile, SortingNetwork, SUB1, SUB2, SUB3, SUB4,
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
/// If you want to hold all possible hands in a single type, use the [`HandStable`] and [`HandTentative`] types.
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

/// A single meld inside a [`Hand`].
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Copy)]
#[derive_const(Clone, Eq, PartialEq)]
#[repr(C, u8, align(2))]
pub enum HandMeld {
	/// Closed quad formed by kan.
	Ankan(KanKouToiTile) = 0,

	/// Open quad formed by kan.
	Minkan(KanKouToiTile) = 1,

	/// Open triplet formed by pon.
	Minkou(KanKouToiTile) = 3,

	/// Open sequence formed by chii.
	Minjun(ShunTile) = 5,
}

assert_size_of!(HandMeld, 2);

/// A hand containing some number of tiles and melds when it's not the player's turn.
///
/// This type is a way to hold all possible stable hand types during a game.
#[derive(Clone)]
#[derive_const(Eq, PartialEq)]
pub struct HandStable(Tile37MultiSet, ArrayVec<HandMeld, 4>);

assert_size_of!(HandStable, 40);

/// A hand containing some number of tiles and melds when it's the player's turn.
/// This has an extra tile that must be discarded using [`discard`][HandTentative::discard]
/// to return to a [`HandStable`].
///
/// This type is a way to hold all possible tentative hand types during a game.
#[derive(Clone)]
#[derive_const(Eq, PartialEq)]
pub struct HandTentative(Tile37MultiSet, ArrayVec<HandMeld, 4>);

assert_size_of!(HandTentative, 40);

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandStable: From<Self>,
{
	/// Draw the given tile into this stable hand to form a tentative hand.
	pub fn draw(self, new_tile: Tile) -> Option<Hand<core::gca!(ADD1::<NT>), NM>> {
		let Self(ts, ms) = self;
		let ts = ts.insert(new_tile)?;
		Some(Hand(ts, ms))
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NM + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<core::gca!(SUB3::<NT>), core::gca!(ADD1::<NM>)>> {
		let Self(ts, ms) = self;

		let (ts, m) = find_daiminkan(ts.into(), new_tile)?;

		let ts = ts.try_into();
		// SAFETY: Exactly 3 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(ms, m);

		Some(Hand(ts, ms))
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> Minkous<NT, NM> {
		Minkous::new(self, new_tile)
	}

	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> Minjuns<NT, NM> {
		Minjuns::new(self, new_tile)
	}
}

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandTentative: From<Self>,
{
	/// Discard the given tile from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile.
	/// If the given tile is not present in this hand, then this function returns `None`.
	pub fn discard(self, tile: Tile) -> Option<Hand<core::gca!(SUB1::<NT>), NM>> {
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

fn hand_fmt(ts: &Tile37MultiSet, ms: &[HandMeld], f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

impl<const NT: usize, const NM: usize> core::fmt::Display for Hand<NT, NM> {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		hand_fmt(self.0.as_ref(), &self.1, f)
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
		let [m1, m2, m3, m4] = ms.map(Into::into);
		Some(ScorableHandRegular::new(m1, m2, m3, ScorableHandFourthMeld::tanki(m4), pair, tsumo_or_ron))
	}

	/// Returns a set of all tiles that would complete this hand.
	///
	/// `inventory` is the set of all tiles at the start of the game, specifically one of the `Tile37MultiSet::INVENTORY_*` constants.
	/// It is required that `self` contains a subset of the tiles in `inventory`. If there is any tile for which `self` contains more copies than there are in `inventory`,
	/// the function may give nonsensical results.
	pub fn tenpai(&self, inventory: &Tile37MultiSet) -> Tile37Set {
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

		hand_1_4_tenpai(self.0.as_ref(), inventory)
	}
}

fn hand_1_4_tenpai(ts: &Tile37MultiSet, inventory: &Tile37MultiSet) -> Tile37Set {
	debug_assert_eq!(core::simd::num::SimdUint::reduce_sum(core::simd::Simd::from_array(ts.len())), 1);

	let remaining = Tile37Set::from_suit_counts(inventory.to_suits_simd() - ts.to_suits_simd());

	let t1 = ts.clone().into_iter().next();
	let (t1, _) = unsafe { t1.unwrap_unchecked() };

	let mut result = Tile37Set::default();

	let t_non_red = t1.remove_red();
	if remaining.contains(t_non_red) {
		result.insert(t_non_red);
	}
	if let Some(t_red) = t_non_red.make_red() && remaining.contains(t_red) {
		result.insert(t_red);
	}

	result
}

macro_rules! hand_into_scorable_hands {
	($(
		Hand<$nt:literal, $nm:literal>::fn into_scorable_hands() -> struct $iter:ident ,
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
					let ms = ms.map(Into::into);
					$iter { lookup, ms }
				}
			}

			#[doc = concat!("An [`Iterator`] of [`ScorableHand`]s that can be created from the original [`Hand<", stringify!($nt), ", ", stringify!($nm), ">`] and the given drawn / called tile.")]
			#[derive(Clone, Debug)]
			pub struct $iter {
				lookup: LookupForNewTile<{ ($nt - 4) / 3 }>,
				ms: [ScorableHandMeld; $nm],
			}

			impl Iterator for $iter {
				type Item = ScorableHandRegular;

				fn next(&mut self) -> Option<Self::Item> {
					let mut ms = [const { core::mem::MaybeUninit::uninit() }; 3];
					let (_, rest) = ms.write_iter(self.ms.into_iter());
					let rest = rest.as_mut_array();
					let rest = unsafe { rest.unwrap_unchecked() };
					let rest = unsafe { &mut *<*mut [core::mem::MaybeUninit<ScorableHandMeld>; 3 - $nm]>::cast::<core::mem::MaybeUninit<[ScorableHandMeld; 3 - $nm]>>(rest) };
					let (m4, pair) = self.lookup.next_into(rest)?;
					let [m1, m2, m3] = unsafe { core::mem::MaybeUninit::array_assume_init(ms) };
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
	Hand<4, 3>::fn into_scorable_hands() -> struct Hand4ScorableHands,
	Hand<7, 2>::fn into_scorable_hands() -> struct Hand7ScorableHands,
	Hand<10, 1>::fn into_scorable_hands() -> struct Hand10ScorableHands,
}

assert_size_of!(Hand4ScorableHands, 56);
assert_size_of!(Hand7ScorableHands, 64);
assert_size_of!(Hand10ScorableHands, 80);

macro_rules! hand_tenpai {
	($(
		Hand<$nt:literal, $nm:literal>::fn tenpai() -> Tile37Set,
	)*) => {
		$(
			impl Hand<$nt, $nm> {
				/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
				///
				/// If the hand is not in tenpai then there is no such tile, so the set will be empty.
				///
				/// `inventory` is the set of all tiles at the start of the game, specifically one of the `Tile37MultiSet::INVENTORY_*` constants.
				/// It is required that `self` contains a subset of the tiles in `inventory`. If there is any tile for which `self` contains more copies than there are in `inventory`,
				/// the function may give nonsensical results.
				pub fn tenpai(&self, inventory: &Tile37MultiSet) -> Tile37Set {
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

					hand_middle_tenpai(self.0.as_ref(), inventory)
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

fn hand_middle_tenpai(ts: &Tile37MultiSet, inventory: &Tile37MultiSet) -> Tile37Set {
	core::debug_assert_matches!(core::simd::num::SimdUint::reduce_sum(core::simd::Simd::from_array(ts.len())), 4 | 7 | 10);
	let remaining = Tile37Set::from_suit_counts(inventory.to_suits_simd() - ts.to_suits_simd());
	lookup_tenpai(ts, remaining)
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
	///
	/// `inventory` is the set of all tiles at the start of the game, specifically one of the `Tile37MultiSet::INVENTORY_*` constants.
	/// It is required that `self` contains a subset of the tiles in `inventory`. If there is any tile for which `self` contains more copies than there are in `inventory`,
	/// the function may give nonsensical results.
	pub fn tenpai(&self, inventory: &Tile37MultiSet) -> Tile37Set {
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

		hand_13_0_tenpai(self.0.as_ref(), inventory)
	}
}

fn hand_13_0_tenpai(ts: &Tile37MultiSet, inventory: &Tile37MultiSet) -> Tile37Set {
	debug_assert_eq!(core::simd::num::SimdUint::reduce_sum(core::simd::Simd::from_array(ts.len())), 13);

	let remaining = Tile37Set::from_suit_counts(inventory.to_suits_simd() - ts.to_suits_simd());

	let mut result = lookup_tenpai(ts, remaining.clone());

	match ToKokushiMusou::new(ts) {
		ToKokushiMusou::Invalid => (),
		ToKokushiMusou::Single { wait, .. } => if remaining.contains(wait) { result.insert(wait); },
		ToKokushiMusou::Any => result |= remaining.clone() & Tile37Set::TERMINALS_AND_HONORS,
	}

	if let ToChiitoiInner::SingleUnpaired { unpaired, .. } = ToChiitoiInner::new(ts) {
		let unpaired_non_red = unpaired.remove_red();
		if remaining.contains(unpaired_non_red) {
			result.insert(unpaired.remove_red());
		}
		if let Some(unpaired) = unpaired_non_red.make_red() && remaining.contains(unpaired) {
			result.insert(unpaired);
		}
	}

	result
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

		let mut ms = core::mem::MaybeUninit::uninit();
		let (m4, pair) = self.lookup.next_into(&mut ms)?;
		let [m1, m2, m3] = unsafe { ms.assume_init() };
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

assert_size_of!(Hand14ScorableHands, 120);

impl Iterator for Hand14ScorableHands {
	type Item = ScorableHand;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(h) = self.kokushi_musou_or_chiitoi.take() {
			return Some(h);
		}

		let mut ms = core::mem::MaybeUninit::uninit();
		let (m4, pair) = self.regular.next_into(&mut ms)?;
		let [m1, m2, m3] = unsafe { ms.assume_init() };
		Some(ScorableHand::Regular(ScorableHandRegular { pair, m1, m2, m3, m4 }))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let extra = usize::from(self.kokushi_musou_or_chiitoi.is_some());
		let (regular_lo, regular_hi) = self.regular.size_hint();
		(extra + regular_lo, regular_hi.and_then(|regular_hi| extra.checked_add(regular_hi)))
	}
}

impl core::iter::FusedIterator for Hand14ScorableHands {}

/// Parses a `Hand` from MPSZ notation, extended to support notating minjuns / minkous / ankans / minkans.
/// See `extended-mpsz.md` in the root of this repo.
///
/// Note that [`HandMeld`] does not retain information about which tile was called or which player it was called from.
/// This means that the `-` / `+` / `=` marker is used to identify the type of the meld,
/// but the order of the tiles and the position of the marker within the meld
/// (which identify the tile that was called and who it was called from) are ignored.
///
/// ```rust
/// # #![deny(unused)]
/// #
/// # use riichi::{
/// #     Hand,
/// #     make_hand,
/// # };
/// #
/// // chii, chii
/// let h: Hand<7, 2> = "4477m1p11z 7-68m 5-46s".parse().unwrap();
/// assert_eq!(h, make_hand!(4m 4m 7m 7m 1p E E { minjun 7m 6m 8m } { minjun 5s 4s 6s }));
///
/// // pon
/// let h: Hand<10, 1> = "35m3378p3467s 2-22m".parse().unwrap();
/// assert_eq!(h, make_hand!(3m 5m 3p 3p 7p 8p 3s 4s 6s 7s { minkou 2m 2m 2m }));
///
/// // chii, shouminkan
/// let h: Hand<7, 2> = "3377p678s 2-34s 2=222m".parse().unwrap();
/// assert_eq!(h, make_hand!(3p 3p 7p 7p 6s 7s 8s { minjun 2s 3s 4s } { minkan 2m 2m 2m 2m }));
///
/// // daiminkan, chii
/// let h: Hand<7, 2> = "1309p789s 5555-z 5-46p".parse().unwrap();
/// assert_eq!(h, make_hand!(1p 3p 0p 9p 7s 8s 9s { minkan Wh Wh Wh Wh } { minjun 5p 4p 6p }));
/// ```
impl<const NT: usize, const NM: usize> core::str::FromStr for Hand<NT, NM> {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (ts, ts_type, mut s) = Tile::parse_run_until::<NT>(s.as_ref(), Some(b' '))?;
		if ts_type.is_some() {
			return Err(());
		}
		let ts = ts.try_into().map_err(|_| ())?;
		let ts = Tile37CountedMultiSet::new(&ts).ok_or(())?;

		let mut ms = [const { core::mem::MaybeUninit::uninit() }; NM];
		for dst in &mut ms {
			let (m, s_) = HandMeld::parse_until(s, Some(b' '))?;
			dst.write(m);
			s = s_;
		}
		if !s.is_empty() {
			return Err(());
		}
		let ms = unsafe { core::mem::MaybeUninit::array_assume_init(ms) };

		Ok(Self(ts, ms))
	}
}

impl HandMeld {
	/// Construct a `HandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `KanKouToiTile::kan` returns `Some`, `None` otherwise.
	pub const fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = KanKouToiTile::kan(t1, t2, t3, t4)?;
		Some(Self::Ankan(t))
	}

	/// Construct a `HandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `KanKouToiTile::kan` returns `Some`, `None` otherwise.
	pub const fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = KanKouToiTile::kan(t1, t2, t3, t4)?;
		Some(Self::Minkan(t))
	}

	/// Construct a `HandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `KanKouToiTile::kou` returns `Some`, `None` otherwise.
	pub const fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = KanKouToiTile::kou(t1, t2, t3)?;
		Some(Self::Minkou(t))
	}

	/// Construct a `HandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunTile::new`] returns `Some`, `None` otherwise.
	pub const fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunTile::new(t1, t2, t3)?;
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
				let t = KanKouToiTile::kan(t1, t2, t3, t4).ok_or(())?;
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

const impl AsRef<ScorableHandMeld> for HandMeld {
	fn as_ref(&self) -> &ScorableHandMeld {
		unsafe { &*<*const Self>::cast::<ScorableHandMeld>(self) }
	}
}

impl core::fmt::Debug for HandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for HandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let this: &ScorableHandMeld = self.as_ref();
		this.fmt(f)
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
	pub fn tiles(&self) -> &Tile37MultiSet {
		&self.0
	}

	pub fn melds(&self) -> &[HandMeld] {
		&self.1
	}

	/// Draw the given tile into this stable hand to form a tentative hand.
	pub fn draw(self, new_tile: Tile) -> Option<HandTentative> {
		let Self(mut ts, ms) = self;
		if !ts.insert(new_tile) { return None; }
		Some(HandTentative(ts, ms))
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Self> {
		let Self(ts, mut ms) = self;

		let (ts, m) = find_daiminkan(ts, new_tile)?;

		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some(Self(ts, ms))
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> HandMinkous {
		HandMinkous::new(self, new_tile)
	}

	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> HandMinjuns {
		HandMinjuns::new(self, new_tile)
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
		match self.1.len() {
			4 => {
				let h = Hand::<1, 4>::try_from(self);
				let h = unsafe { h.unwrap_unchecked() };
				HandScorableHands::One(h.into_scorable_hand(new_tile, tsumo_or_ron).into_iter())
			},

			3 => {
				let h = Hand::<4, 3>::try_from(self);
				let h = unsafe { h.unwrap_unchecked() };
				HandScorableHands::Four(h.into_scorable_hands(new_tile, tsumo_or_ron))
			},

			2 => {
				let h = Hand::<7, 2>::try_from(self);
				let h = unsafe { h.unwrap_unchecked() };
				HandScorableHands::Seven(h.into_scorable_hands(new_tile, tsumo_or_ron))
			},

			1 => {
				let h = Hand::<10, 1>::try_from(self);
				let h = unsafe { h.unwrap_unchecked() };
				HandScorableHands::Ten(h.into_scorable_hands(new_tile, tsumo_or_ron))
			},

			0 => {
				let h = Hand::<13, 0>::try_from(self);
				let h = unsafe { h.unwrap_unchecked() };
				HandScorableHands::Thirteen(h.into_scorable_hands(new_tile, tsumo_or_ron))
			},

			_ => unsafe { core::hint::unreachable_unchecked(); },
		}
	}

	/// Returns a set of all tiles that would complete this hand if it is currently in tenpai.
	///
	/// If the hand is not in tenpai then there is no such tile, so the set will be empty.
	///
	/// `inventory` is the set of all tiles at the start of the game, specifically one of the `Tile37MultiSet::INVENTORY_*` constants.
	/// It is required that `self` contains a subset of the tiles in `inventory`. If there is any tile for which `self` contains more copies than there are in `inventory`,
	/// the function may give nonsensical results.
	pub fn tenpai(&self, inventory: &Tile37MultiSet) -> Tile37Set {
		match self.1.len() {
			4 => hand_1_4_tenpai(&self.0, inventory),
			1..=3 => hand_middle_tenpai(&self.0, inventory),
			0 => hand_13_0_tenpai(&self.0, inventory),
			_ => unsafe { core::hint::unreachable_unchecked(); },
		}
	}
}

impl core::fmt::Debug for HandStable {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for HandStable {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		hand_fmt(&self.0, &self.1, f)
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
/// assert_eq!(h, HandStable::from(make_hand!(4m 4m 7m 7m 1p E E { minjun 7m 6m 8m } { minjun 5s 4s 6s })));
///
/// // pon
/// let h: HandStable = "35m3378p3467s 2-22m".parse().unwrap();
/// assert_eq!(h, HandStable::from(make_hand!(3m 5m 3p 3p 7p 8p 3s 4s 6s 7s { minkou 2m 2m 2m })));
///
/// // chii, shouminkan
/// let h: HandStable = "3377p678s 2-34s 2=222m".parse().unwrap();
/// assert_eq!(h, HandStable::from(make_hand!(3p 3p 7p 7p 6s 7s 8s { minjun 2s 3s 4s } { minkan 2m 2m 2m 2m })));
///
/// // daiminkan, chii
/// let h: HandStable = "1309p789s 5555-z 5-46p".parse().unwrap();
/// assert_eq!(h, HandStable::from(make_hand!(1p 3p 0p 9p 7s 8s 9s { minkan Wh Wh Wh Wh } { minjun 5p 4p 6p })));
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
	pub fn tiles(&self) -> &Tile37MultiSet {
		&self.0
	}

	pub fn melds(&self) -> &[HandMeld] {
		&self.1
	}

	/// Discard the given tile from this hand.
	///
	/// Returns the hand resulting from the discard of that tile.
	/// If the given tile is not present in this hand, then this function returns `None`.
	pub fn discard(self, tile: Tile) -> Option<HandStable> {
		let Self(mut ts, ms) = self;
		ts.remove(tile).then(|| HandStable(ts, ms))
	}

	/// Finds all possible ankans (quad via kan call on a quad in the hand).
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_ankans(self) -> HandAnkans {
		HandAnkans::new(self)
	}

	/// Find all possible shouminkans (quad via kan call on a minkou formed previously).
	///
	/// Returns an [`Iterator`] of all possible hands that would result from this call.
	pub fn find_shouminkans(self) -> HandShouminkans {
		HandShouminkans::new(self)
	}
}

impl core::fmt::Debug for HandTentative {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for HandTentative {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		hand_fmt(&self.0, &self.1, f)
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
/// assert_eq!(h, HandTentative::from(make_hand!(4m 4m 7m 7m 1p E E S { minjun 7m 6m 8m } { minjun 5s 4s 6s })));
///
/// // pon
/// let h: HandTentative = "35m3378p3467s2z 2-22m".parse().unwrap();
/// assert_eq!(h, HandTentative::from(make_hand!(3m 5m 3p 3p 7p 8p 3s 4s 6s 7s S { minkou 2m 2m 2m })));
///
/// // chii, shouminkan
/// let h: HandTentative = "3377p678s2z 2-34s 2=222m".parse().unwrap();
/// assert_eq!(h, HandTentative::from(make_hand!(3p 3p 7p 7p 6s 7s 8s S { minjun 2s 3s 4s } { minkan 2m 2m 2m 2m })));
///
/// // daiminkan, chii
/// let h: HandTentative = "1309p789s2z 5555-z 5-46p".parse().unwrap();
/// assert_eq!(h, HandTentative::from(make_hand!(1p 3p 0p 9p 7s 8s 9s S { minkan Wh Wh Wh Wh } { minjun 5p 4p 6p })));
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
	($($nt:expr, $nm:expr => $ty:tt ,)*) => {
		$(
			impl From<Hand<$nt, $nm>> for $ty {
				fn from(Hand(ts, ms): Hand<$nt, $nm>) -> Self {
					let ts = ts.into();
					let ms = ms.try_into();
					let ms = unsafe { ms.unwrap_unchecked() };
					Self(ts, ms)
				}
			}

			impl TryFrom<$ty> for Hand<$nt, $nm> {
				type Error = $ty;

				fn try_from(h: $ty) -> Result<Self, Self::Error> {
					if h.1.len() == $nm {
						let ts = h.0.try_into();
						let ts = unsafe { ts.unwrap_unchecked() };
						let ms = h.1.try_into();
						let ms = unsafe { ms.unwrap_unchecked() };
						Ok(Hand(ts, ms))
					}
					else {
						Err(h)
					}
				}
			}
		)*
	};
}

hand_enum_from! {
	1, 4 => HandStable,
	2, 4 => HandTentative,
	4, 3 => HandStable,
	5, 3 => HandTentative,
	7, 2 => HandStable,
	8, 2 => HandTentative,
	10, 1 => HandStable,
	11, 1 => HandTentative,
	13, 0 => HandStable,
	14, 0 => HandTentative,
}

#[derive(Debug)]
#[derive_const(Clone)]
struct AnkansInner {
	ts: Tile37MultiSet,
	tiles: Tile34SetIntoIter,
}

impl AnkansInner {
	fn new(ts: Tile37MultiSet) -> Self {
		let tiles = Tile34Set::atleast_four(&Tile34MultiSet::from(ts.clone())).into_iter();
		Self { ts, tiles }
	}

	fn next_inner(&mut self, t_kan: Tile) -> (Tile37MultiSet, HandMeld) {
		// Note: `ts` is a copy of `self.ts`, because we want to yield new hands, not mutate `self`.
		let mut ts = self.ts.clone();

		let (num_regular, num_red_fives) = ts.remove_all_ignore_red(t_kan);
		unsafe { core::hint::assert_unchecked(num_regular + num_red_fives == 4); }
		unsafe { core::hint::assert_unchecked(num_red_fives <= 3); }
		let t = KanKouToiTile::new(t_kan, num_red_fives);
		let t = unsafe { t.unwrap_unchecked() };
		let m = HandMeld::Ankan(t);

		(ts, m)
	}
}

impl Iterator for AnkansInner {
	type Item = (Tile37MultiSet, HandMeld);

	fn next(&mut self) -> Option<Self::Item> {
		let t_kan = self.tiles.next()?;
		Some(self.next_inner(t_kan))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.tiles.size_hint()
	}
}

impl DoubleEndedIterator for AnkansInner {
	fn next_back(&mut self) -> Option<Self::Item> {
		let t_kan = self.tiles.next_back()?;
		Some(self.next_inner(t_kan))
	}
}

impl ExactSizeIterator for AnkansInner {
	fn len(&self) -> usize {
		self.tiles.len()
	}
}

impl core::iter::FusedIterator for AnkansInner {}

unsafe impl core::iter::TrustedLen for AnkansInner {}

/// An [`Iterator`] of [`Hand<{ NT - 4 }, { NM + 1 }>`] values formed by creating an ankan in the given hand.
#[derive(Debug)]
pub struct Ankans<const NT: usize, const NM: usize> {
	inner: AnkansInner,
	ms: [HandMeld; NM],
}

assert_size_of!(Ankans<2, 4>, 40);
assert_size_of!(Ankans<5, 3>, 40);
assert_size_of!(Ankans<8, 2>, 40);
assert_size_of!(Ankans<11, 1>, 40);
assert_size_of!(Ankans<14, 0>, 32);

impl<const NT: usize, const NM: usize> Ankans<NT, NM> {
	fn new(Hand(ts, ms): Hand<NT, NM>) -> Self {
		let inner = AnkansInner::new(ts.into());
		Self { inner, ms }
	}
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<const NT: usize, const NM: usize> Clone for Ankans<NT, NM> {
	fn clone(&self) -> Self {
		Self {
			inner: self.inner.clone(),
			ms: self.ms,
		}
	}
}

impl<const NT: usize, const NM: usize> Iterator for Ankans<NT, NM> {
	type Item = Hand<core::gca!(SUB4::<NT>), core::gca!(ADD1::<NM>)>;

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next()?;

		let ts = ts.try_into();
		// SAFETY: Exactly 4 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(self.ms, m);

		Some(Hand(ts, ms))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Ankans<NT, NM> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next_back()?;

		let ts = ts.try_into();
		// SAFETY: Exactly 4 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(self.ms, m);

		Some(Hand(ts, ms))
	}
}

impl<const NT: usize, const NM: usize> ExactSizeIterator for Ankans<NT, NM> {
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Ankans<NT, NM> {}

unsafe impl<const NT: usize, const NM: usize> core::iter::TrustedLen for Ankans<NT, NM> {}

/// An [`Iterator`] of [`HandStable`] values formed by creating an ankan in the given hand.
#[derive(Clone, Debug)]
pub struct HandAnkans {
	inner: AnkansInner,
	ms: ArrayVec<HandMeld, 4>,
}

assert_size_of!(HandAnkans, 48);

impl HandAnkans {
	fn new(HandTentative(ts, ms): HandTentative) -> Self {
		let inner = AnkansInner::new(ts);
		Self { inner, ms }
	}
}

impl Iterator for HandAnkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next()?;

		let mut ms = self.ms.clone();
		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some(HandStable(ts, ms))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl DoubleEndedIterator for HandAnkans {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next_back()?;

		let mut ms = self.ms.clone();
		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some(HandStable(ts, ms))
	}
}

impl ExactSizeIterator for HandAnkans {
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl core::iter::FusedIterator for HandAnkans {}

unsafe impl core::iter::TrustedLen for HandAnkans {}

fn find_daiminkan(
	mut ts: Tile37MultiSet,
	new_tile: Tile,
) -> Option<(Tile37MultiSet, HandMeld)> {
	let (num_regular, num_red_fives) = ts.remove_all_ignore_red(new_tile);
	if num_regular + num_red_fives != 3 {
		return None;
	}
	let num_red_fives = num_red_fives + u8::from(new_tile.is_red());
	let t = KanKouToiTile::new(new_tile, num_red_fives)?;
	let m = HandMeld::Minkan(t);
	Some((ts, m))
}


fn shouminkans_next(ts: &Tile37MultiSet, ms: &mut [HandMeld], i: &mut u8) -> Option<Tile37MultiSet> {
	loop {
		let m = ms.get_mut(usize::from(*i))?;
		*i += 1;
		let HandMeld::Minkou(mut t) = *m else { continue; };
		let t_kou = t.tile();
		let (new_tile, ts) =
			if let new_tile_non_red = t_kou && ts.contains(new_tile_non_red) {
				let mut ts = ts.clone();
				ts.remove(new_tile_non_red);
				(new_tile_non_red, ts)
			}
			else if let Some(new_tile_red) = t_kou.make_red() && ts.contains(new_tile_red) {
				let mut ts = ts.clone();
				ts.remove(new_tile_red);
				(new_tile_red, ts)
			}
			else {
				continue;
			};
		if new_tile.is_red() {
			unsafe { t.add_red(); }
		}
		*m = HandMeld::Minkan(t);
		return Some(ts);
	}
}

/// An [`Iterator`] of [`Hand<{ NT - 1 }, NM>`] values formed by creating a shouminkan in the given hand.
#[derive(Debug)]
pub struct Shouminkans<const NT: usize, const NM: usize> {
	ts: Tile37CountedMultiSet<NT>,
	ms: [HandMeld; NM],
	i: u8,
}

assert_size_of!(Shouminkans<2, 4>, 32);
assert_size_of!(Shouminkans<5, 3>, 28);
assert_size_of!(Shouminkans<8, 2>, 28);
assert_size_of!(Shouminkans<11, 1>, 24);
assert_size_of!(Shouminkans<14, 0>, 24);

impl<const NT: usize, const NM: usize> Shouminkans<NT, NM> {
	const fn new(Hand(ts, ms): Hand<NT, NM>) -> Self {
		Self { ts, ms, i: 0 }
	}
}

// TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<const NT: usize, const NM: usize> Clone for Shouminkans<NT, NM> {
	fn clone(&self) -> Self {
		Self {
			ts: self.ts.clone(),
			ms: self.ms,
			i: self.i,
		}
	}
}

impl<const NT: usize, const NM: usize> Iterator for Shouminkans<NT, NM> {
	type Item = Hand<core::gca!(SUB1::<NT>), NM>;

	fn next(&mut self) -> Option<Self::Item> {
		// Note: `ms` is a copy of `self.ms`, because we want to yield new hands, not mutate `self`.
		let mut ms = self.ms;

		let ts = shouminkans_next(self.ts.as_ref(), &mut ms, &mut self.i)?;

		let ts = ts.try_into();
		// SAFETY: Exactly 1 element was removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		Some(Hand(ts, ms))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		(0, Some(self.ms.len() - usize::from(self.i)))
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Shouminkans<NT, NM> {}

/// An [`Iterator`] of [`HandStable`] values formed by creating an shouminkan in the given hand.
#[derive(Clone, Debug)]
pub struct HandShouminkans {
	ts: Tile37MultiSet,
	ms: ArrayVec<HandMeld, 4>,
	i: u8,
}

assert_size_of!(HandShouminkans, 40);

impl HandShouminkans {
	const fn new(HandTentative(ts, ms): HandTentative) -> Self {
		Self { ts, ms, i: 0 }
	}
}

impl Iterator for HandShouminkans {
	type Item = HandStable;

	fn next(&mut self) -> Option<Self::Item> {
		// Note: `ms` is a copy of `self.ms`, because we want to yield new hands, not mutate `self`.
		let mut ms = self.ms.clone();

		let ts = shouminkans_next(&self.ts, &mut ms, &mut self.i)?;

		Some(HandStable(ts, ms))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		(0, Some(self.ms.len() - usize::from(self.i)))
	}
}

impl core::iter::FusedIterator for HandShouminkans {}

#[derive(Debug)]
#[derive_const(Clone)]
struct MinkousInner {
	ts: Tile37MultiSet,
	new_tile_is_red: bool,
	two_non_reds: Option<KanKouToiTile>,
	one_red_one_non_red: Option<KanKouToiTile>,
	two_reds: Option<KanKouToiTile>,
}

impl MinkousInner {
	fn new(ts: Tile37MultiSet, new_tile: Tile) -> Self {
		let new_tile_is_red = new_tile.is_red();
		let new_tile_non_red = new_tile.remove_red();

		let mut allowed_discards = ts.clone();
		allowed_discards.remove_all_ignore_red(new_tile_non_red);

		let (two_non_reds, one_red_one_non_red, two_reds) =
			if allowed_discards.is_empty() {
				(None, None, None)
			}
			else {
				let num_non_red = ts.get(new_tile_non_red);
				let num_red = new_tile_non_red.make_red().map_or(0, |new_tile_red| ts.get(new_tile_red));
				let two_non_reds = if num_non_red >= 2 { KanKouToiTile::new(new_tile_non_red, u8::from(new_tile_is_red)) } else { None };
				let one_red_one_non_red = if num_non_red >= 1 && num_red >= 1 { KanKouToiTile::new(new_tile_non_red, 1 + u8::from(new_tile_is_red)) } else { None };
				let two_reds = if num_red >= 2 { KanKouToiTile::new(new_tile_non_red, 2 + u8::from(new_tile_is_red)) } else { None };
				(two_non_reds, one_red_one_non_red, two_reds)
			};

		Self {
			ts,
			new_tile_is_red,
			two_non_reds,
			one_red_one_non_red,
			two_reds,
		}
	}

	fn next_inner(&self, t: KanKouToiTile) -> (Tile37MultiSet, HandMeld) {
		let mut ts = self.ts.clone();

		let t_non_red = t.tile();
		let t_red = t_non_red.make_red().unwrap_or(t_non_red);
		let num_t_red_to_remove = t.num_red_fives() - u8::from(self.new_tile_is_red);
		for _ in 0..num_t_red_to_remove {
			unsafe { core::hint::assert_unchecked(ts.remove(t_red)); }
		}
		for _ in num_t_red_to_remove..2 {
			unsafe { core::hint::assert_unchecked(ts.remove(t_non_red)); }
		}
		let m = HandMeld::Minkou(t);

		(ts, m)
	}
}

impl Iterator for MinkousInner {
	type Item = (Tile37MultiSet, HandMeld);

	fn next(&mut self) -> Option<Self::Item> {
		let t =
			self.two_non_reds.take()
			.or_else(|| self.one_red_one_non_red.take())
			.or_else(|| self.two_reds.take())?;
		Some(self.next_inner(t))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl DoubleEndedIterator for MinkousInner {
	fn next_back(&mut self) -> Option<Self::Item> {
		let t =
			self.two_reds.take()
			.or_else(|| self.one_red_one_non_red.take())
			.or_else(|| self.two_non_reds.take())?;
		Some(self.next_inner(t))
	}
}

impl ExactSizeIterator for MinkousInner {
	fn len(&self) -> usize {
		usize::from(self.two_non_reds.is_some()) + usize::from(self.one_red_one_non_red.is_some()) + usize::from(self.two_reds.is_some())
	}
}

impl core::iter::FusedIterator for MinkousInner {}

unsafe impl core::iter::TrustedLen for MinkousInner {}

/// An [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`] values formed by creating a minkou in the given hand using the given new tile.
#[derive(Clone, Debug)]
pub struct Minkous<const NT: usize, const NM: usize> {
	inner: MinkousInner,
	ms: [HandMeld; NM],
}

assert_size_of!(Minkous<1, 4>, 32);
assert_size_of!(Minkous<4, 3>, 32);
assert_size_of!(Minkous<7, 2>, 28);
assert_size_of!(Minkous<10, 1>, 28);
assert_size_of!(Minkous<13, 0>, 24);

impl<const NT: usize, const NM: usize> Minkous<NT, NM> {
	fn new(Hand(ts, ms): Hand<NT, NM>, new_tile: Tile) -> Self {
		let inner = MinkousInner::new(ts.into(), new_tile);
		Self { inner, ms }
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minkous<NT, NM> {
	type Item = Hand<core::gca!(SUB2::<NT>), core::gca!(ADD1::<NM>)>;

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next()?;

		let ts = ts.try_into();
		// SAFETY: Exactly 2 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(self.ms, m);

		Some(Hand(ts, ms))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Minkous<NT, NM> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next_back()?;

		let ts = ts.try_into();
		// SAFETY: Exactly 2 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(self.ms, m);

		Some(Hand(ts, ms))
	}
}

impl<const NT: usize, const NM: usize> ExactSizeIterator for Minkous<NT, NM> {
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minkous<NT, NM> {}

unsafe impl<const NT: usize, const NM: usize> core::iter::TrustedLen for Minkous<NT, NM> {}

/// An [`Iterator`] of [`HandTentative`] values formed by creating a minkou in the given hand using the given new tile.
#[derive(Clone, Debug)]
pub struct HandMinkous {
	inner: MinkousInner,
	ms: ArrayVec<HandMeld, 4>,
}

assert_size_of!(HandMinkous, 40);

impl HandMinkous {
	fn new(HandStable(ts, ms): HandStable, new_tile: Tile) -> Self {
		let inner = MinkousInner::new(ts, new_tile);
		Self { inner, ms }
	}
}

impl Iterator for HandMinkous {
	type Item = HandTentative;

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next()?;

		let mut ms = self.ms.clone();
		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some(HandTentative(ts, ms))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl DoubleEndedIterator for HandMinkous {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, m) = self.inner.next_back()?;

		let mut ms = self.ms.clone();
		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some(HandTentative(ts, ms))
	}
}

impl ExactSizeIterator for HandMinkous {
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl core::iter::FusedIterator for HandMinkous {}

unsafe impl core::iter::TrustedLen for HandMinkous {}

#[derive(Debug)]
#[derive_const(Clone)]
struct MinjunsInner {
	ts: Tile37MultiSet,
	new_tile: NumberTile,
	suit: NumberSuit,
	// | Bit i of |  first   |  second  |  third   | -> | other1  | other2  | new_tile |
	// | is_valid |          |          |          |    |         |         |          |
	// +==========+==========+==========+==========+====+=========+=========+==========+
	// |     0    | tm2      | tm1      | new_tile | -> | tm2     | tm1     | 34506789 |
	// |     1    | tm2      | tm1_red  | new_tile | -> | tm2     | tm1_red | 6        |
	// |     2    | tm2_red  | tm1      | new_tile | -> | tm2_red | tm1     | 7        |
	// |     3    | tm1      | new_tile | t1       | -> | tm1     | t1      | 23450678 |
	// |     4    | tm1      | new_tile | t1_red   | -> | tm1     | t1_red  | 4        |
	// |     5    | tm1_red  | new_tile | t1       | -> | tm1_red | t1      | 6        |
	// |     6    | new_tile | t1       | t2       | -> | t1      | t2      | 12345067 |
	// |     7    | new_tile | t1       | t2_red   | -> | t1      | t2_red  | 3        |
	// |     8    | new_tile | t1_red   | t2       | -> | t1_red  | t2      | 4        |
	is_valid: u16,
}

impl MinjunsInner {
	fn new(ts: Tile37MultiSet, new_tile: NumberTile, nt: usize) -> Self {
		// `IS_VALID_RED` is a mask indexed by `new_tile.number() >> 2` that indicates `other1` or `other2` being red.
		const IS_VALID_RED: [u16; 9] = {
			let mut result = [0_u16; 9];
			let mut i = 0;
			while i < result.len() {
				let number = i + 1;
				result[i] =
					(u16::from(number == 6) << 1) |
					(u16::from(number == 7) << 2) |
					(u16::from(number == 4) << 4) |
					(u16::from(number == 6) << 5) |
					(u16::from(number == 3) << 7) |
					(u16::from(number == 4) << 8);
				i += 1;
			}
			result
		};

		let NumberTileClassified { number, suit } = new_tile.into();
		let number_offset = u32::from((number as u8 - Number::N1 as u8) >> 2);

		let counts = ts.to_suits()[suit as usize];
		// Micro-optimization: This is the same as `counts | (counts << 1) | (counts << 2)`, which sets bit `3n + 2` if digit `n` is non-zero.
		// This is because each count is `0..=4`, so adding 3 to it sets the MSB of non-zero counts without any risk of overflowing
		// into an adjacent count.
		let present = counts + 0o3333333333;
		let present_non_red =
			((present & 0o0000044444) << 1) |
			((present & 0o4444000000) >> 2);
		let present_red =
			((present & 0o0000004444) << 1) |
			((present & 0o4444400000) >> 2);
		// Micro-optimization: We want to do operations on `present_red` and `present_non_red`, but we can save instructions by combining them into one value,
		// munging that, and then separating out the results.
		let present = (u64::from(present_red) << 30) | u64::from(present_non_red);
		// Bit `3n` is set if `ts` contains numbers `new_tile.number() + n - 2` and `new_tile.number() + n - 1`.
		// Eg if `new_tile.number() == Number::N1`, then bit 6 is set if `ts` contains `Number::N1` and `Number::N2`.
		//
		// Bit 0 is set if `ts` contains numbers `new_tile.number() - 2` and `new_tile.number() - 1`.
		// Bit 9 is set if `ts` contains numbers `new_tile.number() + 1` and `new_tile.number() + 2`.
		let one_away = (present & (present << 3)) >> (number_offset * 3);
		// Bit `3n` is set if `ts` contains numbers `new_tile.number() + n - 2` and `new_tile.number() + n`.
		// Eg if `new_tile.number() == Number::N1`, then bit 6 is set if `ts` contains `Number::N1` and `Number::N3`.
		//
		// Bit 3 is set if `ts` contains numbers `new_tile.number() - 1` and `new_tile.number() + 1`.
		let two_away = ((present << 3) & (present >> 3)) >> (number_offset * 3);
		#[expect(clippy::identity_op)]
		let others =
			// Bit 0 is set if `ts` contains numbers `new_tile.number() - 2` and `new_tile.number() - 1`.
			( one_away       & (0o001 * ((1 << 30) + 1))) |
			// Bit 3 is set if `ts` contains numbers `new_tile.number() - 1` and `new_tile.number() + 1`.
			( two_away       & (0o010 * ((1 << 30) + 1))) |
			// Bit 6 is set if `ts` contains numbers `new_tile.number() + 1` and `new_tile.number() + 2`.
			((one_away >> 3) & (0o100 * ((1 << 30) + 1)));
		#[expect(clippy::cast_possible_truncation)]
		let is_valid_non_red = others as u16;
		// Bit 0 is set if `ts` contains numbers `new_tile.number() - 2` and `new_tile.number() - 1`.
		// Bit 3 is set if `ts` contains numbers `new_tile.number() - 1` and `new_tile.number() + 1`.
		// Bit 6 is set if `ts` contains numbers `new_tile.number() + 1` and `new_tile.number() + 2`.
		#[expect(clippy::cast_possible_truncation)]
		let is_valid_red = (others >> 30) as u16;
		// Bits 1 and 2 are set if `ts` contains numbers `new_tile.number() - 2` and `new_tile.number() - 1`.
		// Bits 4 and 5 are set if `ts` contains numbers `new_tile.number() - 1` and `new_tile.number() + 1`.
		// Bits 7 and 8 are set if `ts` contains numbers `new_tile.number() + 1` and `new_tile.number() + 2`.
		let is_valid_red = (is_valid_red << 2) | (is_valid_red << 1);
		// Bits remain set if they correspond to a shun containing a red five.
		let is_valid_red = is_valid_red & IS_VALID_RED[number_offset as usize];
		let mut is_valid = is_valid_non_red | is_valid_red;

		if usize::from(ts.len()[suit as usize]) == nt {
			// Other suits have no tiles, so there is a chance that kuikae-nashi will leave no tile available to discard after the call.

			let counts_non_red =
				( counts       & 0o000077777) +
				((counts >> 3) & 0o777770000);
			let counts_non_red = (u64::from(counts_non_red) << 9) >> (number_offset * 3);
			let count_tm3 = (counts_non_red & 0o7) as usize;
			let count_new_tile = ((counts_non_red >> 9) & 0o7) as usize;
			let count_t3 = ((counts_non_red >> 18) & 0o7) as usize;
			if count_new_tile + count_tm3 + 2 == nt {
				is_valid &= 0o770;
			}
			if count_new_tile + 2 == nt {
				is_valid &= 0o707;
			}
			if count_new_tile + count_t3 + 2 == nt {
				is_valid &= 0o077;
			}
		}

		Self { ts, new_tile, suit, is_valid }
	}

	fn next_inner(&self, i: u32) -> (Tile37MultiSet, HandMeld, Option<NumberTile>) {
		// shun_type => 0o<t2><t1>0<tm1><tm2>
		const OTHERS: [u16; 3] = [
			0o00011,
			0o01010,
			0o11000,
		];

		unsafe { core::hint::assert_unchecked(i <= 8); }

		let mut ts = self.ts.clone();

		// 0 => tm2, tm1, new_tile
		// 1 => tm1, new_tile, t1
		// 2 => new_tile, t1, t2
		let shun_type = i / 3;
		let contains_five_red = ((0o666 >> i) & 0b1) != 0;

		let number_offset = u32::from((self.new_tile.number() as u8 - Number::N1 as u8) >> 2);
		let new_tile_non_red = Tile::from(self.new_tile).remove_red() as u8;

		let counts_others = (u64::from(OTHERS[shun_type as usize]) << (number_offset * 3)) >> 6;
		#[expect(clippy::cast_possible_truncation)]
		let counts_others = counts_others as u32;
		let counts_others =
			( counts_others & 0o000001111) |
			((counts_others & 0o000010000) << (if contains_five_red { 3 } else { 0 })) |
			((counts_others & 0o111100000) << 3);
		let counts = ts.to_suits()[self.suit as usize] - counts_others;

		unsafe { ts.remove_two_from_suit(self.suit, counts); }

		#[expect(clippy::cast_possible_truncation)]
		let t_representative =
			new_tile_non_red.wrapping_add_signed((shun_type as i8 - 2) << 2) |
			u8::from(contains_five_red || Tile::from(self.new_tile).is_red());
		let t_representative = unsafe { core::mem::transmute::<u8, ShunTile>(t_representative) };
		let m = HandMeld::Minjun(t_representative);

		let counts_non_red =
			( counts       & 0o000077777) +
			((counts >> 3) & 0o777770000);
		// Shun type n => tile (tm3 + 3n) cannot be discarded.
		// Bit 3n is set => tile (tm3 + n) cannot be discarded.
		//
		// Shun type 0 (tm2, tm1, new_tile) => bit 0 set => tm3 cannot be discarded
		// Shun type 1 (tm1, new_tile, t1)  => no bits set => anything can be discarded
		// Shun type 2 (new_tile, t1, t2)   => bit 18 set => t3 cannot be discarded
		let cannot_discard = (0o7_u64 << (shun_type * 9)) & 0o7000007;
		#[expect(clippy::cast_possible_truncation)]
		let cannot_discard = ((cannot_discard << (number_offset * 3)) >> 9) as u32;
		#[expect(clippy::cast_possible_truncation)]
		let cannot_discard = ((counts_non_red & cannot_discard) != 0).then(|| unsafe { core::mem::transmute::<u8, NumberTile>(new_tile_non_red.wrapping_add_signed(((shun_type as i8 - 1) * 3) << 2)) });

		(ts, m, cannot_discard)
	}
}

impl Iterator for MinjunsInner {
	type Item = (Tile37MultiSet, HandMeld, Option<NumberTile>);

	fn next(&mut self) -> Option<Self::Item> {
		let i = self.is_valid.lowest_one()?;
		self.is_valid &= !(0b1 << i);
		Some(self.next_inner(i))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl DoubleEndedIterator for MinjunsInner {
	fn next_back(&mut self) -> Option<Self::Item> {
		let i = self.is_valid.highest_one()?;
		self.is_valid &= !(0b1 << i);
		Some(self.next_inner(i))
	}
}

impl ExactSizeIterator for MinjunsInner {
	fn len(&self) -> usize {
		self.is_valid.count_ones() as usize
	}
}

impl core::iter::FusedIterator for MinjunsInner {}

unsafe impl core::iter::TrustedLen for MinjunsInner {}

/// An [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`] values formed by creating a minjun in the given hand using the given new tile.
///
/// Along with the `Hand`, the iterator element optionally contains a tile that is not allowed to be discarded due to kuikae-nashi.
/// This is in addition to `new_tile` which is implicitly not allowed to be discarded due to kuikae-nashi.
/// Note that kuikae comparisons should use `[CmpIgnoreRed::eq_ignore_red](crate::CmpIgnoreRed::eq_ignore_red)`.
#[derive(Clone, Debug)]
pub struct Minjuns<const NT: usize, const NM: usize> {
	inner: MinjunsInner,
	ms: [HandMeld; NM],
}

assert_size_of!(Minjuns<1, 4>, 32);
assert_size_of!(Minjuns<4, 3>, 32);
assert_size_of!(Minjuns<7, 2>, 28);
assert_size_of!(Minjuns<10, 1>, 28);
assert_size_of!(Minjuns<13, 0>, 24);

impl<const NT: usize, const NM: usize> Minjuns<NT, NM> {
	fn new(Hand(ts, ms): Hand<NT, NM>, new_tile: NumberTile) -> Self {
		let inner = MinjunsInner::new(ts.into(), new_tile, NT);
		Self { inner, ms }
	}
}

impl<const NT: usize, const NM: usize> Iterator for Minjuns<NT, NM> {
	type Item = (Hand<core::gca!(SUB2::<NT>), core::gca!(ADD1::<NM>)>, Option<NumberTile>);

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, m, cannot_discard) = self.inner.next()?;

		let ts = ts.try_into();
		// SAFETY: Exactly 2 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(self.ms, m);

		Some((Hand(ts, ms), cannot_discard))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl<const NT: usize, const NM: usize> DoubleEndedIterator for Minjuns<NT, NM> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, m, cannot_discard) = self.inner.next_back()?;

		let ts = ts.try_into();
		// SAFETY: Exactly 2 elements were removed from `ts`.
		let ts = unsafe { ts.unwrap_unchecked() };

		let ms = append(self.ms, m);

		Some((Hand(ts, ms), cannot_discard))
	}
}

impl<const NT: usize, const NM: usize> ExactSizeIterator for Minjuns<NT, NM> {
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl<const NT: usize, const NM: usize> core::iter::FusedIterator for Minjuns<NT, NM> {}

unsafe impl<const NT: usize, const NM: usize> core::iter::TrustedLen for Minjuns<NT, NM> {}

/// An [`Iterator`] of [`HandTentative`] values formed by creating a minjun in the given hand using the given new tile.
///
/// Along with the `HandTentative`, the iterator element optionally contains a tile that is not allowed to be discarded due to kuikae-nashi.
/// This is in addition to `new_tile` which is implicitly not allowed to be discarded due to kuikae-nashi.
/// Note that kuikae comparisons should use `[CmpIgnoreRed::eq_ignore_red](crate::CmpIgnoreRed::eq_ignore_red)`.
#[derive(Clone, Debug)]
pub struct HandMinjuns {
	inner: MinjunsInner,
	ms: ArrayVec<HandMeld, 4>,
}

assert_size_of!(HandMinjuns, 40);

impl HandMinjuns {
	fn new(HandStable(ts, ms): HandStable, new_tile: NumberTile) -> Self {
		let nt = 13 - 3 * ms.len();
		let inner = MinjunsInner::new(ts, new_tile, nt);
		Self { inner, ms }
	}
}

impl Iterator for HandMinjuns {
	type Item = (HandTentative, Option<NumberTile>);

	fn next(&mut self) -> Option<Self::Item> {
		let (ts, m, cannot_discard) = self.inner.next()?;

		let mut ms = self.ms.clone();
		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some((HandTentative(ts, ms), cannot_discard))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl DoubleEndedIterator for HandMinjuns {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (ts, m, cannot_discard) = self.inner.next_back()?;

		let mut ms = self.ms.clone();
		let result = ms.push(m);
		unsafe { result.unwrap_unchecked(); }

		Some((HandTentative(ts, ms), cannot_discard))
	}
}

impl ExactSizeIterator for HandMinjuns {
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl core::iter::FusedIterator for HandMinjuns {}

unsafe impl core::iter::TrustedLen for HandMinjuns {}

/// An [`Iterator`] of [`ScorableHand`]s that can be created from the original [`HandStable`] and the given drawn / called tile.
#[derive(Clone, Debug)]
pub enum HandScorableHands {
	One(core::option::IntoIter<ScorableHandRegular>),
	Four(Hand4ScorableHands),
	Seven(Hand7ScorableHands),
	Ten(Hand10ScorableHands),
	Thirteen(Hand13ScorableHands),
}

assert_size_of!(HandScorableHands, 104);

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
	pub(crate) fn new(ts: &Tile37MultiSet) -> Self {
		debug_assert_eq!(core::simd::num::SimdUint::reduce_sum(core::simd::Simd::from_array(ts.len())), 13);

		let (wait, duplicate) = Self::new_inner(ts);
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
		const LSB: u64 = ((0b1 << (3 * 13)) - 1) / 7;

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
	let ToChiitoiInner::SingleUnpaired { one_red_five_mask, two_red_fives_mask, pair_is, unpaired } = ToChiitoiInner::new(ts.as_ref()) else { return None; };
	let mut ps = [const { core::mem::MaybeUninit::uninit() }; 6];
	// SAFETY: Requirements satisfied by construction in `ToChiitoiInner::new`.
	unsafe { chiitoi_extract_pair_representatives(&mut ps, one_red_five_mask, two_red_fives_mask, pair_is); }
	let ps = unsafe { core::mem::MaybeUninit::array_assume_init(ps) };
	Some((ps, unpaired))
}

fn tenhou_to_chiitoi(ts: &Tile37CountedMultiSet<14>) -> Option<ScorableHandChiitoi> {
	let ToChiitoiInner::AllPaired { one_red_five_mask, two_red_fives_mask, pair_is } = ToChiitoiInner::new(ts.as_ref()) else { return None; };
	let mut ps = [const { core::mem::MaybeUninit::uninit() }; 7];
	// SAFETY: Requirements satisfied by construction in `ToChiitoiInner::new`.
	unsafe { chiitoi_extract_pair_representatives(&mut ps, one_red_five_mask, two_red_fives_mask, pair_is); }
	let [p1, p2, p3, p4, p5, p6, p7] = unsafe { core::mem::MaybeUninit::array_assume_init(ps) };
	Some(ScorableHandChiitoi { pairs: [p1, p2, p3, p4, p5, p6], p7, tsumo_or_ron: TsumoOrRon::Tsumo })
}

#[derive(Copy)]
#[derive_const(Clone)]
enum ToChiitoiInner {
	Invalid,
	SingleUnpaired { one_red_five_mask: u64, two_red_fives_mask: u64, pair_is: u64, unpaired: Tile },
	AllPaired { one_red_five_mask: u64, two_red_fives_mask: u64, pair_is: u64 },
}

impl ToChiitoiInner {
	fn new(ts: &Tile37MultiSet) -> Self {
		fn new_inner(ts: &Tile37MultiSet) -> Option<(u32, u64, u64, u64, core::simd::Simd<u32, 4>)> {
			const LSB: u32 = ((0b1 << (3 * 9)) - 1) / 7;

			let ts34 = Tile34MultiSet::from(ts.clone());
			let counts = ts34.to_suits_simd();
			let counts_b0 = counts & core::simd::Simd::splat(LSB);
			let eq2 = {
				let b1 = (counts >> 1) & core::simd::Simd::splat(LSB);
				!counts_b0 & b1
			};
			let num_pairs = core::simd::num::SimdUint::reduce_sum(core::simd::num::SimdUint::count_ones(eq2));

			if num_pairs != 6 && num_pairs != 7 {
				return None;
			}

			let [one_red_five_mask, two_red_fives_mask] =
				[1, 2].map(|min|
					(u64::from(ts.get(t!(0m)) >= min) << Tile::offset(t!(5m))) |
					(u64::from(ts.get(t!(0p)) >= min) << Tile::offset(t!(5p))) |
					(u64::from(ts.get(t!(0s)) >= min) << Tile::offset(t!(5s)))
				);

			let mut pair_is = eq2;
			for p in pair_is.as_mut_array() {
				*p = extract_bits32::<0, 1, 3, 9>(*p);
			}
			let pair_is = core::simd::num::SimdUint::cast::<u64>(pair_is) << core::simd::Simd::from_array([0, 9, 18, 27]);
			let pair_is = core::simd::num::SimdUint::reduce_or(pair_is);

			Some((num_pairs, one_red_five_mask, two_red_fives_mask, pair_is, counts_b0))
		}

		let Some((num_pairs, one_red_five_mask, two_red_fives_mask, pair_is, counts_b0)) = new_inner(ts) else { return Self::Invalid; };
		if num_pairs == 7 {
			return Self::AllPaired { one_red_five_mask, two_red_fives_mask, pair_is };
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
		let unpaired = (((suit as u8) * 9 + (offset / 3) as u8) << 2) + t!(1m) as u8;
		let unpaired = unsafe { core::mem::transmute::<u8, Tile>(unpaired) };
		let unpaired =
			if ts.contains(unpaired) { unpaired }
			else if let Some(unpaired) = unpaired.make_red() && ts.contains(unpaired) { unpaired }
			else { unsafe { core::hint::unreachable_unchecked(); } };
		Self::SingleUnpaired { one_red_five_mask, two_red_fives_mask, pair_is, unpaired }
	}
}

/// # Safety
///
/// Requires `pair_is <= (1 << 34) - 1` and `pair_is.count_ones() == result.len()`.
unsafe fn chiitoi_extract_pair_representatives(
	result: &mut [core::mem::MaybeUninit<ScorableHandPair>],
	one_red_five_mask: u64,
	two_red_fives_mask: u64,
	mut pair_is: u64,
) {
	let ones = core::iter::from_fn(|| {
		let i = pair_is.lowest_one();
		// SAFETY: Function safety contract requires `pair_is.count_ones() == result.len()`.
		let i = unsafe { i.unwrap_unchecked() };
		pair_is &= !(0b1 << i);
		Some(i)
	});
	for (r, i) in result.iter_mut().zip(ones) {
		#[expect(clippy::cast_possible_truncation)]
		let num_red_fives = (((one_red_five_mask >> i) & 0b1) + ((two_red_fives_mask >> i) & 0b1)) as u8;
		#[expect(clippy::cast_possible_truncation)]
		let t = ((i as u8) << 2) + t!(1m) as u8;
		// SAFETY: Function safety contract requires `pair_is <= (1 << 34) - 1`.
		let t = unsafe { core::mem::transmute::<u8, Tile>(t) };
		let t = KanKouToiTile::new(t, num_red_fives);
		let t = unsafe { t.unwrap_unchecked() };
		r.write(ScorableHandPair(t));
	}
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	use super::*;

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
		assert_eq!(minkous.size_hint(), (1, Some(1)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 3m 3m 3m 4m 4m 4m 5m 5m { minkou 2m 2m 2m }));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous2() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(5m));
		assert_eq!(minkous.size_hint(), (1, Some(1)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 5m }));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous3() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let mut minkous = h.find_minkous(t!(0m));
		assert_eq!(minkous.size_hint(), (1, Some(1)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 0m }));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous4() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 0m);
		let mut minkous = h.find_minkous(t!(5m));
		assert_eq!(minkous.size_hint(), (1, Some(1)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m { minkou 5m 5m 0m }));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous5() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m 5m 5m);
		let mut minkous = h.find_minkous(t!(0m));
		assert_eq!(minkous.size_hint(), (1, Some(1)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minkous6() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m 5m 0m);
		let mut minkous = h.find_minkous(t!(5m));
		assert_eq!(minkous.size_hint(), (2, Some(2)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 0m { minkou 5m 5m 5m }));
		assert_eq!(minkous.size_hint(), (1, Some(1)));
		assert_eq!(minkous.next().unwrap(), make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 5m { minkou 5m 5m 0m }));
		assert_eq!(minkous.size_hint(), (0, Some(0)));
		core::assert_matches!(minkous.next(), None);
		assert_eq!(minkous.size_hint(), (0, Some(0)));
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let mut minjuns = h.find_minjuns(tn!(4m));
		assert_eq!(minjuns.size_hint(), (5, Some(5)));
		assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 5m 0m 6m 7m 8m E E E G G { minjun 4m 2m 3m }), Some(tn!(1m))));
		assert_eq!(minjuns.size_hint(), (4, Some(4)));
		assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 0m 6m 7m 8m E E E G G { minjun 4m 3m 5m }), None));
		assert_eq!(minjuns.size_hint(), (3, Some(3)));
		assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 5m 6m 7m 8m E E E G G { minjun 4m 3m 0m }), None));
		assert_eq!(minjuns.size_hint(), (2, Some(2)));
		assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 3m 0m 7m 8m E E E G G { minjun 4m 5m 6m }), Some(tn!(7m))));
		assert_eq!(minjuns.size_hint(), (1, Some(1)));
		assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 3m 5m 7m 8m E E E G G { minjun 4m 0m 6m }), Some(tn!(7m))));
		assert_eq!(minjuns.size_hint(), (0, Some(0)));
		core::assert_matches!(minjuns.next(), None);
		assert_eq!(minjuns.size_hint(), (0, Some(0)));
	}

	// Ref: https://riichi.wiki/index.php?title=Kuikae&oldid=29176
	#[test]
	fn kuikae1() {
		{
			let h = make_hand!(1p 2p 3p E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(2p));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(2p E E E S S S W W W N { minjun 2p 1p 3p }), None));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }), None));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1s 2s 3s E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(1s));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1s E E E S S S W W W N { minjun 1s 2s 3s }), None));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(4m));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1m E E E S S S W W W N { minjun 4m 2m 3m }), Some(tn!(1m))));
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
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 4m 5m 6m E E E S S S W { minjun 4m 2m 3m }), Some(tn!(1m))));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 4m 6m E E E S S S W { minjun 4m 3m 5m }), None));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 3m 4m E E E S S S W { minjun 4m 5m 6m }), None));
			core::assert_matches!(minjuns.next(), None);
		}

		{
			let h = make_hand!(1m 2m 3m 4m 5m 6m E E E S S S W);
			let mut minjuns = h.find_minjuns(tn!(7m));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(1m 2m 3m 4m E E E S S S W { minjun 7m 5m 6m }), Some(tn!(4m))));
			core::assert_matches!(minjuns.next(), None);
		}
	}

	#[test]
	fn kuikae2() {
		// Red five doesn't matter for kuikae-nashi.
		{
			let h = make_hand!(0m 6m 7m E E E S S S W W W N);
			let mut minjuns = h.find_minjuns(tn!(8m));
			assert_eq!(minjuns.next().unwrap(), (make_hand!(0m E E E S S S W W W N { minjun 8m 6m 7m }), Some(tn!(5m))));
			core::assert_matches!(minjuns.next(), None);
		}
		{
			let h = make_hand!(3m 4m 5m 5m { minkou E E E } { minkou S S S } { minkou W W W });
			let mut minjuns = h.find_minjuns(tn!(0m));
			core::assert_matches!(minjuns.next(), None);
		}
		{
			let h = make_hand!(3m 4m 5m 0m { minkou E E E } { minkou S S S } { minkou W W W });
			let mut minjuns = h.find_minjuns(tn!(5m));
			core::assert_matches!(minjuns.next(), None);
		}
	}

	#[test]
	fn tenpai() {
		{
			let h = make_hand!(5p 6p 0s 6s 7s 8s 8s Wh Wh Wh { minkou R R R });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![4p, 7p]);
		}

		{
			let h = make_hand!(4m 5m 6p 7p 8p 1s 2s 3s 4s 5s 6s 8s 8s);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![3m, 6m]);
		}

		{
			let h = make_hand!(1m 1m 4p 4p { minkou N N N } { minkou 3p 3p 3p } { minkou R R R });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![1m, 4p]);
		}

		{
			let h = make_hand!(1m 1m 4m 5m 6m 3p 4p 4p 0p 6p 1s 2s 3s);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![2p, 5p]);
		}

		{
			let h = make_hand!(4m 4m 1p 2p 3p 0p 5p 1s 2s 3s { minjun 1m 2m 3m });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![4m, 5p]);
		}

		{
			let h = make_hand!(3p 3p 4p 4p 0p 5p 7p 8p 8p 8p 9p G G);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![8p, G]);
		}

		{
			let h = make_hand!(4m 0m 6m 7m 7m 4s 0s 6s 7s 8s { minjun 4p 5p 6p });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![3s, 6s, 9s]);
		}

		{
			let h = make_hand!(1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m]);
		}

		{
			let h = make_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R]);
		}

		{
			let h = make_hand!(1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![S]);
		}

		// Red five
		{
			let h = make_hand!(1m 1m 2m 2m 2m 3m 3m 3m 4p 5p 5p 5p 6p);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![1m, 4m, 0p]);
		}

		// Red five
		{
			let h = make_hand!(5m 5m 0m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![5m, 6m, 7m, 8m]);
		}

		// Red five
		{
			let h = make_hand!(5m 5m 5m 6m 6m 7m 7m { minjun 1p 2p 3p } { minjun 1p 2p 3p });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![0m, 6m, 7m, 8m]);
		}

		// Four copies of a tile at the start of a run
		{
			let h = make_hand!(4m 4m 4m 4m 5m 6m 6m 7m E E Wh Wh Wh);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![5m, 0m, 8m]);
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand. Not considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 1m 1m 1m 3m 4m 5m 3p 4p 5p 3s 4s 5s);
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![]);
		}

		// Karaten nuance: waiting for 1m but already have 4x 1m in hand, but only 1x 1m in unmelded tiles. Considered to be in tenpai for fifth 1m.
		{
			let h = make_hand!(1m 3m 4m 5m 3p 4p 5p 3s 4s 5s { minkou 1m 1m 1m });
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![1m]);
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
			assert_eq!(h.tenpai(&Tile37MultiSet::INVENTORY_YONMA_111), t37set![8p]);
		}
	}
}
