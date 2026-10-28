use crate::{
	HandMeld,
	NumberTile,
	ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile, Tile34MultiSet, Tile34Set, Tile37CountedMultiSet, TsumoOrRon,
	WindTile,
};
use crate::hand::ToKokushiMusou;

/// A hand that has been divided into melds, pairs, etc and can be scored.
///
/// [`ScorableHand::score`] produces the best possible score for this hand.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means:
///
/// - For `Regular`, the `ScorableHandRegular` is consistent. See its docs for details.
///
/// - For `Chiitoi`, the `ScorableHandChiitoi` is consistent. See its docs for details.
///
/// - For `KokushiMusou`, the `ScorableHandKokushiMusou` is consistent. See its docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Copy, Ord, PartialOrd)]
#[derive_const(Clone, Eq, PartialEq)]
pub enum ScorableHand {
	/// Regular hand shape containing four melds and one pair.
	Regular(ScorableHandRegular),

	/// Chiitoi hand shape containing seven pairs.
	Chiitoi(ScorableHandChiitoi),

	/// Kokushi musou hand shape containing one of each terminal and honor tile and one duplicate.
	KokushiMusou(ScorableHandKokushiMusou),
}

/// Regular hand shape containing four melds and one pair.
///
/// The fourth meld indicates what type of wait this hand had.
///
/// # Safety
///
/// This type expects that its fields are consistent. This means:
///
/// - All [`ScorableHandMeld`]s and the [`ScorableHandFourthMeld`] are themselves consistent.
///   See their docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Copy, Ord, PartialOrd)]
#[derive_const(Clone, Eq, PartialEq)]
// Enforce field order.
//
// `m1`, `m2` and `m3` are `repr(align(2))`, m4 is `repr(align(4))`, and `pair` is `repr(align(1))`.
// Without `repr(C)`, rustc lays them out as `m4:m1:m2:m3:pair`, which has the diadvantage that `m4` comes before the other `m*`s.
// This means any operation that wants to vectorize over all the melds ignoring the fourth meld's wait, like operations on `self.melds_simd()`,
// must do reads at offsets of 0, 4, 6, 8 which does not stride.
//
// By using `repr(C)` we can force the fields to be laid out in order so that `self.melds_simd()` can interpret the 2..10 bytes of `self` as `[ScorableHandMeld; 4]`.
// Also `self.melds_and_pair_simd()` can interpret the 0..10 bytes as `[ScorableHandMeld; 5]`.
#[repr(C)]
pub struct ScorableHandRegular {
	pub pair: ScorableHandRegularPair,
	pub m1: ScorableHandMeld,
	pub m2: ScorableHandMeld,
	pub m3: ScorableHandMeld,
	pub m4: ScorableHandFourthMeld,
}

/// Chiitoi hand shape containing seven pairs.
///
/// # Safety
///
/// This type expects that its fields are consistent. This means:
///
/// - All [`ScorableHandPair`]s are themselves consistent. See its docs for details.
///
/// - Mo two pairs have the same tiles.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Copy, Ord, PartialOrd)]
#[derive_const(Eq, PartialEq)]
#[repr(C)]
pub struct ScorableHandChiitoi {
	pub pairs: [ScorableHandPair; 6],
	pub p7: ScorableHandPair,
	pub tsumo_or_ron: TsumoOrRon,
}

/// Kokushi musou hand shape containing one of each terminal and honor tile and one duplicate.
///
/// This type expects that its fields are consistent. This means that the `duplicate` and `t14` tiles are valid for a kokushi musou hand.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Copy, Ord, PartialOrd)]
#[derive_const(Clone, Eq, PartialEq)]
pub struct ScorableHandKokushiMusou {
	pub duplicate: Tile,
	pub t14: Tile,
	pub tsumo_or_ron: TsumoOrRon,
}

#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(C, align(2))] // See comment in `ScorableHandMeld::cmp`.
pub struct ScorableHandRegularPair {
	pub tag: ScorableHandRegularPairTag,
	pub inner: ScorableHandPair,
}

#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ScorableHandRegularPairTag {
	// Same tags as `ScorableHandMeld::Ankou` and `Menkou`, so that a pair can pretend to be an ankou or menkou for algorithms that benefit from it (`fn chanta_routou()`).
	//
	// It also makes `ScorableHandRegular` store its discriminant in this field instead of any other. If this tag was not there,
	// the discriminant would be stored in `ScorableHandRegular::m1`, which would push `ScorableHandChiitoi` and `ScorableHandKokushiMusou` variant data
	// to offset 3 instead of offset 1.
	//
	// `Mintoi` implies the hand had a tanki wait and won by ron. No algorithm cares about the difference between an open or closed pair;
	// the difference only matters for tracking tanki ron.
	Antoi = 2,
	Mintoi = 3,
}

/// A single meld inside a [`ScorableHand`].
///
/// Only the representative tile is held, since that is sufficient to uniquely determine the whole meld.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Copy)]
#[derive_const(Clone)]
#[repr(C, u8, align(2))] // See comment in `ScorableHandMeld::cmp`.
pub enum ScorableHandMeld {
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

	/// Closed triplet held in hand.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Ankou(Tile) = 2,

	/// Open triplet formed by pon.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkou(Tile) = 3,

	/// Closed sequence held in hand.
	Anjun(ShunLowTileAndHasFiveRed) = 4,

	/// Open sequence formed by chii.
	Minjun(ShunLowTileAndHasFiveRed) = 5,
}

/// The fourth meld of a [`ScorableHand::Regular`]. In addition to the content of the meld, this indicates what wait the hand had.
///
/// Only the representative tile of the meld is held, since that is sufficient to uniquely determine the whole meld.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Copy)]
#[derive_const(Clone)]
#[repr(C, u8, align(4))] // See comment in `ScorableHandFourthMeld::cmp`.
pub enum ScorableHandFourthMeld {
	/// Closed quad formed by kan.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Ankan(Tile, KanWait) = 0,

	/// Open quad formed by kan.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkan(Tile, KanWait) = 1,

	/// Closed triplet held in hand.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Ankou(Tile, KouWait) = 2,

	/// Open triplet formed by pon.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkou(Tile, KouWait) = 3,

	/// Closed sequence held in hand.
	Anjun(ShunLowTileAndHasFiveRed, ShunWait) = 4,

	/// Open sequence formed by chii.
	Minjun(ShunLowTileAndHasFiveRed, ShunWait) = 5,
}

#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum KanWait {
	Tanki = 0,
}

#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum KouWait {
	/// This meld was already complete. One of the tiles of the [`ScorableHandRegular::pair`] was the wait.
	Tanki = 0,

	/// This meld is a kou and one of its tiles completed the hand.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	///
	/// Eg 111m => 1m completed the hand.
	Shanpon = 1,
}

#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ShunWait {
	/// This meld was already complete. One of the tiles of the [`ScorableHandRegular::pair`] was the wait.
	Tanki = 0,

	/// This meld is a shun and had a middle wait.
	///
	/// Eg 123m => 2m completed the hand.
	Kanchan = 1,

	/// This meld is a shun and had a one-sided wait.
	///
	/// Eg 123m => 3m completed the hand, 789p => 7p completed the hand.
	Penchan = 2,

	/// This meld is a shun and had a double-sided wait. The lowest number tile (the first tile) completed the hand.
	///
	/// Eg 123m => 1m completed the hand, 234m => 2m completed the hand, 678p => 6p completed the hand.
	RyanmenLow = 3,

	/// This meld is a shun and had a double-sided wait. The highest number tile (the last tile) completed the hand.
	///
	/// Eg 234m => 4m completed the hand, 678p => 8p completed the hand, 789p => 9p completed the hand.
	RyanmenHigh = 4,
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(unused)] // Constructed via `transmute`
pub(crate) enum ScorableHandFourthMeldDw {
	AnkanTanki = 0,
	MinkanTanki = 1,
	AnkouTanki = 2,
	MinkouTanki = 3,
	AnjunTanki = 4,
	MinjunTanki = 5,
	AnkouShanpon = 6,
	MinkouShanpon = 7,
	AnjunKanchan = 8,
	MinjunKanchan = 9,
	AnjunPenchan = 12,
	MinjunPenchan = 13,
	AnjunRyanmenLow = 16,
	MinjunRyanmenLow = 17,
	AnjunRyanmenHigh = 20,
	MinjunRyanmenHigh = 21,
}

/// A single pair inside a [`ScorableHand`].
///
/// Only one of the tiles in the pair is held, since that is sufficient to uniquely determine the whole pair.
///
/// If the pair is of one `Five` and one `FiveRed` tile, then the `FiveRed` is held.
/// Thus if the held tile is a `FiveRed`, the other tile in the pair is assumed to be a `Five`.
#[derive(Copy)]
#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ScorableHandPair(pub Tile);

assert_size_of!(ScorableHand, 12);
assert_size_of!(ScorableHandRegular, 12);
assert_size_of!(ScorableHandChiitoi, 8);
assert_size_of!(ScorableHandKokushiMusou, 3);
assert_size_of!(ScorableHandMeld, 2);
assert_size_of!(ScorableHandFourthMeld, 4);
assert_size_of!(ScorableHandPair, 1);

impl ScorableHand {
	pub const fn set_tsumo_or_ron(&mut self, tsumo_or_ron: TsumoOrRon) {
		let dst = match self {
			Self::Regular(h) => { h.set_tsumo_or_ron(tsumo_or_ron); return; },
			Self::Chiitoi(h) => &mut h.tsumo_or_ron,
			Self::KokushiMusou(h) => &mut h.tsumo_or_ron,
		};
		*dst = tsumo_or_ron;
	}

	pub(crate) fn for_each_tile(&self, f: impl FnMut(Tile)) {
		match self {
			Self::Regular(h) => h.for_each_tile(f),
			Self::Chiitoi(h) => h.for_each_tile(f),
			Self::KokushiMusou(h) => h.for_each_tile(f),
		}
	}
}

impl core::fmt::Debug for ScorableHand {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHand {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			Self::Regular(h) => h.fmt(f),
			Self::Chiitoi(h) => h.fmt(f),
			Self::KokushiMusou(h) => h.fmt(f),
		}
	}
}

impl From<ScorableHandRegular> for ScorableHand {
	fn from(h: ScorableHandRegular) -> Self {
		Self::Regular(h)
	}
}

impl From<ScorableHandChiitoi> for ScorableHand {
	fn from(h: ScorableHandChiitoi) -> Self {
		Self::Chiitoi(h)
	}
}

impl From<ScorableHandKokushiMusou> for ScorableHand {
	fn from(h: ScorableHandKokushiMusou) -> Self {
		Self::KokushiMusou(h)
	}
}

impl ScorableHandRegular {
	pub fn new(ma: ScorableHandMeld, mb: ScorableHandMeld, mc: ScorableHandMeld, md: ScorableHandFourthMeld, pair: ScorableHandPair, tsumo_or_ron: TsumoOrRon) -> Self {
		let (m1, m2, m3, m4, pair_tag) =
			if let Some(md) = md.to_tanki() {
				let mut ms = [ma, mb, mc, md];
				SortingNetwork::sort(&mut ms);
				let [m1, m2, m3, m4] = ms;
				let pair_tag = match tsumo_or_ron {
					TsumoOrRon::Tsumo => ScorableHandRegularPairTag::Antoi,
					TsumoOrRon::Ron => ScorableHandRegularPairTag::Mintoi,
				};
				(m1, m2, m3, ScorableHandFourthMeld::tanki(m4), pair_tag)
			}
			else {
				let mut m123 = [ma, mb, mc];
				SortingNetwork::sort(&mut m123);
				let [m1, m2, m3] = m123;
				(m1, m2, m3, md, ScorableHandRegularPairTag::Antoi)
			};
		Self { pair: ScorableHandRegularPair { tag: pair_tag, inner: pair }, m1, m2, m3, m4 }
	}

	pub const fn set_tsumo_or_ron(&mut self, tsumo_or_ron: TsumoOrRon) {
		let d =
			if self.m4.is_tanki() {
				<*mut _>::cast::<u8>(&raw mut self.pair.tag)
			}
			else {
				<*mut ScorableHandFourthMeld>::cast::<u8>(&raw mut self.m4)
			};
		let d = unsafe { &mut *d };
		*d = (*d & !0b1) | tsumo_or_ron as u8;
	}

	fn for_each_tile(&self, mut f: impl FnMut(Tile)) {
		for m in self.melds() {
			m.for_each_tile(&mut f);
		}
		self.pair.inner.for_each_tile(f);
	}

	const fn melds(&self) -> &[ScorableHandMeld; 4] {
		let ms = unsafe { <*const Self>::byte_add(self, core::mem::offset_of!(Self, m1)) };
		unsafe { &*<*const ScorableHandRegular>::cast::<[ScorableHandMeld; 4]>(ms) }
	}

	pub(crate) fn melds_simd(&self) -> (core::simd::Simd<u8, 4>, core::simd::Simd<u8, 4>) {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10]>(self) };
		let this = core::simd::Simd::<_, 8>::from_slice(&this[2..]);
		let ds = core::simd::simd_swizzle!(this, [0, 2, 4, 6]);
		let ts = core::simd::simd_swizzle!(this, [1, 3, 5, 7]);
		(ds, ts)
	}

	fn melds_and_pair_simd(&self) -> (core::simd::Simd<u8, 5>, core::simd::Simd<u8, 5>) {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10]>(self) };
		let this = core::simd::Simd::from_array(*this);
		let ds = core::simd::simd_swizzle!(this, [0, 2, 4, 6, 8]);
		let ts = core::simd::simd_swizzle!(this, [1, 3, 5, 7, 9]);
		(ds, ts)
	}

	pub(crate) fn is_menzen(&self) -> bool {
		let (ds, _) = self.melds_simd();
		let is_closed = core::simd::num::SimdUint::reduce_or(ds.extract::<0, 3>()) & 0b1 == 0b0;
		is_closed & self.m4.is_menzen()
	}

	pub(crate) fn is_pinfu(&self, round_wind: WindTile, seat_wind: WindTile) -> bool {
		// Micro-optimization: This match is the proper impl, but it generates many branches. We can do better with some comparisons on the discriminants and waits.
		//
		//     matches!(
		//         self,
		//         Self {
		//             m1: ScorableHandMeld::Anjun(_),
		//             m2: ScorableHandMeld::Anjun(_),
		//             m3: ScorableHandMeld::Anjun(_),
		//             m4: ScorableHandFourthMeld::Anjun(_, ShunWait::RyanmenLow | ShunWait::RyanmenHigh) | ScorableHandFourthMeld::Minjun(_, ShunWait::RyanmenLow | ShunWait::RyanmenHigh),
		//             pair,
		//         } if pair.inner.num_yakuhai(round_wind, seat_wind) == 0,
		//     )
		let (ds, _) = self.melds_simd();
		let [_, _, m4_w] = self.m4.parts();
		// Self::Anjun == 4
		core::simd::cmp::SimdPartialEq::simd_eq(ds.extract::<0, 3>(), core::simd::Simd::splat(4)).all() &&
			// Don't need to check `m4_d == Anjun || m4_d == Minjun`, because the `ShunWait::Ryanmen*` values are not used by any `KanWait` or `KouWait` vriants.
			(m4_w == ShunWait::RyanmenLow as u8 || m4_w == ShunWait::RyanmenHigh as u8) &&
			(self.pair.inner.num_yakuhai(round_wind, seat_wind) == 0)
	}

	pub(crate) fn peikou_isshoku_jun(&self) -> PeikouIsshokuJun {
		let (ds, ts) = self.melds_simd();
		PeikouIsshokuJun::new(ds, ts, self.is_menzen())
	}

	pub(crate) fn chanta_routou(&self) -> ChantaRoutou {
		const SHUN_TERMINALS: Tile34Set = t34set![1m, 7m, 1p, 7p, 1s, 7s];

		let (ds, ts) = self.melds_and_pair_simd();
		let masks = Tile::masks(Tile::offsets(ts));

		let is_shun = core::simd::cmp::SimdPartialOrd::simd_ge(ds, core::simd::Simd::splat(4));
		let shun_terminals_contains_t = core::simd::cmp::SimdPartialEq::simd_ne(masks & SHUN_TERMINALS.simd_splat(), core::simd::Simd::splat(0));
		let kan_kou_terminals_contains_t = core::simd::cmp::SimdPartialEq::simd_ne(masks & Tile34Set::TERMINALS.simd_splat(), core::simd::Simd::splat(0));
		let kan_kou_honors_contains_t = core::simd::cmp::SimdPartialEq::simd_ne(masks & Tile34Set::HONORS.simd_splat(), core::simd::Simd::splat(0));
		let chanta_routous = core::simd::Select::select(
			is_shun,
			core::simd::Select::select(
				shun_terminals_contains_t,
				core::simd::Simd::splat(ChantaRoutou::has_terminals().0),
				core::simd::Simd::splat(ChantaRoutou::other().0),
			),
			core::simd::Select::select(
				kan_kou_terminals_contains_t,
				core::simd::Simd::splat(ChantaRoutou::all_terminals().0),
				core::simd::Select::select(
					kan_kou_honors_contains_t,
					core::simd::Simd::splat(ChantaRoutou::all_honors().0),
					core::simd::Simd::splat(ChantaRoutou::other().0),
				),
			),
		);

		let result = core::simd::num::SimdUint::reduce_or(chanta_routous);
		ChantaRoutou(result)
	}

	pub(crate) fn num_wind_yakuhai(&self, round_wind: WindTile, seat_wind: WindTile) -> [u8; 4] {
		let (_, ts) = self.melds_simd();
		let is_round_wind = core::simd::cmp::SimdPartialEq::simd_eq(ts, core::simd::Simd::splat(round_wind as u8)).any();
		let is_seat_wind = core::simd::cmp::SimdPartialEq::simd_eq(ts, core::simd::Simd::splat(seat_wind as u8)).any();
		let result =
			(u32::from(is_round_wind) << ((round_wind as u8 - tw!(E) as u8) << 2)) +
			(u32::from(is_seat_wind) << ((seat_wind as u8 - tw!(E) as u8) << 2));
		result.to_le_bytes()
	}

	pub(crate) fn is_dragon_yakuhai(&self) -> [bool; 3] {
		const DRAGONS: core::simd::Simd<u64, 3> = core::simd::Simd::from_array([t34set![Wh].present, t34set![G].present, t34set![R].present]);

		let (_, ts) = self.melds_simd();
		let masks = Tile::masks::<u64, _>(Tile::offsets(ts));
		let masks = core::simd::num::SimdUint::reduce_or(masks);
		let masks = core::simd::Simd::splat(masks);
		let masks = masks & DRAGONS;
		let matches = core::simd::cmp::SimdPartialEq::simd_ne(masks, core::simd::Simd::splat(0));
		matches.to_array()
	}

	pub(crate) fn is_shiiaru_raotai(&self) -> bool {
		let (ds, _) = self.melds_simd();
		let is_ankan = core::simd::cmp::SimdPartialEq::simd_eq(ds, core::simd::Simd::splat(0));
		let is_open = core::simd::cmp::SimdPartialEq::simd_ne(ds & core::simd::Simd::splat(0b1), core::simd::Simd::splat(0b0));
		let is_fully_open = (is_ankan | is_open).all();
		is_fully_open & self.m4.is_tanki()
	}

	pub(crate) fn iisou(&self) -> Iisou {
		let (ds, ts) = self.melds_and_pair_simd();
		Iisou::new(ds, ts)
	}

	pub(crate) fn is_sanshoku_doujun(&self) -> bool {
		let (ds, ts) = self.melds_simd();
		let is_shun = core::simd::cmp::SimdPartialOrd::simd_ge(ds, core::simd::Simd::splat(4));
		Self::is_sanshoku(is_shun, ts)
	}

	pub(crate) fn ittsuukansen(&self) -> IttsuuKanSen {
		let (ds, ts) = self.melds_and_pair_simd();
		IttsuuKanSen::new(ds, ts, self.is_menzen())
	}

	pub(crate) fn is_toitoi(&self) -> bool {
		let (ds, _) = self.melds_simd();
		core::simd::num::SimdUint::reduce_or(ds) <= 3
	}

	pub(crate) fn num_ankou(&self) -> NumAnkou {
		let (ds, _) = self.melds_simd();
		NumAnkou::new(ds, self.m4.is_tanki())
	}

	pub(crate) fn is_sanshoku_doukou(&self) -> bool {
		let (ds, ts) = self.melds_simd();
		let is_kan_kou = core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(3));
		let is_number_tile = core::simd::cmp::SimdPartialOrd::simd_le(ts, core::simd::Simd::splat(t!(9s) as u8));
		Self::is_sanshoku(is_kan_kou & is_number_tile, ts)
	}

	pub(crate) fn num_kantsu(&self) -> NumKantsu {
		let (ds, _) = self.melds_simd();
		NumKantsu::new(ds)
	}

	pub(crate) fn suushii_sangen(&self) -> SuushiiSangen {
		let (_, ts) = self.melds_simd();
		SuushiiSangen::new(ts, self.pair.inner.0)
	}

	pub(crate) fn num_renkou(&self) -> NumRenkou {
		let (ds, ts) = self.melds_simd();
		NumRenkou::new(ds, ts)
	}

	pub(crate) fn is_akadora_sanshoku(&self) -> bool {
		let (_, ts) = self.melds_and_pair_simd();
		is_akadora_sanshoku(ts)
	}

	pub(crate) fn is_uumensai(&self) -> bool {
		let (_, ts) = self.melds_and_pair_simd();
		let suits = Tile::suits5(ts);
		let masks = core::simd::Simd::splat(0b1) << suits;
		let mask = core::simd::num::SimdUint::reduce_or(masks);
		mask == 0b11111
	}

	pub(crate) fn honchinitsu(&self) -> Honchinitsu {
		let (_, ts) = self.melds_and_pair_simd();
		Honchinitsu::new(ts)
	}

	pub(crate) fn num_chuuren_poutou(&self) -> u8 {
		fn sub(counts: &mut core::simd::Simd<u8, 9>, mask: u16) {
			*counts = core::simd::Select::select(
				core::simd::Mask::<i8, _>::from_bitmask(mask.into()),
				core::simd::num::SimdUint::saturating_sub(
					*counts,
					core::simd::Simd::splat(1),
				),
				*counts,
			);
		}

		let (ds, ts) = self.melds_and_pair_simd();

		let suits = Tile::suits4(ts);
		let masks = core::simd::Simd::splat(0b1) << suits;
		let mask = core::simd::num::SimdUint::reduce_or(masks);
		let is_valid = (0b0000000000010110 >> mask) & 0b1;
		if is_valid == 0 { return 0; }

		let is_ankou = core::simd::cmp::SimdPartialEq::simd_eq(ds.extract::<1, 3>(), core::simd::Simd::splat(2));
		let is_anjun = core::simd::cmp::SimdPartialEq::simd_eq(ds.extract::<1, 3>(), core::simd::Simd::splat(4));
		let is_other = !is_ankou & !is_anjun;
		if is_other.any() { return 0; }

		let n1s = ts - core::simd::Simd::splat(suits[0] * (t!(1p) as u8 - t!(1m) as u8) + t!(1m) as u8);
		let n1s = n1s >> 1;

		let mut counts = core::simd::Simd::<u8, _>::from_array([3, 1, 1, 1, 1, 1, 1, 1, 3]);

		{
			let n1s = n1s.extract::<1, 3>();

			let m123_n1s = core::simd::Simd::splat(0b1) << core::simd::num::SimdUint::cast::<u16>(n1s);
			let [m1_n1, m2_n1, m3_n1] = m123_n1s.to_array();
			sub(&mut counts, m1_n1);
			sub(&mut counts, m2_n1);
			sub(&mut counts, m3_n1);

			let m123_n2s = core::simd::Select::select(is_anjun, n1s + core::simd::Simd::splat(1), n1s);
			let m123_n2s = core::simd::Simd::splat(0b1) << core::simd::num::SimdUint::cast::<u16>(m123_n2s);
			let [m1_n2, m2_n2, m3_n2] = m123_n2s.to_array();
			sub(&mut counts, m1_n2);
			sub(&mut counts, m2_n2);
			sub(&mut counts, m3_n2);

			let m123_n3s = core::simd::Select::select(is_anjun, n1s + core::simd::Simd::splat(2), n1s);
			let m123_n3s = core::simd::Simd::splat(0b1) << core::simd::num::SimdUint::cast::<u16>(m123_n3s);
			let [m1_n3, m2_n3, m3_n3] = m123_n3s.to_array();
			sub(&mut counts, m1_n3);
			sub(&mut counts, m2_n3);
			sub(&mut counts, m3_n3);
		}

		let pair_n = n1s[0];
		let m4_n = n1s[4];
		// Micro-optimization: `match m4 { ... }` generates a multi-level jump table. `match m4.dw()` generates a simple single-level one.
		let m4_pair_ns = match self.m4.dw() {
			ScorableHandFourthMeldDw::AnkanTanki |
			ScorableHandFourthMeldDw::MinkanTanki |
			ScorableHandFourthMeldDw::MinkouTanki |
			ScorableHandFourthMeldDw::MinjunTanki => return 0,

			ScorableHandFourthMeldDw::AnkouTanki => [m4_n, m4_n, m4_n, pair_n, pair_n],

			ScorableHandFourthMeldDw::AnjunTanki => [m4_n, m4_n + 1, m4_n + 2, pair_n, pair_n],

			ScorableHandFourthMeldDw::AnkouShanpon |
			ScorableHandFourthMeldDw::MinkouShanpon => [m4_n, m4_n, pair_n, pair_n, m4_n],

			ScorableHandFourthMeldDw::AnjunKanchan |
			ScorableHandFourthMeldDw::MinjunKanchan => [m4_n, m4_n + 2, pair_n, pair_n, m4_n + 1],

			ScorableHandFourthMeldDw::AnjunPenchan |
			ScorableHandFourthMeldDw::MinjunPenchan => [m4_n + u8::from(m4_n != 0), m4_n + 1 + u8::from(m4_n != 0), pair_n, pair_n, m4_n + u8::from(m4_n == 0) * 2],

			ScorableHandFourthMeldDw::AnjunRyanmenLow |
			ScorableHandFourthMeldDw::MinjunRyanmenLow => [m4_n + 1, m4_n + 2, pair_n, pair_n, m4_n],

			ScorableHandFourthMeldDw::AnjunRyanmenHigh |
			ScorableHandFourthMeldDw::MinjunRyanmenHigh => [m4_n, m4_n + 1, pair_n, pair_n, m4_n + 2],
		};
		let m4_pair_ns = core::simd::Simd::from_array(m4_pair_ns);
		let m4_pair_ns = core::simd::Simd::splat(0b1) << core::simd::num::SimdUint::cast::<u16>(m4_pair_ns);
		let [old1, old2, old3, old4, new] = m4_pair_ns.to_array();

		sub(&mut counts, old1);
		sub(&mut counts, old2);
		sub(&mut counts, old3);
		sub(&mut counts, old4);
		let complete_without_new_tile = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::splat(0)).all();

		sub(&mut counts, new);
		let complete = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::splat(0)).all();

		if complete { 1 + u8::from(complete_without_new_tile) } else { 0 }
	}

	pub(crate) fn is_hyakuman_goku(&self) -> bool {
		let (ds, ts) = self.melds_and_pair_simd();

		let valid = core::simd::cmp::SimdPartialOrd::simd_le(ts, core::simd::Simd::splat(t!(9m) as u8));
		if !valid.all() {
			return false;
		}

		let ds = ds.extract::<1, 4>();
		let ns = Tile::offsets(ts);
		let pair_value = (ns[0] + 1) * 2;
		let ns = ns.extract::<1, 4>();
		let kan_values = (ns + core::simd::Simd::splat(1)) * core::simd::Simd::splat(4);
		let kou_values = (ns + core::simd::Simd::splat(1)) * core::simd::Simd::splat(3);
		let shun_values = (ns + core::simd::Simd::splat(2)) * core::simd::Simd::splat(3);

		let values =
			core::simd::Select::select(
				core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(1)),
				kan_values,
				core::simd::Select::select(
					core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(3)),
					kou_values,
					shun_values,
				),
			);
		let values = pair_value + core::simd::num::SimdUint::reduce_sum(values);

		values >= 100
	}

	pub(crate) fn is_golden_gate_bridge(&self) -> bool {
		const MASK: u32 = 0b001010101_u32;

		let (ds, ts) = self.melds_simd();
		let is_shun = core::simd::cmp::SimdPartialOrd::simd_ge(ds, core::simd::Simd::splat(4));
		let masks = Tile::masks::<u32, _>(Tile::offsets(ts));
		let counts = core::simd::Select::select(is_shun, masks, core::simd::Simd::splat(0));
		let counts = core::simd::num::SimdUint::reduce_or(counts);
		let counts = core::simd::Simd::splat(counts);
		let counts = counts >> core::simd::Simd::from_array([0, 9, 18]);
		let counts = counts & core::simd::Simd::splat(MASK);
		self.is_menzen() && core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::splat(MASK)).any()
	}

	fn is_sanshoku(is_valid: core::simd::Mask<i8, 4>, ts: core::simd::Simd::<u8, 4>) -> bool {
		const MASK: u64 = 0b000000001_000000001_000000001_000000001_000000001_u64;

		let offsets = Tile::offsets(ts);

		let masks = Tile::masks::<u32, _>(offsets);
		let masks = core::simd::Select::select(is_valid, masks, core::simd::Simd::splat(0));
		let counts = core::simd::num::SimdUint::reduce_or(masks);

		let masks = core::simd::Simd::splat(MASK) << core::simd::num::SimdUint::cast::<u64>(offsets);
		let masks = masks >> 18;
		let masks = core::simd::num::SimdUint::cast::<u32>(masks);
		let expected = masks & core::simd::Simd::splat((1 << 27) - 1);
		let actual = masks & core::simd::Simd::splat(counts);
		let is_valid = is_valid.cast::<i32>() & core::simd::cmp::SimdPartialEq::simd_eq(expected, actual);
		is_valid.any()
	}
}

impl core::fmt::Debug for ScorableHandRegular {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandRegular {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self { pair, m1, m2, m3, m4 } = self;
		write!(f, "{m1} {m2} {m3} {m4} {pair}")
	}
}

impl ScorableHandRegularPair {
	pub const fn antoi(pair_representative: Tile) -> Self {
		Self {
			tag: ScorableHandRegularPairTag::Antoi,
			inner: ScorableHandPair(pair_representative),
		}
	}

	pub const fn mintoi(pair_representative: Tile) -> Self {
		Self {
			tag: ScorableHandRegularPairTag::Mintoi,
			inner: ScorableHandPair(pair_representative),
		}
	}
}

impl core::fmt::Debug for ScorableHandRegularPair {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandRegularPair {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str("{ ")?;
		self.inner.try_for_each_tile(|t| write!(f, "{t} "))?;
		f.write_str(&"ron }"[(match self.tag {
			ScorableHandRegularPairTag::Antoi => 4,
			ScorableHandRegularPairTag::Mintoi => 0,
		})..])
	}
}

impl ScorableHandChiitoi {
	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		for p in self.pairs {
			p.for_each_tile(&mut f);
		}
		self.p7.for_each_tile(&mut f);
	}

	pub(crate) fn is_toipuutao(self) -> bool {
		let ts = self.tiles_simd();
		let masks = Tile::masks(Tile::offsets(ts));
		let is_valid = core::simd::cmp::SimdPartialEq::simd_ne(masks & Tile34Set::REVERSIBLE.simd_splat(), core::simd::Simd::splat(0));
		is_valid.all()
	}

	pub(crate) fn chanta_routou(self) -> ChantaRoutou {
		let ts = self.tiles_simd();
		let masks = Tile::masks(Tile::offsets(ts));

		let terminals_contains_t = core::simd::cmp::SimdPartialEq::simd_ne(masks & Tile34Set::TERMINALS.simd_splat(), core::simd::Simd::splat(0));
		let honors_contains_t = core::simd::cmp::SimdPartialEq::simd_ne(masks & Tile34Set::HONORS.simd_splat(), core::simd::Simd::splat(0));
		let chanta_routous = core::simd::Select::select(
			terminals_contains_t,
			core::simd::Simd::splat(ChantaRoutou::all_terminals().0),
			core::simd::Select::select(
				honors_contains_t,
				core::simd::Simd::splat(ChantaRoutou::all_honors().0),
				core::simd::Simd::splat(ChantaRoutou::other().0),
			),
		);

		let result = core::simd::num::SimdUint::reduce_or(chanta_routous);
		ChantaRoutou(result)
	}

	pub(crate) fn is_uumensai(self) -> bool {
		let ts = self.tiles_simd();
		let suits = Tile::suits5(ts);
		let masks = core::simd::Simd::splat(0b1) << suits;
		let mask = core::simd::num::SimdUint::reduce_or(masks);
		mask == 0b11111
	}

	pub(crate) fn is_akadora_sanshoku(self) -> bool {
		is_akadora_sanshoku(self.tiles_simd())
	}

	pub(crate) fn honchinitsu(self) -> Honchinitsu {
		Honchinitsu::new(self.tiles_simd())
	}

	pub(crate) fn dairin_kokuiisou(self) -> DairinKokuiisou {
		DairinKokuiisou::new(self.tiles_simd())
	}

	fn tiles_simd(self) -> core::simd::Simd<u8, 7> {
		let ts = unsafe { <*const Self>::byte_add(&raw const self, core::mem::offset_of!(Self, pairs)) };
		let ts = <*const Self>::cast::<[ScorableHandPair; 7]>(ts);
		let ts = unsafe { &*ts };
		core::simd::Simd::from_array(ts.map(|ScorableHandPair(t)| t as u8))
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl Clone for ScorableHandChiitoi {
	fn clone(&self) -> Self {
		*self
	}
}

impl core::fmt::Debug for ScorableHandChiitoi {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandChiitoi {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self { pairs: [p1, p2, p3, p4, p5, p6], p7, tsumo_or_ron } = self;
		write!(f, "{p1} {p2} {p3} {p4} {p5} {p6} {{ ")?;
		p7.try_for_each_tile(|t| write!(f, "{t} "))?;
		f.write_str(&"ron }"[(match tsumo_or_ron {
			TsumoOrRon::Tsumo => 4,
			TsumoOrRon::Ron => 0,
		})..])
	}
}

impl ScorableHandKokushiMusou {
	pub fn new(ts: &Tile37CountedMultiSet<13>, t14: Tile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		ToKokushiMusou::new(ts).with_new_tile(t14, tsumo_or_ron)
	}

	pub(crate) fn num_kokushi_musou(self) -> u8 {
		if self.duplicate == self.t14 { 2 } else { 1 }
	}

	pub(crate) fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		f(t!(1m));
		f(t!(9m));
		f(t!(1p));
		f(t!(9p));
		f(t!(1s));
		f(t!(9s));
		f(t!(E));
		f(t!(S));
		f(t!(W));
		f(t!(N));
		f(t!(Wh));
		f(t!(G));
		f(t!(R));
		f(self.duplicate);
	}
}

impl core::fmt::Debug for ScorableHandKokushiMusou {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandKokushiMusou {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let mut ts = Tile34MultiSet::TERMINALS_AND_HONORS;
		ts.insert(self.duplicate);
		ts.remove(self.t14);
		for (t, n) in ts {
			write!(f, "{t} ")?;
			if n.get() > 1 {
				write!(f, "{t} ")?;
			}
		}

		self.t14.fmt(f)?;

		f.write_str(&" ron"[..(match self.tsumo_or_ron {
			TsumoOrRon::Tsumo => 0,
			TsumoOrRon::Ron => 4,
		})])
	}
}

impl ScorableHandMeld {
	/// Construct a `ScorableHandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub const fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Ankan(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub const fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Minkan(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankou`](Self::Ankou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub const fn ankou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Ankou(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub const fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Minkou(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Anjun`](Self::Anjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn anjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Anjun(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Minjun(t))
	}

	/// `[d, t]`
	const fn parts(self) -> [u8; 2] {
		let m = unsafe { core::mem::transmute::<Self, [core::mem::MaybeUninit<u8>; core::mem::size_of::<Self>()]>(self) };
		let m = unsafe { core::mem::MaybeUninit::array_assume_init(m) };
		// Remove bounds check in callers that use `d` to index an array.
		unsafe { core::hint::assert_unchecked(m[0] <= 5); }
		unsafe { core::hint::assert_unchecked(m[1] <= t!(R) as u8); }
		m
	}

	pub(crate) fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		#[expect(clippy::unit_arg)]
		self.try_for_each_tile::<!>(|t| Ok(f(t)));
	}

	fn try_for_each_tile<E>(self, mut f: impl FnMut(Tile) -> Result<(), E>) -> Result<(), E> {
		match self {
			Self::Ankan(t1) |
			Self::Minkan(t1) => {
				let t_rest = t1.remove_red();
				f(t_rest)?;
				f(t_rest)?;
				f(t_rest)?;
				f(t1)?;
			},

			Self::Ankou(t1) |
			Self::Minkou(t1) => {
				let t_rest = t1.remove_red();
				f(t_rest)?;
				f(t_rest)?;
				f(t1)?;
			},

			Self::Anjun(t) |
			Self::Minjun(t) => {
				let (t1, t2, t3) = t.shun();
				f(t1.into())?;
				f(t2.into())?;
				f(t3.into())?;
			}
		}
		Ok(())
	}
}

impl core::fmt::Debug for ScorableHandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		// Micro-optimization: `f.write_str(match self { ... })` causes each string to be stored as a separate constant
		// that then needs to be looked up from a LUT. The same happens for the length of each string.
		// Making a single string and indexing it manually avoids that first load, and calculating the length using arithmetic avoids the second.
		const STRINGS: &str = "\
			{ ankan ?\
			{ minkan \
			{ ankou ?\
			{ minkou \
			{ anjun ?\
			{ minjun \
		";

		let [d, ..] = self.parts();
		let start = usize::from(d) * 9;
		let len = 8 + usize::from(d & 0b1);
		let end = start + len;
		// Micro-optimization: rustc does not notice that all the ranges are valid and emits a str slice check, so assert that they are valid.
		unsafe { core::hint::assert_unchecked(end <= STRINGS.len()); }
		let s = &STRINGS[start..end];
		f.write_str(s)?;
		self.try_for_each_tile(|t| write!(f, "{t} "))?;
		f.write_str("}")
	}
}

const impl From<HandMeld> for ScorableHandMeld {
	fn from(meld: HandMeld) -> Self {
		match meld {
			HandMeld::Ankan(t) => Self::Ankan(t),
			HandMeld::Minkan(t) => Self::Minkan(t),
			HandMeld::Minkou(t) => Self::Minkou(t),
			HandMeld::Minjun(t) => Self::Minjun(t),
		}
	}
}

/// Converts a `ScorableHandFourthMeld` to a `ScorableHandMeld` by ignoring the wait.
const impl From<ScorableHandFourthMeld> for ScorableHandMeld {
	fn from(meld: ScorableHandFourthMeld) -> Self {
		*meld.as_ref()
	}
}

const impl Eq for ScorableHandMeld {}

const impl Ord for ScorableHandMeld {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		const fn sort_criteria(m: ScorableHandMeld) -> u16 {
			// To look nice when displaying a `ScorableHand`, we want to sort first based on the tiles, and only then on the type of meld.
			// This means sorting the shun 123m before the kou 222m before the shun 234m.
			//
			// For comparing the tiles, we only need to compare the first tile of the melds and can ignore the rest.
			// The kou 222m and the shun 234m have the same first tile, and kous are sorted before shuns, so 222m will be sorted before 234m as desired.
			// Comparing more than the first tile isn't necessary because the other tiles cannot change the comparison derived from the first tile and the meld type.
			//
			// Some combinations of melds cannot happen if the melds came from a single hand, eg there cannot be two kous / kans with the same tiles
			// since that would require six or more of the same tile. However there is no guarantee that we're comparing `ScorableHandMeld`s belonging to the same hand,
			// so we cannot optimize based on this.

			// Micro-optimization:
			//
			// If we do `(self_tile, self_discriminant).cmp(&(other_tile, other_discriminant))`,
			// rustc generates branch-heavy code that compares each tuple element separately.
			//
			// Since `ScorableHandMeld` is `repr(C, u8, align(2))`, it is legal to type-pun `Self` to `u16`,
			// reorder it to put the fields according to comparison priority, and then do a single `u16` comparison.
			// In fact the fields are already in the right order if we do a LE read.
			u16::from_le_bytes(m.parts())
		}

		let sc = sort_criteria(*self);
		let sc_other = sort_criteria(*other);
		sc.cmp(&sc_other)
	}
}

const impl PartialEq for ScorableHandMeld {
	fn eq(&self, other: &Self) -> bool {
		// Micro-optimization: We don't want to use `derive(PartialEq)` because the auto-generated impl has the branchy element-by-element comparison problem
		// mentioned in `ScorableHandMeld::cmp` above.
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

const impl PartialOrd for ScorableHandMeld {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl ScorableHandFourthMeld {
	/// Construct a [`ScorableHandFourthMeld::Ankou`] or [`ScorableHandFourthMeld::Minkou`] using the given kou representative tile, `TsumoOrRon` flag and `KouWait` wait.
	pub const fn kou(t: Tile, tsumo_or_ron: TsumoOrRon, wait: KouWait) -> Self {
		match tsumo_or_ron {
			TsumoOrRon::Tsumo => Self::Ankou(t, wait),
			TsumoOrRon::Ron => Self::Minkou(t, wait),
		}
	}

	/// Construct a [`ScorableHandFourthMeld::Ankou`] or [`ScorableHandFourthMeld::Minkou`] with a [`KouWait::Shanpon`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub const fn shanpon(t1: Tile, t2: Tile, t3: Tile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::kou(t, tsumo_or_ron, KouWait::Shanpon))
	}

	/// Construct a [`ScorableHandFourthMeld::Ankou`] or [`ScorableHandFourthMeld::Minkou`] using the given shun representative tile, `TsumoOrRon` flag and `ShunWait` wait.
	pub const fn shun(t: ShunLowTileAndHasFiveRed, tsumo_or_ron: TsumoOrRon, wait: ShunWait) -> Self {
		match tsumo_or_ron {
			TsumoOrRon::Tsumo => Self::Anjun(t, wait),
			TsumoOrRon::Ron => Self::Minjun(t, wait),
		}
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::Kanchan`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn kanchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::Kanchan))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::Penchan`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn penchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::Penchan))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::RyanmenLow`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn ryanmen_low(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::RyanmenLow))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::RyanmenHigh`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub const fn ryanmen_high(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::RyanmenHigh))
	}

	/// Converts a [`ScorableHandMeld`] to a `ScorableHandFourthMeld` with a `Tanki` wait.
	pub const fn tanki(meld: ScorableHandMeld) -> Self {
		match meld {
			ScorableHandMeld::Ankan(t) => Self::Ankan(t, KanWait::Tanki),
			ScorableHandMeld::Minkan(t) => Self::Minkan(t, KanWait::Tanki),
			ScorableHandMeld::Ankou(t) => Self::Ankou(t, KouWait::Tanki),
			ScorableHandMeld::Minkou(t) => Self::Minkou(t, KouWait::Tanki),
			ScorableHandMeld::Anjun(t) => Self::Anjun(t, ShunWait::Tanki),
			ScorableHandMeld::Minjun(t) => Self::Minjun(t, ShunWait::Tanki),
		}
	}

	pub(crate) const fn to_tanki(self) -> Option<ScorableHandMeld> {
		// TODO(rustup): Use `bool::then` when that becomes `const fn`.
		if self.is_tanki() {
			Some(self.into())
		}
		else {
			None
		}
	}

	pub(crate) const fn is_tanki(self) -> bool {
		// Micro-optimization: rustc generates silly code for `match self { Foo(_, wait) => matches!(wait, Wait::Tanki), ... }` and
		// and `let w = match self { Foo(_, wait) => wait as u8, ... }` and `let w = match self { Foo(_, wait) => unsafe { transmute::<_, u8>)(wait), ... }`
		// where it tries to mask the value with a different constant depending on the discriminant of `self`.
		// Since all the enums are `repr(u8)` and all define `Tanki` as 0, such masking is unnecessary.
		//
		// This method of punning the waits to `u8` avoids that masking.
		let w = match &self {
			ScorableHandFourthMeld::Ankan(_, wait) |
			ScorableHandFourthMeld::Minkan(_, wait) => <*const KanWait>::cast::<u8>(wait),
			ScorableHandFourthMeld::Ankou(_, wait) |
			ScorableHandFourthMeld::Minkou(_, wait) => <*const KouWait>::cast::<u8>(wait),
			ScorableHandFourthMeld::Anjun(_, wait) |
			ScorableHandFourthMeld::Minjun(_, wait) => <*const ShunWait>::cast::<u8>(wait),
		};
		// SAFETY: All `*Wait` enums are `repr(u8)`.
		let w = unsafe { *w };
		w == 0
	}

	/// `[d, t, w]`
	pub(crate) const fn parts(self) -> [u8; 3] {
		let m = unsafe { core::mem::transmute::<Self, [core::mem::MaybeUninit<u8>; core::mem::size_of::<Self>()]>(self) };
		let result = [unsafe { m[0].assume_init() }, unsafe { m[1].assume_init() }, unsafe { m[2].assume_init() }];
		// Remove bounds check in callers that use `d` to index an array.
		unsafe { core::hint::assert_unchecked(result[0] <= 5); }
		unsafe { core::hint::assert_unchecked(result[1] <= t!(R) as u8); }
		unsafe { core::hint::assert_unchecked(result[2] <= 4); }
		result
	}

	/// Returns an integer uniquely representing the `d` and `w` fields.
	pub(crate) const fn dw(self) -> ScorableHandFourthMeldDw {
		let [d, _, w] = self.parts();
		let result = d + w * 4;
		unsafe { core::mem::transmute::<u8, ScorableHandFourthMeldDw>(result) }
	}

	const fn is_menzen(self) -> bool {
		// Micro-optimization: This match is the proper impl, but it generates a jump table. We can do better with some comparisons on the discriminants and waits.
		//
		//     match self {
		//         Self::Ankan(..) |
		//         Self::Ankou(..) |
		//         Self::Anjun(..) |
		//         Self::Minkou(_, KouWait::Shanpon) |
		//         Self::Minjun(_, ShunWait::Kanchan | ShunWait::Penchan | ShunWait::RyanmenLow | ShunWait::RyanmenHigh)
		//             => true,
		//
		//         Self::Minkan(..) |
		//         Self::Minkou(_, KouWait::Tanki) |
		//         Self::Minjun(_, ShunWait::Tanki)
		//             => false,
		//     }
		//
		// Comparing the parts individually makes rustc generate shifts to extract the individual parts from the 4B loaded value of `self`.
		// Doing the comparison on the `u32` formed from `self`'s bytes generates a single mask and comparison on the whole 4B loaded value.
		// That is, rustc is smart enough to generate the AND mask as `0x00_07_00_01` .
		let [d, _, w] = self.parts();
		let masked = u32::from_ne_bytes([d & 0b1, 0, w, 0]);
		masked != u32::from_ne_bytes([0b1, 0, 0, 0])
	}
}

impl core::fmt::Debug for ScorableHandFourthMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

/// Converts a `ScorableHandFourthMeld` to a `ScorableHandMeld` by ignoring the wait.
const impl AsRef<ScorableHandMeld> for ScorableHandFourthMeld {
	fn as_ref(&self) -> &ScorableHandMeld {
		unsafe { &*<*const Self>::cast::<ScorableHandMeld>(self) }
	}
}

impl core::fmt::Display for ScorableHandFourthMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		// Micro-optimization: `f.write_str(match self { ... })` causes each string to be stored as a separate constant
		// that then needs to be looked up from a LUT or via a jump table. The same happens for the length of each string.
		// Making a single string and indexing it manually avoids that first load, and calculating the length using arithmetic avoids the second.
		const PREFIX_STRINGS: &str = "\
			{ ankan ?\
			{ minkan \
			{ ankou ?\
			{ minkou \
			{ anjun ?\
			{ minjun \
		";
		const SUFFIX_STRINGS: &str = "\
			}?????????????\
			shanpon }?????\
			kanchan }?????\
			penchan }?????\
			ryanmen_low }?\
			ryanmen_high }\
		";

		let [d, ..] = self.parts();
		let start = usize::from(d) * 9;

		// TODO(rustup): Load-bearing assert. For some reason this assert is required to prevent rustc from emitting an unnecessary assert for `d != 7`.
		// It needs to be exactly `d < 6`; `d <= 5` (already present in `fn parts()`) or `start <= end` don't work.
		// It needs to be exactly here; moving it above the `let start = ...` assignment stops working.
		unsafe { core::hint::assert_unchecked(d < 6); }

		let len = 8 + usize::from(d & 0b1);
		let end = start + len;
		// Micro-optimization: rustc does not notice that all the ranges are valid and emits a str slice check, so assert that they are valid.
		unsafe { core::hint::assert_unchecked(end <= PREFIX_STRINGS.len()); }
		let s = &PREFIX_STRINGS[start..end];
		f.write_str(s)?;

		self.as_ref().try_for_each_tile(|t| write!(f, "{t} "))?;

		let dw = self.dw() as u8;
		let start = (5 - (usize::from(dw < 6) + usize::from(dw < 8) + usize::from(dw < 12) + usize::from(dw < 16) + usize::from(dw < 20))) * 14;
		let len = 14 - (usize::from(dw < 6) * 8 + usize::from(dw < 16) * 4 + usize::from(dw < 20));
		let end = start + len;
		// Micro-optimization: rustc does not notice that all the ranges are valid and emits a str slice check, so assert that they are valid.
		unsafe { core::hint::assert_unchecked(start <= end); }
		unsafe { core::hint::assert_unchecked(end <= SUFFIX_STRINGS.len()); }
		let s = &SUFFIX_STRINGS[start..end];
		f.write_str(s)
	}
}

const impl Eq for ScorableHandFourthMeld {}

const impl Ord for ScorableHandFourthMeld {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		const fn sort_criteria(m: ScorableHandFourthMeld) -> u32 {
			// Micro-optimization:
			//
			// If we do `(self_tile, self_discriminant, self_wait).cmp(&(other_tile, other_discriminant, other_wait))`,
			// rustc generates branch-heavy code that compares each tuple element separately.
			//
			// Since `ScorableHandFourthMeld` is `repr(C, u8, align(4))` and because we want to ignore the padding byte,
			// it is legal to type-pun `Self` to `u32`, mask / shift out the padding byte, reorder it to put the fields according to comparison priority,
			// and then do a single `u32` comparison.

			let [d, t, w] = m.parts();

			// Construct `[w, zero, d, t]` and then convert it to `t:d:zero:w`. Comparing this integer produces the required sort order.
			//
			// `zero:t:d:w` or `t:d:w:zero` would also work but those arrangements require more instructions to produce.
			let sc = [w, 0, d, t];
			u32::from_le_bytes(sc)
		}

		let sc = sort_criteria(*self);
		let sc_other = sort_criteria(*other);
		sc.cmp(&sc_other)
	}
}

const impl PartialEq for ScorableHandFourthMeld {
	fn eq(&self, other: &Self) -> bool {
		// Micro-optimization: If we do `matches!(self.cmp(other), Ordering::Equal)`, rustc inlines `Ord::cmp` but doesn't elide the rotation,
		// even though that won't affect the equality comparison. So we compare the parts ourselves instead of delegating to `Ord::cmp`.
		self.parts() == other.parts()
	}
}

const impl PartialOrd for ScorableHandFourthMeld {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl ScorableHandPair {
	/// Construct a `ScorableHandPair` using the given tiles.
	///
	/// Returns `Some` if `t1.eq_ignore_red(&t2)`, `None` otherwise.
	pub const fn new(t1: Tile, t2: Tile) -> Option<Self> {
		let t = Tile::pair_representative(t1, t2)?;
		Some(Self(t))
	}

	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		#[expect(clippy::unit_arg)]
		self.try_for_each_tile::<!>(|t| Ok(f(t)));
	}

	fn try_for_each_tile<E>(self, mut f: impl FnMut(Tile) -> Result<(), E>) -> Result<(), E> {
		f(self.0.remove_red())?;
		f(self.0)?;
		Ok(())
	}

	pub(crate) const fn num_yakuhai(self, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		(u8::from(self.0 == round_wind.into()) + u8::from(self.0 == seat_wind.into())) | u8::from(self.0 >= t!(Wh))
	}
}

impl core::fmt::Debug for ScorableHandPair {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandPair {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str("{ ")?;
		self.try_for_each_tile(|t| write!(f, "{t} "))?;
		f.write_str("}")
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
pub(crate) enum PeikouIsshokuJun {
	None,
	Iipeikou,
	Ryanpeikou,
	IsshokuSanjun,
	IsshokuYonjun,
}

impl PeikouIsshokuJun {
	fn new(ds: core::simd::Simd<u8, 4>, ts: core::simd::Simd<u8, 4>, is_menzen: bool) -> Self {
		// The SWAR impl generates smaller code for targets without vectorization.
		let (num_peikou, is_isshoku_yonjun, is_isshoku_sanjun) = cfg_select! {
			use_core_simd => {{
				let consider = core::simd::cmp::SimdPartialOrd::simd_ge(ds, core::simd::Simd::splat(4));
				let count_adjustments = core::simd::Select::select(consider, core::simd::Simd::splat(1), core::simd::Simd::splat(0));
				let offsets = Tile::offsets(ts);

				#[expect(clippy::cast_possible_truncation)]
				let id = core::simd::Simd::from_array(core::array::from_fn(|i| i as u8));

				let counts: core::simd::Simd<u8, 25> =
					(0..4)
					.map(|i| core::simd::Select::select(
						core::simd::cmp::SimdPartialEq::simd_eq(core::simd::Simd::splat(offsets[i]), id),
						core::simd::Simd::splat(count_adjustments[i]),
						core::simd::Simd::splat(0),
					))
					.sum();

				// Micro-optimization: `simd_eq().to_bitmask().count_ones()` generates silly code that widens the mask to `0xFF` as an intermediate step
				// because of how `core::simd::Mask` is designed internally to wrap `iN` instead of `i1`.
				// Doing `reduce_sum(select(simd_eq(), splat(1), splat(0)))` generates the intended code that does popcount on the mask.
				let num_peikou =
					usize::from(core::simd::num::SimdUint::reduce_sum(core::simd::Select::select(
						core::simd::cmp::SimdPartialOrd::simd_ge(counts, core::simd::Simd::splat(2)),
						core::simd::Simd::splat(1_u8),
						core::simd::Simd::splat(0_u8),
					)));

				let is_isshoku_yonjun = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::splat(4)).any();
				let is_isshoku_sanjun = core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::splat(3)).any();

				(num_peikou, is_isshoku_yonjun, is_isshoku_sanjun)
			}},

			_ => {{
				// `[[2, 2, 2, 2, 2, 2, 2, 0, 0]; 3]` packed into two bits per element.
				let mut peikou_counts = 0x2AAA0AAA82AAA_u64;
				let mut num_peikou = 0;

				// `[[3, 3, 3, 3, 3, 3, 3, 0, 0]; 3]` packed into two bits per element.
				let mut isshoku_jun_counts = 0x3FFF0FFFC3FFF_u64;
				let mut is_isshoku_sanjun = false;
				let is_isshoku_yonjun;

				let consider = core::simd::cmp::SimdPartialOrd::simd_ge(ds, core::simd::Simd::splat(4));
				let offsets = Tile::offsets(ts) << 1;
				let count_adjustments = core::simd::Select::select(consider.extract::<0, 3>(), core::simd::Simd::splat(1), core::simd::Simd::splat(0)) << core::simd::num::SimdUint::cast::<u64>(offsets.extract::<0, 3>());

				{
					let count_adjustment = count_adjustments[0];

					peikou_counts -= count_adjustment;

					isshoku_jun_counts -= count_adjustment;
				}

				{
					let consider_m2 = consider.test(1);
					let offset = offsets[1];
					let count_adjustment = count_adjustments[1];

					let peikou_count = peikou_counts.wrapping_shr(offset.into()) & 0b11;
					num_peikou += (u64::from(consider_m2) & peikou_count) as usize;
					peikou_counts -= count_adjustment;

					isshoku_jun_counts -= count_adjustment;
				}

				{
					let consider_m3 = consider.test(2);
					let offset = offsets[2];
					let count_adjustment = count_adjustments[2];

					let peikou_count = peikou_counts.wrapping_shr(offset.into()) & 0b11;
					num_peikou += (u64::from(consider_m3) & peikou_count) as usize;
					if consider_m3 && peikou_count != 0 {
						peikou_counts -= count_adjustment;
					}

					let isshoku_jun_count = isshoku_jun_counts.wrapping_shr(offset.into()) & 0b11;
					is_isshoku_sanjun |= consider_m3 && isshoku_jun_count == 1;
					isshoku_jun_counts -= count_adjustment;
				}

				{
					let consider_m4 = consider.test(3);
					let offset = offsets[3];

					let peikou_count = peikou_counts.wrapping_shr(offset.into()) & 0b11;
					num_peikou += (u64::from(consider_m4) & peikou_count) as usize;

					let isshoku_jun_count = isshoku_jun_counts.wrapping_shr(offset.into()) & 0b11;
					is_isshoku_sanjun |= consider_m4 && isshoku_jun_count == 1;
					is_isshoku_yonjun = consider_m4 && isshoku_jun_count == 0;
				}

				(num_peikou, is_isshoku_yonjun, is_isshoku_sanjun)
			}},
		};

		if is_isshoku_yonjun { Self::IsshokuYonjun }
		else if is_isshoku_sanjun { Self::IsshokuSanjun }
		else if is_menzen && num_peikou == 2 { Self::Ryanpeikou }
		else if is_menzen && num_peikou == 1 { Self::Iipeikou }
		else { Self::None }
	}
}

// [     3     ][        2         ][        1        0         ]
// [other: bool][honors: None | All][terminals: None | Has | All]
//
// None = 0b0
// All = 0b1
// Has = 0b11
//
// ... so that:
//
// None | None = None
// None | Has = Has
// None | All = All
// All | None = All
// All | Has = Has
// All | All = All
// Has | None = Has
// Has | Has = Has
// Has | All = Has
//
// Tested exhaustively in the `chanta_routou` test.
#[derive(Copy)]
#[derive_const(Clone)]
pub(crate) struct ChantaRoutou(u8);

#[expect(clippy::unusual_byte_groupings)]
impl ChantaRoutou {
	const fn has_terminals() -> Self { Self(0b0_0_11) }
	const fn all_terminals() -> Self { Self(0b0_0_01) }
	const fn all_honors() -> Self { Self(0b0_1_00) }
	const fn other() -> Self { Self(0b1_0_00) }

	// All simples
	pub(crate) const fn is_tanyao(self) -> bool { self.0 == 0b1_0_00 }
	// Has terminals and honors
	pub(crate) const fn is_chanta(self) -> bool { self.0 == 0b0_1_11 }
	// All terminals and honors
	pub(crate) const fn is_honroutou(self) -> bool { self.0 == 0b0_1_01 }
	// Has terminals
	pub(crate) const fn is_junchan(self) -> bool { self.0 == 0b0_0_11 }
	// All honors
	pub(crate) const fn is_tsuuiisou(self) -> bool { self.0 == 0b0_1_00 }
	// All terminals
	pub(crate) const fn is_chinroutou(self) -> bool { self.0 == 0b0_0_01 }
	// Other
	#[cfg(test)]
	const fn is_other(self) -> bool { self.0 > 0b1_0_00 }
}

const impl core::ops::BitOr for ChantaRoutou {
	type Output = ChantaRoutou;

	fn bitor(self, rhs: Self) -> Self::Output {
		Self(self.0 | rhs.0)
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
pub enum Iisou {
	None,
	Toipuutao,
	Ryuuiisou,
	Chinryuusou,
	Kouitten,
	Benikujaku,
	Kokuiisou,
}

impl Iisou {
	fn new(ds: core::simd::Simd<u8, 5>, ts: core::simd::Simd<u8, 5>) -> Self {
		fn new_inner(
			masks: core::simd::Simd<u64, 5>,
			is_kan_kou: core::simd::Mask<i8, 5>,
			kan_kou_pair_valid: Tile34Set,
			shun_valid: Tile34Set,
		) -> bool {
			let sets = core::simd::Select::select(is_kan_kou, kan_kou_pair_valid.simd_splat(), shun_valid.simd_splat());
			let is_valid = core::simd::cmp::SimdPartialEq::simd_ne(sets & masks, core::simd::Simd::splat(0));
			is_valid.all()
		}

		let is_kan_kou = core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(3));

		let masks = Tile::masks(Tile::offsets(ts));

		if new_inner(masks, is_kan_kou, Tile34Set::REVERSIBLE, t34set![1p, 2p, 3p, 4s]) {
			Self::Toipuutao
		}
		else if new_inner(masks, is_kan_kou, t34set![2s, 3s, 4s, 6s, 8s], t34set![2s]) {
			Self::Chinryuusou
		}
		else if new_inner(masks, is_kan_kou, t34set![2s, 3s, 4s, 6s, 8s, G], t34set![2s]) {
			// Ryuuiisou requires G, but a hand without G would've already matched as Chinryuusou.
			Self::Ryuuiisou
		}
		else if new_inner(masks, is_kan_kou, t34set![2s, 3s, 4s, 6s, 8s, R], t34set![2s]) {
			// Kouitten requires R, but a hand without R would've already matched as Chinryuusou.
			Self::Kouitten
		}
		else if new_inner(masks, is_kan_kou, t34set![1s, 5s, 7s, 9s, R], Default::default()) {
			Self::Benikujaku
		}
		else if new_inner(masks, is_kan_kou, Tile34Set::BLACK, Default::default()) {
			Self::Kokuiisou
		}
		else {
			Self::None
		}
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(unused)] // Constructed via `transmute`
pub(crate) enum IttsuuKanSen {
	None = 0b000,
	SanshokuTsuukan = 0b001,
	Ittsuu = 0b010,
	TouhokuShinkansen = 0b100,
}

impl IttsuuKanSen {
	fn new(ds: core::simd::Simd<u8, 5>, ts: core::simd::Simd<u8, 5>, is_menzen: bool) -> Self {
		const SANSHOKU_TSUUKAN_MASKS: core::simd::Simd<u32, 6> = core::simd::Simd::from_array([
			0b001000000_000001000_000000001,
			0b000001000_001000000_000000001,
			0b001000000_000000001_000001000,
			0b000000001_001000000_000001000,
			0b000001000_000000001_001000000,
			0b000000001_000001000_001000000,
		]);
		const ITTSUU_MASK: u32 = 0b001001001_u32;
		const TOUHOKU_SHINKANSEN_WINDS: Tile34Set = t34set![E, N];

		let offsets = Tile::offsets(ts);

		let is_shun = core::simd::cmp::SimdPartialOrd::simd_ge(ds.extract::<1, 4>(), core::simd::Simd::splat(4));
		let masks = Tile::masks::<u32, _>(offsets.extract::<1, 4>());
		let counts = core::simd::Select::select(is_shun, masks, core::simd::Simd::splat(0));
		let counts = core::simd::num::SimdUint::reduce_or(counts);
		let counts = core::simd::Simd::splat(counts);
		let is_sanshoku_tsuukan = {
			let counts = counts & SANSHOKU_TSUUKAN_MASKS;
			core::simd::cmp::SimdPartialEq::simd_eq(counts, SANSHOKU_TSUUKAN_MASKS).any()
		};
		if is_sanshoku_tsuukan {
			return Self::SanshokuTsuukan;
		}

		let is_ittsuu = {
			let counts = counts.extract::<0, 3>() >> core::simd::Simd::from_array([0, 9, 18]);
			let counts = counts & core::simd::Simd::splat(ITTSUU_MASK);
			core::simd::cmp::SimdPartialEq::simd_eq(counts, core::simd::Simd::splat(ITTSUU_MASK)).any()
		};

		let result = u8::from(is_ittsuu) << 1;

		let is_touhoku_shinkansen = is_menzen && {
			let is_kan_kou = core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(3));
			let masks = Tile::masks::<u64, _>(offsets);
			let masks = core::simd::Select::select(is_kan_kou, masks, core::simd::Simd::splat(0));
			let mask = core::simd::num::SimdUint::reduce_or(masks);
			mask == TOUHOKU_SHINKANSEN_WINDS.present
		};
		let result = result << u8::from(is_touhoku_shinkansen);

		unsafe { core::mem::transmute::<u8, Self>(result) }
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(unused)] // Constructed via `transmute`
pub(crate) enum NumAnkou {
	None = 0b000,
	Sanankou = 0b001,
	Suuankou = 0b010,
	SuuankouTanki = 0b100,
}

impl NumAnkou {
	fn new(ds: core::simd::Simd<u8, 4>, m4_is_tanki: bool) -> Self {
		let is_ankou_or_ankan = core::simd::cmp::SimdPartialEq::simd_eq(ds & core::simd::Simd::splat(0b101), core::simd::Simd::splat(0));
		let counts = core::simd::Select::select(is_ankou_or_ankan, core::simd::Simd::splat(1_u8), core::simd::Simd::splat(0_u8));
		let count = core::simd::num::SimdUint::reduce_sum(counts);
		let inner = 2 - u8::from(count <= 3) - u8::from(count <= 2);
		let inner = inner << u8::from((count == 4) & m4_is_tanki);
		unsafe { core::mem::transmute::<u8, Self>(inner) }
	}

	pub(crate) const fn num_suuankou(self) -> u8 {
		(self as u8) >> 1
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
pub(crate) enum NumKantsu {
	Neither,
	Sankantsu,
	Suukantsu,
}

impl NumKantsu {
	fn new(ds: core::simd::Simd<u8, 4>) -> Self {
		let is_kantsu = core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(1));
		let counts = core::simd::Select::select(is_kantsu, core::simd::Simd::splat(1_u8), core::simd::Simd::splat(0_u8));
		let count = core::simd::num::SimdUint::reduce_sum(counts);
		match count {
			3 => Self::Sankantsu,
			4 => Self::Suukantsu,
			_ => Self::Neither,
		}
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
pub(crate) enum SuushiiSangen {
	None,
	Shousuushii,
	Daisuushii,
	Shousangen,
	Daisangen,
}

impl SuushiiSangen {
	fn new(ts: core::simd::Simd<u8, 4>, pair: Tile) -> Self {
		let is_ge_ton = core::simd::cmp::SimdPartialOrd::simd_ge(ts, core::simd::Simd::splat(t!(E) as u8));
		let is_le_pei = core::simd::cmp::SimdPartialOrd::simd_le(ts, core::simd::Simd::splat(t!(N) as u8));
		let counts_wind_meld = core::simd::Select::select(is_ge_ton & is_le_pei, core::simd::Simd::splat(1_u8), core::simd::Simd::splat(0_u8));
		let num_wind_melds = core::simd::num::SimdUint::reduce_sum(counts_wind_meld);

		let counts_dragon_meld = core::simd::Select::select(is_le_pei, core::simd::Simd::splat(0_u8), core::simd::Simd::splat(1_u8));
		let num_dragon_melds = core::simd::num::SimdUint::reduce_sum(counts_dragon_meld);

		match (num_wind_melds, num_dragon_melds) {
			(3, _) if ((t!(E) as u8)..=(t!(N) as u8)).contains(&(pair as u8)) => Self::Shousuushii,
			(4, _) => Self::Daisuushii,
			(_, 2) if ((t!(Wh) as u8)..=(t!(R) as u8)).contains(&(pair as u8)) => Self::Shousangen,
			(_, 3) => Self::Daisangen,
			_ => Self::None,
		}
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
pub(crate) enum NumRenkou {
	Neither,
	Sanrenkou,
	Suurenkou,
}

impl NumRenkou {
	fn new(ds: core::simd::Simd<u8, 4>, ts: core::simd::Simd<u8, 4>) -> Self {
		const SUURENKOU_MASK: u64 = 0b1111;
		const SANRENKOU_MASK: u64 = 0b111;

		let is_kan_kou = core::simd::cmp::SimdPartialOrd::simd_le(ds, core::simd::Simd::splat(3));

		let offsets = Tile::offsets(ts);

		let masks = Tile::masks::<u64, _>(offsets);
		let masks = core::simd::Select::select(is_kan_kou, masks, core::simd::Simd::splat(0));
		let counts = core::simd::num::SimdUint::reduce_or(masks);
		let counts = core::simd::Simd::splat(counts);
		let counts = counts & core::simd::Simd::from_array([
			t34set![1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m].present,
			t34set![1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p].present,
			t34set![1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s].present,
		]);

		let offsets = core::simd::num::SimdUint::cast::<u64>(offsets);
		let expected4 = core::simd::Simd::splat(SUURENKOU_MASK) << offsets;
		let expected3 = core::simd::Simd::splat(SANRENKOU_MASK) << offsets;

		let actual_man = core::simd::Simd::splat(counts[0]) & expected4;
		let actual_pin = core::simd::Simd::splat(counts[1]) & expected4;
		let actual_sou = core::simd::Simd::splat(counts[2]) & expected4;

		let is_suurenkou =
			core::simd::cmp::SimdPartialEq::simd_eq(expected4, actual_man) |
			core::simd::cmp::SimdPartialEq::simd_eq(expected4, actual_pin) |
			core::simd::cmp::SimdPartialEq::simd_eq(expected4, actual_sou);
		if is_suurenkou.any() {
			return Self::Suurenkou;
		}

		let is_sanrenkou =
			core::simd::cmp::SimdPartialEq::simd_eq(expected3, actual_man) |
			core::simd::cmp::SimdPartialEq::simd_eq(expected3, actual_pin) |
			core::simd::cmp::SimdPartialEq::simd_eq(expected3, actual_sou);
		if is_sanrenkou.any() {
			return Self::Sanrenkou;
		}

		Self::Neither
	}
}

fn is_akadora_sanshoku<const N: usize>(ts: core::simd::Simd<u8, N>) -> bool {
	core::simd::num::SimdUint::reduce_sum(ts & core::simd::Simd::splat(0b1)) == 3
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(unused)] // Constructed via `transmute`
pub(crate) enum Honchinitsu {
	None = 0b00,
	Honitsu = 0b01,
	Chinitsu = 0b10,
}

impl Honchinitsu {
	fn new<const N: usize>(ts: core::simd::Simd<u8, N>) -> Self {
		//   mask | result
		// =======+================
		//  00000 | None (impossible)
		//  00010 | Chinitsu (man)
		//  00100 | Chinitsu (pin)
		//  00110 | None
		//  01000 | Chinitsu (sou)
		//  01010 | None
		//  01100 | None
		//  01110 | None
		//  10000 | None
		//  10010 | Honitsu (man)
		//  10100 | Honitsu (pin)
		//  10110 | None
		//  11000 | Honitsu (sou)
		//  11010 | None
		//  11100 | None
		//  11110 | None

		const INNERS: u32 = {
			let mut result = 0_u32;
			result |= (Honchinitsu::Chinitsu as u32) << 0b00010;
			result |= (Honchinitsu::Chinitsu as u32) << 0b00100;
			result |= (Honchinitsu::Chinitsu as u32) << 0b01000;
			result |= (Honchinitsu::Honitsu as u32) << 0b10010;
			result |= (Honchinitsu::Honitsu as u32) << 0b10100;
			result |= (Honchinitsu::Honitsu as u32) << 0b11000;
			result
		};

		let suits = Tile::suits4(ts);
		let masks = core::simd::Simd::splat(0b10) << suits;
		let mask = core::simd::num::SimdUint::reduce_or(masks);

		// Micro-optimization: rustc generates `mask & 0b11110` to normalize the shift amount to 5 bits,
		// because it seems to not notice that `mask` is already only five bits. So we assert it ourselves.
		unsafe { core::hint::assert_unchecked(mask <= 0b11110); }
		let result = (INNERS >> mask) & 0b11;
		unsafe { core::mem::transmute::<u8, Self>(result as u8) }
	}
}

#[derive(Copy)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(unused)] // Constructed via `transmute`
pub(crate) enum DairinKokuiisou {
	None = 0b00000,
	Daisuurin = 0b00001,
	Daisharin = 0b00010,
	Daichikurin = 0b00100,
	Daichiishin = 0b01000,
	Kokuiisou = 0b10000,
}

impl DairinKokuiisou {
	fn new(ts: core::simd::Simd<u8, 7>) -> Self {
		let masks = Tile::masks::<u64, _>(Tile::offsets(ts));
		let set = core::simd::num::SimdUint::reduce_or(masks);
		let sets = core::simd::Simd::splat(set);
		let inner = core::simd::cmp::SimdPartialEq::simd_eq(sets, core::simd::Simd::from_array([
			t34set![2m, 3m, 4m, 5m, 6m, 7m, 8m].present,
			t34set![2p, 3p, 4p, 5p, 6p, 7p, 8p].present,
			t34set![2s, 3s, 4s, 5s, 6s, 7s, 8s].present,
			Tile34Set::HONORS.present,
			Tile34Set::BLACK.present,
		])).to_bitmask();
		// SAFETY: `inner` can only have one of the five values of `Self` since `ts` only has seven pairs.
		#[expect(clippy::cast_possible_truncation)]
		unsafe { core::mem::transmute::<u8, Self>(inner as u8) }
	}
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use crate::DragonTile;
	use super::*;

	impl ScorableHand {
		fn is_pinfu(&self, round_wind: WindTile, seat_wind: WindTile) -> bool {
			match self {
				Self::Regular(h) => h.is_pinfu(round_wind, seat_wind),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_iipeikou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.peikou_isshoku_jun(), PeikouIsshokuJun::Iipeikou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_tanyao(&self) -> bool {
			match self {
				Self::Regular(h) => h.chanta_routou().is_tanyao(),
				Self::Chiitoi(h) => h.chanta_routou().is_tanyao(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn num_wind_yakuhai(&self, wind: WindTile, round_wind: WindTile, seat_wind: WindTile) -> u8 {
			match self {
				Self::Regular(h) => {
					let result = h.num_wind_yakuhai(round_wind, seat_wind);
					result[match wind {
						tw!(E) => 0,
						tw!(S) => 1,
						tw!(W) => 2,
						tw!(N) => 3,
					}]
				},
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => 0,
			}
		}

		fn is_dragon_yakuhai(&self, dragon: DragonTile) -> bool {
			match self {
				Self::Regular(h) => {
					let result = h.is_dragon_yakuhai();
					result[match dragon {
						td!(Wh) => 0,
						td!(G) => 1,
						td!(R) => 2,
					}]
				},
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_shiiaru_raotai(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_shiiaru_raotai(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_toipuutao(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.iisou(), Iisou::Toipuutao),
				Self::Chiitoi(h) => h.is_toipuutao(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_chanta(&self) -> bool {
			match self {
				Self::Regular(h) => h.chanta_routou().is_chanta(),
				Self::Chiitoi(h) => h.chanta_routou().is_chanta(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanshoku_doujun(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_sanshoku_doujun(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_ittsuu(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.ittsuukansen(), IttsuuKanSen::Ittsuu),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_toitoi(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_toitoi(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanankou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.num_ankou(), NumAnkou::Sanankou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanshoku_doukou(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_sanshoku_doukou(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sankantsu(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.num_kantsu(), NumKantsu::Sankantsu),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		const fn is_chiitoi(&self) -> bool {
			matches!(self, Self::Chiitoi(_))
		}

		fn is_honroutou(&self) -> bool {
			match self {
				Self::Regular(h) => h.chanta_routou().is_honroutou(),
				Self::Chiitoi(h) => h.chanta_routou().is_honroutou(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_shousangen(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.suushii_sangen(), SuushiiSangen::Shousangen),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanrenkou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.num_renkou(), NumRenkou::Sanrenkou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanshoku_tsuukan(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.ittsuukansen(), IttsuuKanSen::SanshokuTsuukan),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_akadora_sanshoku(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_akadora_sanshoku(),
				Self::Chiitoi(h) => h.is_akadora_sanshoku(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_uumensai(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_uumensai(),
				Self::Chiitoi(h) => h.is_uumensai(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_honitsu(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.honchinitsu(), Honchinitsu::Honitsu),
				Self::Chiitoi(h) => matches!(h.honchinitsu(), Honchinitsu::Honitsu),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_junchan(&self) -> bool {
			match self {
				Self::Regular(h) => h.chanta_routou().is_junchan(),
				Self::Chiitoi(h) => h.chanta_routou().is_junchan(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_ryanpeikou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.peikou_isshoku_jun(), PeikouIsshokuJun::Ryanpeikou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_isshoku_sanjun(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.peikou_isshoku_jun(), PeikouIsshokuJun::IsshokuSanjun),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_chinitsu(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.honchinitsu(), Honchinitsu::Chinitsu),
				Self::Chiitoi(h) => matches!(h.honchinitsu(), Honchinitsu::Chinitsu),
				Self::KokushiMusou(_) => false,
			}
		}

		fn num_kokushi_musou(&self) -> u8 {
			match self {
				Self::Regular(_) |
				Self::Chiitoi(_) => 0,
				Self::KokushiMusou(h) => h.num_kokushi_musou(),
			}
		}

		fn num_suuankou(&self) -> u8 {
			match self {
				Self::Regular(h) => h.num_ankou().num_suuankou(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => 0,
			}
		}

		fn is_daisangen(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.suushii_sangen(), SuushiiSangen::Daisangen),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_shousuushii(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.suushii_sangen(), SuushiiSangen::Shousuushii),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_daisuushii(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.suushii_sangen(), SuushiiSangen::Daisuushii),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_tsuuiisou(&self) -> bool {
			match self {
				Self::Regular(h) => h.chanta_routou().is_tsuuiisou(),
				Self::Chiitoi(h) => h.chanta_routou().is_tsuuiisou(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_chinroutou(&self) -> bool {
			match self {
				Self::Regular(h) => h.chanta_routou().is_chinroutou(),
				Self::Chiitoi(h) => h.chanta_routou().is_chinroutou(),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_ryuuiisou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.iisou(), Iisou::Ryuuiisou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn num_chuuren_poutou(&self) -> u8 {
			match self {
				Self::Regular(h) => h.num_chuuren_poutou(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => 0,
			}
		}

		fn is_suukantsu(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.num_kantsu(), NumKantsu::Suukantsu),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_suurenkou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.num_renkou(), NumRenkou::Suurenkou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_daisharin(&self) -> bool {
			match self {
				Self::Chiitoi(h) => matches!(h.dairin_kokuiisou(), DairinKokuiisou::Daisharin),
				Self::Regular(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_daichikurin(&self) -> bool {
			match self {
				Self::Chiitoi(h) => matches!(h.dairin_kokuiisou(), DairinKokuiisou::Daichikurin),
				Self::Regular(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_daisuurin(&self) -> bool {
			match self {
				Self::Chiitoi(h) => matches!(h.dairin_kokuiisou(), DairinKokuiisou::Daisuurin),
				Self::Regular(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_isshoku_yonjun(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.peikou_isshoku_jun(), PeikouIsshokuJun::IsshokuYonjun),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_hyakuman_goku(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_hyakuman_goku(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_kouitten(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.iisou(), Iisou::Kouitten),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_benikujaku(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.iisou(), Iisou::Benikujaku),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_kokuiisou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.iisou(), Iisou::Kokuiisou),
				Self::Chiitoi(h) => matches!(h.dairin_kokuiisou(), DairinKokuiisou::Kokuiisou),
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_golden_gate_bridge(&self) -> bool {
			match self {
				Self::Regular(h) => h.is_golden_gate_bridge(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_touhoku_shinkansen(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.ittsuukansen(), IttsuuKanSen::TouhokuShinkansen),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_daichiishin(&self) -> bool {
			match self {
				Self::Chiitoi(h) => matches!(h.dairin_kokuiisou(), DairinKokuiisou::Daichiishin),
				Self::Regular(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_chinryuusou(&self) -> bool {
			match self {
				Self::Regular(h) => matches!(h.iisou(), Iisou::Chinryuusou),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}
	}

	#[expect(clippy::unusual_byte_groupings)]
	impl core::fmt::Debug for ChantaRoutou {
		fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
			f.write_str(match self.0 {
				0b0_0_01 => "Chinroutou",
				0b0_0_11 => "Junchan",
				0b0_1_00 => "Tsuuiisou",
				0b0_1_01 => "Honroutou",
				0b0_1_11 => "Chanta",
				0b1_0_00 => "Tanyao",
				0b1_0_01.. => "Other",
				_ => unsafe { core::hint::unreachable_unchecked(); },
			})
		}
	}

	#[test]
	fn num_yakuhai() {
		for &t in Tile::each(crate::GameType::Yonma) {
			let p = ScorableHandPair::new(t, t);
			let p = unsafe { p.unwrap_unchecked() };
			for round_wind in tw![E, S, W, N] {
				for seat_wind in tw![E, S, W, N] {
					let expected = match t {
						t!(
							1m | 2m | 3m | 4m | 5m | 0m | 6m | 7m | 8m | 9m |
							1p | 2p | 3p | 4p | 5p | 0p | 6p | 7p | 8p | 9p |
							1s | 2s | 3s | 4s | 5s | 0s | 6s | 7s | 8s | 9s
						) => 0,
						t!(E) => u8::from(matches!(round_wind, tw!(E))) + u8::from(matches!(seat_wind, tw!(E))),
						t!(S) => u8::from(matches!(round_wind, tw!(S))) + u8::from(matches!(seat_wind, tw!(S))),
						t!(W) => u8::from(matches!(round_wind, tw!(W))) + u8::from(matches!(seat_wind, tw!(W))),
						t!(N) => u8::from(matches!(round_wind, tw!(N))) + u8::from(matches!(seat_wind, tw!(N))),
						t!(Wh | G | R) => 1,
					};
					let actual = p.num_yakuhai(round_wind, seat_wind);
					assert_eq!(actual, expected);
				}
			}
		}
	}

	macro_rules! define_expected_yaku {
		($($field:ident => $method:ident ($($arg:expr),*) $(== $value:expr)? ,)*) => {
			#[derive(Default)]
			struct ExpectedYaku {
				$($field : bool),*
			}

			impl ExpectedYaku {
				#[track_caller]
				fn check(&self, hand: &ScorableHand) {
					$(
						assert_eq!(hand.$method($($arg),*) $(== $value)?, self.$field, stringify!($field));
					)*
					assert!(hand.num_kokushi_musou() <= 2);
					assert!(hand.num_suuankou() <= 2);
					assert!(hand.num_chuuren_poutou() <= 2);
				}
			}
		};
	}

	define_expected_yaku! {
		iipeikou => is_iipeikou(),
		tanyao => is_tanyao(),
		haku => is_dragon_yakuhai(td!(Wh)),
		hatsu => is_dragon_yakuhai(td!(G)),
		chun => is_dragon_yakuhai(td!(R)),
		shiiaru_raotai => is_shiiaru_raotai(),
		toipuutao => is_toipuutao(),
		chanta => is_chanta(),
		sanshoku_doujun => is_sanshoku_doujun(),
		ittsuu => is_ittsuu(),
		toitoi => is_toitoi(),
		sanankou => is_sanankou(),
		sanshoku_doukou => is_sanshoku_doukou(),
		sankantsu => is_sankantsu(),
		chiitoi => is_chiitoi(),
		honroutou => is_honroutou(),
		shousangen => is_shousangen(),
		sanrenkou => is_sanrenkou(),
		sanshoku_tsuukan => is_sanshoku_tsuukan(),
		akadora_sanshoku => is_akadora_sanshoku(),
		uumensai => is_uumensai(),
		honitsu => is_honitsu(),
		junchan => is_junchan(),
		ryanpeikou => is_ryanpeikou(),
		isshoku_sanjun => is_isshoku_sanjun(),
		chinitsu => is_chinitsu(),
		kokushi_musou => num_kokushi_musou() == 1,
		kokushi_musou_juusanmen_machi => num_kokushi_musou() == 2,
		suuankou => num_suuankou() == 1,
		suuankou_tanki => num_suuankou() == 2,
		daisangen => is_daisangen(),
		shousuushii => is_shousuushii(),
		daisuushii => is_daisuushii(),
		tsuuiisou => is_tsuuiisou(),
		chinroutou => is_chinroutou(),
		ryuuiisou => is_ryuuiisou(),
		chuuren_poutou => num_chuuren_poutou() == 1,
		chuuren_poutou_kyuumen_machi => num_chuuren_poutou() == 2,
		suukantsu => is_suukantsu(),
		suurenkou => is_suurenkou(),
		daisharin => is_daisharin(),
		daichikurin => is_daichikurin(),
		daisuurin => is_daisuurin(),
		isshoku_yonjun => is_isshoku_yonjun(),
		hyakuman_goku => is_hyakuman_goku(),
		kouitten => is_kouitten(),
		benikujaku => is_benikujaku(),
		kokuiisou => is_kokuiisou(),
		golden_gate_bridge => is_golden_gate_bridge(),
		touhoku_shinkansen => is_touhoku_shinkansen(),
		daichiishin => is_daichiishin(),
		chinryuusou => is_chinryuusou(),
	}

	macro_rules! test {
		(@inner_new_tile $hand:ident) => {};

		(@inner_new_tile $hand:ident + $new_tile:tt => [ $( $scorable_hand:tt => { $($funcs:tt)* } )* ] $($rest:tt)*) => {
			{
				std::println!("hand: {:?} + {}", $hand, t!($new_tile));
				#[allow(unused_mut)]
				let mut hands: std::collections::BTreeSet<_> = $hand.clone().to_scorable_hands(t!($new_tile), $crate::TsumoOrRon::Tsumo).collect();
				$({
					let hand = hands.pop_first().unwrap();
					assert_eq!(hand, ScorableHand::from(make_scorable_hand! $scorable_hand));
					test!(@inner_func hand $($funcs)*);
				})*
				assert!(hands.is_empty(), "{hands:?}");
			}
			test!(@inner_new_tile $hand $($rest)* );
		};

		(@inner_new_tile $hand:ident + $new_tile:tt ron => [ $( $scorable_hand:tt => { $($funcs:tt)* } )* ] $($rest:tt)*) => {
			{
				std::println!("hand: {:?} + {}", $hand, t!($new_tile));
				#[allow(unused_mut)]
				let mut hands: std::collections::BTreeSet<_> = $hand.clone().to_scorable_hands(t!($new_tile), $crate::TsumoOrRon::Ron).collect();
				$({
					let hand = hands.pop_first().unwrap();
					assert_eq!(hand, ScorableHand::from(make_scorable_hand! $scorable_hand));
					test!(@inner_func hand $($funcs)*);
				})*
				assert!(hands.is_empty(), "{hands:?}");
			}
			test!(@inner_new_tile $hand $($rest)* );
		};

		(@inner_func $hand:ident $($rest:tt)*) => {
			#[allow(unused_mut)]
			let mut expected = ExpectedYaku::default();
			test!(@inner_funcs $hand expected $($rest)*);
			expected.check(&$hand);
		};

		(@inner_funcs $hand:ident $expected:ident) => {};

		(@inner_funcs $hand:ident $expected:ident pinfu $args:tt ; $($rest:tt)*) => {
			assert!($hand.is_pinfu $args, "pinfu");
			test!(@inner_funcs $hand $expected $($rest)*)
		};

		(@inner_funcs $hand:ident $expected:ident !pinfu $args:tt ; $($rest:tt)*) => {
			assert!(!$hand.is_pinfu $args, "!pinfu");
			test!(@inner_funcs $hand $expected $($rest)*)
		};

		(@inner_funcs $hand:ident $expected:ident num_wind_yakuhai $args:tt == $value:expr ; $($rest:tt)*) => {
			assert_eq!($hand.num_wind_yakuhai $args, $value, "num_wind_yakuhai");
			test!(@inner_funcs $hand $expected $($rest)*)
		};

		(@inner_funcs $hand:ident $expected:ident $method:ident (); $($rest:tt)*) => {
			$expected.$method = true;
			test!(@inner_funcs $hand $expected $($rest)*)
		};

		($hand:tt $($new_tile:tt)*) => {{
			let hand = $crate::HandStable::from($crate::make_hand! $hand);
			test!(@inner_new_tile hand $($new_tile)*);
		}};
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn pinfu1() {
		test!((2m 3m 4m 4p 5p 7p 8p 9p 4s 5s 6s 8s 8s)
			+ 3p => [
				({ anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 4s 5s 6s } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }) => {
					pinfu(tw!(E), tw!(E));
				}
			]
			+ 6p => [
				({ anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 4s 5s 6s } { anjun 4p 5p 6p ryanmen_high } { 8s 8s }) => {
					pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	#[test]
	fn pinfu2() {
		test!((1m 2m 3m 2s 3s 4s 7s 8s 5p 6p 7p 9p 9p)
			+ 6s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 6s 7s 8s ryanmen_low } { 9p 9p }) => {
					pinfu(tw!(E), tw!(E));
				}
			]
			+ 9s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 7s 8s 9s ryanmen_high } { 9p 9p }) => {
					pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	//
	// > Counter examples
	// >
	// > Every tile group is a sequence, but this hand is open.
	#[test]
	fn pinfu3() {
		test!((4m 5m 6m 3p 4p 5p 7p 8p 5s 5s { minjun 5s 6s 7s })
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 3p 4p 5p } { minjun 5s 6s 7s } { anjun 6p 7p 8p ryanmen_low } { 5s 5s }) => {
					!pinfu(tw!(E), tw!(E));
					tanyao();
				}
			]
			+ 9p => [
				({ anjun 4m 5m 6m } { anjun 3p 4p 5p } { minjun 5s 6s 7s } { anjun 7p 8p 9p ryanmen_high } { 5s 5s }) => {
					!pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	//
	// > Counter examples
	// >
	// > The pair of east winds invalidates pinfu if won by the dealer or by any player in the east round.
	#[test]
	fn pinfu4() {
		test!((2m 3m 1p 2p 3p 6s 7s 8s 3m 4m 5m E E)
			+ 1m => [
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 1m 2m 3m ryanmen_low } { E E }) => {
					!pinfu(tw!(E), tw!(E));
					!pinfu(tw!(E), tw!(S));
					!pinfu(tw!(E), tw!(W));
					!pinfu(tw!(E), tw!(N));
					!pinfu(tw!(S), tw!(E));
					pinfu(tw!(S), tw!(S));
					pinfu(tw!(S), tw!(W));
					pinfu(tw!(S), tw!(N));
					!pinfu(tw!(W), tw!(E));
					pinfu(tw!(W), tw!(S));
					pinfu(tw!(W), tw!(W));
					pinfu(tw!(W), tw!(N));
					!pinfu(tw!(N), tw!(E));
					pinfu(tw!(N), tw!(S));
					pinfu(tw!(N), tw!(W));
					pinfu(tw!(N), tw!(N));
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m kanchan } { E E }) => {
					!pinfu(tw!(E), tw!(E));
					!pinfu(tw!(E), tw!(S));
					!pinfu(tw!(E), tw!(W));
					!pinfu(tw!(E), tw!(N));
					!pinfu(tw!(S), tw!(E));
					!pinfu(tw!(S), tw!(S));
					!pinfu(tw!(S), tw!(W));
					!pinfu(tw!(S), tw!(N));
					!pinfu(tw!(W), tw!(E));
					!pinfu(tw!(W), tw!(S));
					!pinfu(tw!(W), tw!(W));
					!pinfu(tw!(W), tw!(N));
					!pinfu(tw!(N), tw!(E));
					!pinfu(tw!(N), tw!(S));
					!pinfu(tw!(N), tw!(W));
					!pinfu(tw!(N), tw!(N));
				}
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 2m 3m 4m ryanmen_high } { E E }) => {
					!pinfu(tw!(E), tw!(E));
					!pinfu(tw!(E), tw!(S));
					!pinfu(tw!(E), tw!(W));
					!pinfu(tw!(E), tw!(N));
					!pinfu(tw!(S), tw!(E));
					pinfu(tw!(S), tw!(S));
					pinfu(tw!(S), tw!(W));
					pinfu(tw!(S), tw!(N));
					!pinfu(tw!(W), tw!(E));
					pinfu(tw!(W), tw!(S));
					pinfu(tw!(W), tw!(W));
					pinfu(tw!(W), tw!(N));
					!pinfu(tw!(N), tw!(E));
					pinfu(tw!(N), tw!(S));
					pinfu(tw!(N), tw!(W));
					pinfu(tw!(N), tw!(N));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	//
	// > Counter examples
	// >
	// > The pair wait invalidates pinfu.
	#[test]
	fn pinfu5() {
		test!((1p 2p 3p 4p 5p 6p 7m 8m 9m 5s 6s 7s 3m)
			+ 3m => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7m 8m 9m } { anjun 5s 6s 7s } { 3m 3m }) => {
					!pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	//
	// > Counter examples
	// >
	// > The dragon pair invalidates pinfu.
	#[test]
	fn pinfu6() {
		test!((2m 3m 1p 2p 3p 6s 7s 8s 3m 4m 5m Wh Wh)
			+ 1m => [
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 1m 2m 3m ryanmen_low } { Wh Wh }) => {
					!pinfu(tw!(E), tw!(E));
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m kanchan } { Wh Wh }) => {
					!pinfu(tw!(E), tw!(E));
				}
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 2m 3m 4m ryanmen_high } { Wh Wh }) => {
					!pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	//
	// > Counter examples
	// >
	// > The kanchan wait invalidates pinfu.
	#[test]
	fn pinfu7() {
		test!((1m 2m 3m 2s 3s 4s 7s 9s 2p 2p 5p 6p 7p)
			+ 8s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 7s 8s 9s kanchan } { 2p 2p }) => {
					!pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=29178
	//
	// > Counter examples
	// >
	// > This hand does qualify for pinfu if won by 6-pin or 9-pin.
	// > However, if won by 3-pin, it is considered to have won with a 3-pin tanki (specifically, it has a nobetan wait on 3-6p).
	// > Note that 6-pin could be considered a tanki wait, but still qualifies for pinfu, because the han increase takes precedence over tanki's extra fu.
	#[test]
	fn pinfu8() {
		test!((4m 5m 6m 1s 2s 3s 3p 4p 5p 6p 6p 7p 8p)
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 6p 7p 8p } { 6p 6p }) => {
					!pinfu(tw!(E), tw!(E));
				}
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 6p 7p 8p ryanmen_low } { 6p 6p }) => {
					pinfu(tw!(E), tw!(E));
				}
			]
			+ 9p => [
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 7p 8p 9p ryanmen_high } { 6p 6p }) => {
					pinfu(tw!(E), tw!(E));
					sanshoku_tsuukan();
				}
			]
			+ 3p => [
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 4p 5p 6p } { anjun 6p 7p 8p } { 3p 3p }) => {
					!pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Pinfu
	#[test]
	fn pinfu9() {
		test!((1m 2m 3m 5m 6m 7m 2p 3p 4p 6s 7s 9s 9s)
			+ 5s => [
				({ anjun 1m 2m 3m } { anjun 5m 6m 7m } { anjun 2p 3p 4p } { anjun 5s 6s 7s ryanmen_low } { 9s 9s }) => {
					pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://mahjongsoul.game.yo-star.com/?paipu=260122-eb23da04-3945-40c2-b154-a6f55eb1ed1c_a909728900
	#[test]
	fn iipeikou1() {
		test!((8m 8m 2s 3s 4s 5s 0s 6s 6s 7s 7s E E)
			+ 8m => [
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 0s 6s 7s } { ankou 8m 8m 8m shanpon } { E E }) => {
					iipeikou();
				}
			]
			+ E => [
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 0s 6s 7s } { ankou E E E shanpon } { 8m 8m }) => {
					iipeikou();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Pure Double Sequence
	#[test]
	fn iipeikou2() {
		test!((1m 2m 3m 1m 2m 3m 4p 4p 4p 7p 8p 9p 3s)
			+ 3s => [
				({ anjun 1m 2m 3m } { anjun 1m 2m 3m } { ankou 4p 4p 4p } { anjun 7p 8p 9p } { 3s 3s }) => {
					iipeikou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn tanyao1() {
		test!((3m 3m 3m 4m 4m 2p 2p 2p 5p 6p 7p 8p 8p)
			+ 8p => [
				({ ankou 3m 3m 3m } { ankou 2p 2p 2p } { anjun 5p 6p 7p } { ankou 8p 8p 8p shanpon } { 4m 4m }) => {
					tanyao();
					sanankou();
				}
			]
			+ 4m => [
				({ ankou 3m 3m 3m } { ankou 2p 2p 2p } { anjun 5p 6p 7p } { ankou 4m 4m 4m shanpon } { 8p 8p }) => {
					tanyao();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tanyao&oldid=29058
	#[test]
	fn tanyao2() {
		test!((2s 2s 2s 6s 7s 8s 4m 5m 6m 3p 3p 5p 5p)
			+ 3p => [
				({ ankou 2s 2s 2s } { anjun 6s 7s 8s } { anjun 4m 5m 6m } { ankou 3p 3p 3p shanpon } { 5p 5p }) => {
					tanyao();
				}
			]
			+ 5p => [
				({ ankou 2s 2s 2s } { anjun 6s 7s 8s } { anjun 4m 5m 6m } { ankou 5p 5p 5p shanpon } { 3p 3p }) => {
					tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tanyao&oldid=29058
	#[test]
	fn tanyao3() {
		test!((6m 7m 8m 4s 5s 3p 3p 3p 6p 6p { minkou 2m 2m 2m })
			+ 3s => [
				({ anjun 6m 7m 8m } { ankou 3p 3p 3p } { minkou 2m 2m 2m } { anjun 3s 4s 5s ryanmen_low } { 6p 6p }) => {
					tanyao();
				}
			]
			+ 6s => [
				({ anjun 6m 7m 8m } { ankou 3p 3p 3p } { minkou 2m 2m 2m } { anjun 4s 5s 6s ryanmen_high } { 6p 6p }) => {
					tanyao();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Tanyao
	#[test]
	fn tanyao4() {
		test!((8s { minjun 2m 3m 4m } { minjun 5m 6m 7m } { minkou 3p 3p 3p } { minjun 4s 5s 6s })
			+ 8s => [
				({ minjun 2m 3m 4m } { minjun 5m 6m 7m } { minkou 3p 3p 3p } { minjun 4s 5s 6s } { 8s 8s }) => {
					tanyao();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn yakuhai1() {
		test!((1p 2p 3p 5s 5s G G { minkou 9p 9p 9p } { minkou E E E })
			+ 5s => [
				({ anjun 1p 2p 3p } { minkou 9p 9p 9p } { minkou E E E } { ankou 5s 5s 5s shanpon } { G G }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 2;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
				}
			]
			+ G => [
				({ anjun 1p 2p 3p } { minkou 9p 9p 9p } { minkou E E E } { ankou G G G shanpon } { 5s 5s }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 2;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
					hatsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Yakuhai&oldid=29138
	#[test]
	fn yakuhai2() {
		test!((G G 3p 4p 5p 9m 9m { minjun 1m 2m 3m } { minkou 6s 6s 6s })
			+ G => [
				({ anjun 3p 4p 5p } { minjun 1m 2m 3m } { minkou 6s 6s 6s } { ankou G G G shanpon } { 9m 9m }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
					hatsu();
				}
			]
			+ 9m => [
				({ anjun 3p 4p 5p } { minjun 1m 2m 3m } { minkou 6s 6s 6s } { ankou 9m 9m 9m shanpon } { G G }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Seat Wind
	#[test]
	fn yakuhai3() {
		test!((3m 3m 3m 4p 5p 6p 7s 8s 9s 1s { minkou W W W })
			+ 1s => [
				({ ankou 3m 3m 3m } { anjun 4p 5p 6p } { anjun 7s 8s 9s } { minkou W W W } { 1s 1s }) => {
					num_wind_yakuhai(tw!(W), tw!(E), tw!(W)) == 1;
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Prevalent Wind
	#[test]
	fn yakuhai4() {
		test!((3m 3m 3m 4p 5p 6p 7s 8s 9s 1s { minkou E E E })
			+ 1s => [
				({ ankou 3m 3m 3m } { anjun 4p 5p 6p } { anjun 7s 8s 9s } { minkou E E E } { 1s 1s }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(W)) == 1;
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Dragons
	#[test]
	fn yakuhai5() {
		test!((3m 3m 3m 4p 5p 6p 7s 8s 9s 1s { minkou Wh Wh Wh })
			+ 1s => [
				({ ankou 3m 3m 3m } { anjun 4p 5p 6p } { anjun 7s 8s 9s } { minkou Wh Wh Wh } { 1s 1s }) => {
					haku();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn shiiaru_raotai1() {
		test!((G { minkou 9s 9s 9s } { minkou 2p 2p 2p } { minjun 4p 0p 6p } { minjun 1p 2p 3p })
			+ G => [
				({ minkou 9s 9s 9s } { minkou 2p 2p 2p } { minjun 4p 0p 6p } { minjun 1p 2p 3p } { G G }) => {
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Shiiaruraotai
	#[test]
	fn shiiaru_raotai2() {
		test!((8s { minjun 2m 3m 4m } { minjun 5m 6m 7m } { minkou 3p 3p 3p } { minjun 4s 5s 6s })
			+ 8s => [
				({ minjun 2m 3m 4m } { minjun 5m 6m 7m } { minkou 3p 3p 3p } { minjun 4s 5s 6s } { 8s 8s }) => {
					shiiaru_raotai();
					tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn toipuutao() {
		test!((1p 2p 3p 3p 4p 5p 8s 8s 8s Wh { minjun 6s 4s 5s })
			+ Wh => [
				({ anjun 1p 2p 3p } { anjun 3p 4p 5p } { minjun 4s 5s 6s } { ankou 8s 8s 8s } { Wh Wh }) => {
					toipuutao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn chanta1() {
		test!((1m 1m 7p 8p 9p 1s 2s 3s S S { minjun 2p 1p 3p })
			+ 1m => [
				({ anjun 7p 8p 9p } { anjun 1s 2s 3s } { minjun 2p 1p 3p } { ankou 1m 1m 1m shanpon } { S S }) => {
					chanta();
				}
			]
			+ S => [
				({ anjun 7p 8p 9p } { anjun 1s 2s 3s } { minjun 2p 1p 3p } { ankou S S S shanpon } { 1m 1m }) => {
					chanta();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chanta&oldid=30930
	#[test]
	fn chanta2() {
		test!((1p 2p 3p 9s 9s 9s N N 2m 3m 7m 8m 9m)
			+ 1m => [
				({ anjun 1p 2p 3p } { ankou 9s 9s 9s } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_low } { N N }) => {
					chanta();
				}
			]
			+ 4m => [
				({ anjun 1p 2p 3p } { ankou 9s 9s 9s } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_high } { N N }) => {
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Half Outside Hand
	#[test]
	fn chanta3() {
		test!((G { minjun 1m 2m 3m } { minjun 7m 8m 9m } { minjun 1p 2p 3p } { minkou E E E })
			+ G => [
				({ minjun 1m 2m 3m } { minjun 7m 8m 9m } { minjun 1p 2p 3p } { minkou E E E } { G G }) => {
					chanta();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=29035
	#[test]
	fn sanshoku_doujun1() {
		test!((1m 2m 3m 1p 2p 3p 1s 2s 3s 6s 7s 8s E)
			+ E => [
				({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s } { E E }) => {
					sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=29035
	#[test]
	fn sanshoku_doujun2() {
		test!((1m 2m 3m 1p 2p 3p 1s 2s 3s E { minjun 6s 7s 8s })
			+ E => [
				({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s } { E E }) => {
					sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=29035
	#[test]
	fn sanshoku_doujun3() {
		test!((1p 2p 3p 6s 7s E E { minjun 1m 2m 3m } { minjun 3s 1s 2s})
			+ 8s => [
				({ anjun 1p 2p 3p } { minjun 1m 2m 3m } { minjun 3s 1s 2s } { anjun 6s 7s 8s ryanmen_high } { E E }) => {
					sanshoku_doujun();
				}
			]
			+ 5s => [
				({ anjun 1p 2p 3p } { minjun 1m 2m 3m } { minjun 3s 1s 2s } { anjun 5s 6s 7s ryanmen_low } { E E }) => {
					sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=29035
	#[test]
	fn sanshoku_doujun4() {
		test!((4m 5m 6m 4s 5s 6s 4p 5p S S S G G)
			+ 3p => [
				({ anjun 4m 5m 6m } { anjun 4s 5s 6s } { ankou S S S } { anjun 3p 4p 5p ryanmen_low } { G G }) => {
					uumensai();
				}
			]
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 4s 5s 6s } { ankou S S S } { anjun 4p 5p 6p ryanmen_high } { G G }) => {
					sanshoku_doujun();
					uumensai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Mixed Triple Sequence
	#[test]
	fn sanshoku_doujun5() {
		test!((W { minjun 1m 2m 3m } { minjun 1p 2p 3p } { minjun 1s 2s 3s } { minkou 6s 6s 6s })
			+ W => [
				({ minjun 1m 2m 3m } { minjun 1p 2p 3p } { minjun 1s 2s 3s } { minkou 6s 6s 6s } { W W }) => {
					sanshoku_doujun();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ikki_tsuukan&oldid=29042
	#[test]
	fn ittsuu1() {
		test!((1m 2m 3m 4m 0m 6m 7m 8m 9m 3p 4p 5s 5s)
			+ 2p => [
				({ anjun 1m 2m 3m } { anjun 4m 0m 6m } { anjun 7m 8m 9m } { anjun 2p 3p 4p ryanmen_low } { 5s 5s }) => {
					ittsuu();
				}
			]
			+ 5p => [
				({ anjun 1m 2m 3m } { anjun 4m 0m 6m } { anjun 7m 8m 9m } { anjun 3p 4p 5p ryanmen_high } { 5s 5s }) => {
					ittsuu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ikki_tsuukan&oldid=29042
	#[test]
	fn ittsuu2() {
		test!((2m 2m 2m 4s 6s Wh Wh { minjun 1s 2s 3s } { minjun 8s 7s 9s })
			+ 5s => [
				({ ankou 2m 2m 2m } { minjun 1s 2s 3s } { minjun 7s 8s 9s } { anjun 4s 5s 6s kanchan } { Wh Wh }) => {
					ittsuu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ikki_tsuukan&oldid=29042
	#[test]
	fn ittsuu3() {
		test!((1m 2m 3m 4m 4m 5p 6p { minjun 5m 6m 7m } { minjun 7m 8m 9m })
			+ 4p => [
				({ anjun 1m 2m 3m } { minjun 5m 6m 7m } { minjun 7m 8m 9m } { anjun 4p 5p 6p ryanmen_low } { 4m 4m }) => {
				}
			]
			+ 7p => [
				({ anjun 1m 2m 3m } { minjun 5m 6m 7m } { minjun 7m 8m 9m } { anjun 5p 6p 7p ryanmen_high } { 4m 4m }) => {
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Pure Straight
	#[test]
	fn ittsuu4() {
		test!((1m 2m 3m 4m 5m 6m 7m 8m 9m E { minkou 1p 1p 1p })
			+ E => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { minkou 1p 1p 1p } { E E }) => {
					ittsuu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn toitoi1() {
		test!((1m 1m 1m 7p 7p 4s 4s S S S { minkou 8p 8p 8p })
			+ 7p => [
				({ ankou 1m 1m 1m } { ankou S S S } { minkou 8p 8p 8p } { ankou 7p 7p 7p shanpon } { 4s 4s }) => {
					toitoi();
					sanankou();
				}
			]
			+ 4s => [
				({ ankou 1m 1m 1m } { ankou S S S } { minkou 8p 8p 8p } { ankou 4s 4s 4s shanpon } { 7p 7p }) => {
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=29053
	#[test]
	fn toitoi2() {
		test!((1p 1p 1p 4p 4p 4p 8s 8s R R { minkou W W W })
			+ 8s => [
				({ ankou 1p 1p 1p } { ankou 4p 4p 4p } { minkou W W W } { ankou 8s 8s 8s shanpon } { R R }) => {
					toitoi();
					sanankou();
				}
			]
			+ R => [
				({ ankou 1p 1p 1p } { ankou 4p 4p 4p } { minkou W W W } { ankou R R R shanpon } { 8s 8s }) => {
					toitoi();
					chun();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=29053
	#[test]
	fn toitoi3() {
		test!((2m 2m 2m 9p 9p Wh Wh { ankan 4p 4p 4p 4p } { minkou W W W })
			+ 9p => [
				({ ankou 2m 2m 2m } { ankan 4p 4p 4p 4p } { minkou W W W } { ankou 9p 9p 9p shanpon } { Wh Wh }) => {
					toitoi();
					sanankou();
				}
			]
			+ Wh => [
				({ ankou 2m 2m 2m } { ankan 4p 4p 4p 4p } { minkou W W W } { ankou Wh Wh Wh shanpon } { 9p 9p }) => {
					toitoi();
					haku();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=29053
	#[test]
	fn toitoi4() {
		test!((N N N 3p 3p 3p 6s 6s 6s 7m 7m G G)
			+ 7m => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { ankou 7m 7m 7m shanpon } { G G }) => {
					toitoi();
					uumensai();
					suuankou();
				}
			]
			+ 7m ron => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { minkou 7m 7m 7m shanpon } { G G }) => {
					toitoi();
					sanankou();
					uumensai();
				}
			]
			+ G => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { ankou G G G shanpon } { 7m 7m }) => {
					toitoi();
					hatsu();
					uumensai();
					suuankou();
				}
			]
			+ G ron => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { minkou G G G shanpon } { 7m 7m }) => {
					toitoi();
					hatsu();
					sanankou();
					uumensai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> All Triplets
	#[test]
	fn toitoi5() {
		test!((S { minkou 3m 3m 3m } { minkou 4p 4p 4p } { minkou 3s 3s 3s } { minkou E E E })
			+ S => [
				({ minkou 3m 3m 3m } { minkou 4p 4p 4p } { minkou 3s 3s 3s } { minkou E E E } { S S }) => {
					toitoi();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn sanankou1() {
		test!((6m 6m 6m 2p 3p 8p 8p 4s 4s 4s N N N)
			+ 1p => [
				({ ankou 6m 6m 6m } { ankou 4s 4s 4s } { ankou N N N } { anjun 1p 2p 3p ryanmen_low } { 8p 8p }) => {
					sanankou();
				}
			]
			+ 4p => [
				({ ankou 6m 6m 6m } { ankou 4s 4s 4s } { ankou N N N } { anjun 2p 3p 4p ryanmen_high } { 8p 8p }) => {
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=29131
	//
	// > Case where the yaku is guaranteed
	#[test]
	fn sanankou2() {
		test!((1p 1p 1p 3p 3p 3p 5p 5p 5p 6s { minjun 1s 2s 3s })
			+ 6s => [
				({ ankou 1p 1p 1p } { ankou 3p 3p 3p } { ankou 5p 5p 5p } { minjun 1s 2s 3s } { 6s 6s }) => {
					sanankou();
				}
			]
			+ 6s ron => [
				({ ankou 1p 1p 1p } { ankou 3p 3p 3p } { ankou 5p 5p 5p } { minjun 1s 2s 3s } { 6s 6s ron }) => {
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=29131
	//
	// > Case where the hand must be won by tsumo
	#[test]
	fn sanankou3() {
		test!((1m 2m 3m 1p 1p 1p 3p 3p 6p 6p 6s 6s 6s)
			+ 3p => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { ankou 3p 3p 3p shanpon } { 6p 6p }) => {
					sanankou();
				}
			]
			+ 3p ron => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { minkou 3p 3p 3p shanpon } { 6p 6p }) => {
				}
			]
			+ 6p => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { ankou 6p 6p 6p shanpon } { 3p 3p }) => {
					sanankou();
				}
			]
			+ 6p ron => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { minkou 6p 6p 6p shanpon } { 3p 3p }) => {
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=29131
	//
	// > Case where the hand must be won by tsumo
	#[test]
	fn sanankou4() {
		test!((4m 4m 4m 6m 6m 6m 7p 7p 9s 9s { minjun 1p 2p 3p })
			+ 7p => [
				({ ankou 4m 4m 4m } { ankou 6m 6m 6m } { minjun 1p 2p 3p } { ankou 7p 7p 7p shanpon } { 9s 9s }) => {
					sanankou();
				}
			]
			+ 7p ron => [
				({ ankou 4m 4m 4m } { ankou 6m 6m 6m } { minjun 1p 2p 3p } { minkou 7p 7p 7p shanpon } { 9s 9s }) => {
				}
			]
			+ 9s => [
				({ ankou 4m 4m 4m } { ankou 6m 6m 6m } { minjun 1p 2p 3p } { ankou 9s 9s 9s shanpon } { 7p 7p }) => {
					sanankou();
				}
			]
			+ 9s ron => [
				({ ankou 4m 4m 4m } { ankou 6m 6m 6m } { minjun 1p 2p 3p } { minkou 9s 9s 9s shanpon } { 7p 7p }) => {
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=29131
	//
	// > Case where the hand is won by discard.
	// > Note: A tsumo results in the suuankou yakuman.
	#[test]
	fn sanankou5() {
		test!((7m 7m 7m 8p 8p 8p 3s 3s E E R R R)
			+ 3s => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { ankou 3s 3s 3s shanpon } { E E }) => {
					chun();
					toitoi();
					uumensai();
					suuankou();
				}
			]
			+ 3s ron => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { minkou 3s 3s 3s shanpon } { E E }) => {
					sanankou();
					chun();
					toitoi();
					uumensai();
				}
			]
			+ E => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { ankou E E E shanpon } { 3s 3s }) => {
					chun();
					toitoi();
					uumensai();
					suuankou();
				}
			]
			+ E ron => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { minkou E E E shanpon } { 3s 3s }) => {
					sanankou();
					chun();
					toitoi();
					uumensai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Three Concealed Triplets
	#[test]
	fn sanankou6() {
		test!((1m 1m 1m 1p 1p 1p 1s 1s 1s E { minjun 3s 4s 5s })
			+ E => [
				({ ankou 1m 1m 1m } { ankou 1p 1p 1p } { ankou 1s 1s 1s } { minjun 3s 4s 5s } { E E }) => {
					sanankou();
					sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn sanshoku_doukou1() {
		test!((4m 5m 6m 7m 7m 7m 5s { minkou 7s 7s 7s } { minkou 7p 7p 7p })
			+ 5s => [
				({ anjun 4m 5m 6m } { ankou 7m 7m 7m } { minkou 7s 7s 7s } { minkou 7p 7p 7p } { 5s 5s }) => {
					sanshoku_doukou();
					tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=30756
	#[test]
	fn sanshoku_doukou2() {
		test!((3m 3m 3m 3s 3s 3s 6s 7s W W { minkou 3p 3p 3p })
			+ 5s => [
				({ ankou 3m 3m 3m } { ankou 3s 3s 3s } { minkou 3p 3p 3p } { anjun 5s 6s 7s ryanmen_low } { W W }) => {
					sanshoku_doukou();
				}
			]
			+ 8s => [
				({ ankou 3m 3m 3m } { ankou 3s 3s 3s } { minkou 3p 3p 3p } { anjun 6s 7s 8s ryanmen_high } { W W }) => {
					sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=30756
	#[test]
	fn sanshoku_doukou3() {
		test!((3m 3m 3m 3s 3s 4s 5s 6s 6s 6s { minkou 3p 3p 3p })
			+ 3s => [
				({ ankou 3m 3m 3m } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { 3s 3s }) => {
					tanyao();
				}
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 3s 4s 5s ryanmen_low } { 3s 3s }) => {
					tanyao();
				}
				({ ankou 3m 3m 3m } { anjun 4s 5s 6s } { minkou 3p 3p 3p } { ankou 3s 3s 3s shanpon } { 6s 6s }) => {
					sanshoku_doukou();
					tanyao();
				}
			]
			+ 6s => [
				({ ankou 3m 3m 3m } { anjun 4s 5s 6s } { minkou 3p 3p 3p } { ankou 6s 6s 6s shanpon } { 3s 3s }) => {
					tanyao();
				}
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 4s 5s 6s ryanmen_high } { 3s 3s }) => {
					tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=30756
	#[test]
	fn sanshoku_doukou4() {
		test!((3m 3m 3m 3s 3s 6s 7s 8s W W { minkou 3p 3p 3p })
			+ 3s => [
				({ ankou 3m 3m 3m } { anjun 6s 7s 8s } { minkou 3p 3p 3p } { ankou 3s 3s 3s shanpon } { W W }) => {
					sanshoku_doukou();
				}
			]
			+ W => [
				({ ankou 3m 3m 3m } { anjun 6s 7s 8s } { minkou 3p 3p 3p } { ankou W W W shanpon } { 3s 3s }) => {
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Triple Triplets
	#[test]
	fn sanshoku_doukou5() {
		test!((R { minkou 3m 3m 3m } { minkou 3p 3p 3p } { minkou 3s 3s 3s } { minjun 5s 6s 7s })
			+ R => [
				({ minkou 3m 3m 3m } { minkou 3p 3p 3p } { minkou 3s 3s 3s } { minjun 5s 6s 7s } { R R }) => {
					sanshoku_doukou();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn sankantsu1() {
		test!((4m 5m 6m 2s { minkan 6p 6p 6p 6p } { minkan 9s 9s 9s 9s } { ankan 5s 5s 5s 5s })
			+ 2s => [
				({ anjun 4m 5m 6m } { minkan 6p 6p 6p 6p } { minkan 9s 9s 9s 9s } { ankan 5s 5s 5s 5s } { 2s 2s }) => {
					sankantsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sankantsu&oldid=29604
	#[test]
	fn sankantsu2() {
		test!((3p 4p 5p E { minkan 4m 4m 4m 4m } { ankan 8s 8s 8s 8s } { minkan 2p 2p 2p 2p })
			+ E => [
				({ anjun 3p 4p 5p } { minkan 4m 4m 4m 4m } { ankan 8s 8s 8s 8s } { minkan 2p 2p 2p 2p } { E E }) => {
					sankantsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Triple Quads
	#[test]
	fn sankantsu3() {
		test!((R { minjun 5s 6s 7s } { minkan 3m 3m 3m 3m } { minkan 3p 3p 3p 3p } { minkan 3s 3s 3s 3s })
			+ R => [
				({ minjun 5s 6s 7s } { minkan 3m 3m 3m 3m } { minkan 3p 3p 3p 3p } { minkan 3s 3s 3s 3s } { R R }) => {
					sankantsu();
					shiiaru_raotai();
					sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn chiitoi1() {
		test!((1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh)
			+ S => [
				({ 1p 1p } { 7p 7p } { W W } { 5m 5m } { 4s 4s } { Wh Wh } { S S }) => {
					chiitoi();
					uumensai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiitoitsu&oldid=29016
	#[test]
	fn chiitoi2() {
		test!((1m 1m 3m 3m 4m 5p 5p 2s 2s W W Wh Wh)
			+ 4m => [
				({ 1m 1m } { 3m 3m } { 5p 5p } { 2s 2s } { W W } { Wh Wh } { 4m 4m }) => {
					chiitoi();
					uumensai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Seven Pairs
	#[test]
	fn chiitoi3() {
		test!((1m 1m 2m 2m 3p 3p 4p 4p 6p 6p 7s 7s N)
			+ N => [
				({ 1m 1m } { 2m 2m } { 3p 3p } { 4p 4p } { 6p 6p } { 7s 7s } { N N }) => {
					chiitoi();
				}
			]
		);
	}

	// 0m wait redness is preserved.
	#[test]
	fn chiitoi4() {
		test!((0m 6m 6m 1p 1p 2p 2p 3s 3s 4s 4s N N)
			+ 5m => [
				({ 6m 6m } { 1p 1p } { 2p 2p } { 3s 3s } { 4s 4s } { N N } { 5m 0m }) => {
					chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn honroutou1() {
		test!((1m 1m 1m 9m 9m S S { minkou 9s 9s 9s } { minkou N N N })
			+ 9m => [
				({ ankou 1m 1m 1m } { minkou 9s 9s 9s } { minkou N N N } { ankou 9m 9m 9m shanpon } { S S }) => {
					honroutou();
					toitoi();
				}
			]
			+ S => [
				({ ankou 1m 1m 1m } { minkou 9s 9s 9s } { minkou N N N } { ankou S S S shanpon } { 9m 9m }) => {
					honroutou();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=29046
	#[test]
	fn honroutou2() {
		test!((1p 1p 1p 9s 9s 9s E E 1m 1m { minkou S S S })
			+ E => [
				({ ankou 1p 1p 1p } { ankou 9s 9s 9s } { minkou S S S } { ankou E E E shanpon } { 1m 1m }) => {
					honroutou();
					toitoi();
					sanankou();
				}
			]
			+ 1m => [
				({ ankou 1p 1p 1p } { ankou 9s 9s 9s } { minkou S S S } { ankou 1m 1m 1m shanpon } { E E }) => {
					honroutou();
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=29046
	#[test]
	fn honroutou3() {
		test!((1p 1p 9s 9s { minkou 9m 9m 9m } { minkou N N N } { minkou W W W })
			+ 1p => [
				({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { ankou 1p 1p 1p shanpon } { 9s 9s }) => {
					honroutou();
					toitoi();
				}
			]
			+ 9s => [
				({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { ankou 9s 9s 9s shanpon } { 1p 1p }) => {
					honroutou();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=29046
	#[test]
	fn honroutou4() {
		test!((9m 9m 1p 1p 1s 1s 9s 9s S S W W N)
			+ N => [
				({ 9m 9m } { 1p 1p } { 1s 1s } { 9s 9s } { S S } { W W } { N N }) => {
					honroutou();
					chiitoi();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> All Terminals and Honors
	#[test]
	fn honroutou5() {
		test!((E { minkou 1m 1m 1m } { minkou 9m 9m 9m } { minkou 1p 1p 1p } { minkou 1s 1s 1s })
			+ E => [
				({ minkou 1m 1m 1m } { minkou 9m 9m 9m } { minkou 1p 1p 1p } { minkou 1s 1s 1s } { E E }) => {
					honroutou();
					shiiaru_raotai();
					toitoi();
					sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn shousangen1() {
		test!((6s 7s 8s Wh Wh Wh G G R R { minjun 2m 3m 4m })
			+ G => [
				({ anjun 6s 7s 8s } { ankou Wh Wh Wh } { minjun 2m 3m 4m } { ankou G G G shanpon } { R R }) => {
					shousangen();
					haku();
					hatsu();
				}
			]
			+ R => [
				({ anjun 6s 7s 8s } { ankou Wh Wh Wh } { minjun 2m 3m 4m } { ankou R R R shanpon } { G G }) => {
					shousangen();
					haku();
					chun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=29049
	#[test]
	fn shousangen2() {
		test!((2m 3m 3p 4p 0p R R G G G { minkou Wh Wh Wh })
			+ 1m => [
				({ anjun 3p 4p 0p } { ankou G G G } { minkou Wh Wh Wh } { anjun 1m 2m 3m ryanmen_low } { R R }) => {
					shousangen();
					haku();
					hatsu();
				}
			]
			+ 4m => [
				({ anjun 3p 4p 0p } { ankou G G G } { minkou Wh Wh Wh } { anjun 2m 3m 4m ryanmen_high } { R R }) => {
					shousangen();
					haku();
					hatsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=29049
	#[test]
	fn shousangen3() {
		test!((6m 7m 8m 4s 4s Wh Wh R R R { minkou G G G })
			+ 4s => [
				({ anjun 6m 7m 8m } { ankou R R R } { minkou G G G } { ankou 4s 4s 4s shanpon } { Wh Wh }) => {
					shousangen();
					hatsu();
					chun();
				}
			]
			+ Wh => [
				({ anjun 6m 7m 8m } { ankou R R R } { minkou G G G } { ankou Wh Wh Wh shanpon } { 4s 4s }) => {
					daisangen();
					haku();
					hatsu();
					chun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=29049
	#[test]
	fn shousangen4() {
		test!((2p 3p 4p 3s 4s G G { minkou Wh Wh Wh } { minkou R R R })
			+ 5s ron => [
				({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_high } { G G }) => {
					shousangen();
					haku();
					chun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=29049
	#[test]
	fn shousangen5() {
		test!((5m 6m 7m 1s 2s 3s G G R R { minkou Wh Wh Wh })
			+ G ron => [
				({ anjun 5m 6m 7m } { anjun 1s 2s 3s } { minkou Wh Wh Wh }{ minkou G G G shanpon } { R R }) => {
					shousangen();
					haku();
					hatsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Little Three Dragons
	#[test]
	fn shousangen6() {
		test!((2m 3m 4m 5p 6p 7p R { minkou Wh Wh Wh } { minkou G G G })
			+ R => [
				({ anjun 2m 3m 4m } { anjun 5p 6p 7p } { minkou Wh Wh Wh } { minkou G G G } { R R }) => {
					shousangen();
					haku();
					hatsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn sanrenkou1() {
		test!((3p 3p 3p 4p 4p 4p 0p 5p 6s 6s { minkou R R R })
			+ 5p => [
				({ ankou 3p 3p 3p } { ankou 4p 4p 4p } { minkou R R R } { ankou 0p 5p 5p shanpon } { 6s 6s }) => {
					sanrenkou();
					chun();
					toitoi();
					sanankou();
				}
				{{ anjun 3p 4p 5p } { anjun 3p 4p 0p } { minkou R R R } { anjun 3p 4p 5p ryanmen_high } { 6s 6s }} => {
					chun();
					isshoku_sanjun();
				}
			]
		);
	}

	// Consecutive kous do not cross suits.
	#[test]
	fn sanrenkou2() {
		test!((8m 8m 8m 9m 9m 9m 1p 1p G G { minkou R R R })
			+ 1p => [
				({ ankou 8m 8m 8m } { ankou 9m 9m 9m } { minkou R R R } { ankou 1p 1p 1p shanpon } { G G }) => {
					chun();
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Three Chained Triplets
	#[test]
	fn sanrenkou3() {
		test!((8p { minkou 1m 1m 1m } { minkou 2m 2m 2m } { minkou 3m 3m 3m } { minjun 5s 6s 7s })
			+ 8p => [
				({ minkou 1m 1m 1m } { minkou 2m 2m 2m } { minkou 3m 3m 3m } { minjun 5s 6s 7s } { 8p 8p }) => {
					sanrenkou();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn sanshoku_tsuukan1() {
		test!((5m 6m 7m 7m 8m 1p 2p 3p 4p 4p 4s 5s 6s)
			+ 9m => [
				({ anjun 5m 6m 7m } { anjun 1p 2p 3p } { anjun 4s 5s 6s } { anjun 7m 8m 9m ryanmen_high } { 4p 4p }) => {
					sanshoku_tsuukan();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn sanshoku_tsuukan2() {
		test!((4m 5m 6m 1p 2p 3p 1s 7s 8s 9s S S S)
			+ 1s => [
				({ anjun 4m 5m 6m } { anjun 1p 2p 3p } { anjun 7s 8s 9s } { ankou S S S } { 1s 1s }) => {
					sanshoku_tsuukan();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn akadora_sanshoku() {
		test!((3m 4m 0m 0s 5s W W { minkou 7s 7s 7s } { minjun 0p 4p 6p })
			+ W => [
				({ anjun 3m 4m 0m } { minjun 4p 0p 6p } { minkou 7s 7s 7s } { ankou W W W shanpon } { 5s 0s }) => {
					akadora_sanshoku();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn uumensai1() {
		test!((9s 9s G G { minkou N N N } { minkou 2m 2m 2m } { minjun 6p 4p 5p })
			+ 9s => [
				({ minkou N N N } { minkou 2m 2m 2m } { minjun 4p 5p 6p } { ankou 9s 9s 9s shanpon } { G G }) => {
					uumensai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Uumensai
	#[test]
	fn uumensai2() {
		test!((S { minjun 1m 2m 3m } { minjun 2p 3p 4p } { minkou 5s 5s 5s } { minkou G G G })
			+ S => [
				({ minjun 1m 2m 3m } { minjun 2p 3p 4p } { minkou 5s 5s 5s } { minkou G G G } { S S }) => {
					uumensai();
					hatsu();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn honitsu1() {
		test!((6p 6p 7p 8p 9p S S N N N { minjun 2p 1p 3p })
			+ 6p => [
				({ anjun 7p 8p 9p } { ankou N N N } { minjun 2p 1p 3p } { ankou 6p 6p 6p shanpon } { S S }) => {
					honitsu();
				}
			]
			+ S => [
				({ anjun 7p 8p 9p } { ankou N N N } { minjun 2p 1p 3p } { ankou S S S shanpon } { 6p 6p }) => {
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honiisou&oldid=29051
	#[test]
	fn honitsu2() {
		test!((1m 1m 1m 2m 3m 4m 8m 8m G G { minkou W W W })
			+ 8m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { minkou W W W } { ankou 8m 8m 8m shanpon } { G G }) => {
					honitsu();
				}
			]
			+ G => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { minkou W W W } { ankou G G G shanpon } { 8m 8m }) => {
					honitsu();
					hatsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Half Flush
	#[test]
	fn honitsu4() {
		test!((1m 1m 1m 2m 3m 4m 5m 6m 7m S S S Wh)
			+ Wh => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { ankou S S S } { Wh Wh }) => {
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn junchan1() {
		test!((1m 9m 9m 9m 7p 8p 9p 1s 2s 3s { minjun 2s 1s 3s })
			+ 1m => [
				({ ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 1s 2s 3s } { minjun 2s 1s 3s } { 1m 1m }) => {
					junchan();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Junchantaiyaochuu&oldid=29104
	#[test]
	fn junchan2() {
		test!((1m 2m 3m 9m 9m 9m 7p 8p 9p 1s 1s 7s 8s)
			+ 9s => [
				({ anjun 1m 2m 3m } { ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 7s 8s 9s ryanmen_high } { 1s 1s }) => {
					junchan();
				}
			]
			+ 6s => [
				({ anjun 1m 2m 3m } { ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 6s 7s 8s ryanmen_low } { 1s 1s }) => {
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Fully Outside Hand
	#[test]
	fn junchan3() {
		test!((1s { minjun 1m 2m 3m } { minjun 7m 8m 9m } { minjun 1p 2p 3p } { minkou 9s 9s 9s })
			+ 1s => [
				({ minjun 1m 2m 3m } { minjun 7m 8m 9m } { minjun 1p 2p 3p } { minkou 9s 9s 9s } { 1s 1s }) => {
					junchan();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn ryanpeikou1() {
		test!((4m 4m 5m 5m 6m 6m 6p 6p 7p 8p 8p 2s 2s)
			+ 7p => [
				({ anjun 4m 5m 6m } { anjun 4m 5m 6m } { anjun 6p 7p 8p } { anjun 6p 7p 8p kanchan } { 2s 2s }) => {
					ryanpeikou();
					tanyao();
				}
				({ 4m 4m } { 5m 5m } { 6m 6m } { 6p 6p } { 8p 8p } { 2s 2s } { 7p 7p }) => {
					tanyao();
					chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryanpeikou&oldid=29561
	#[test]
	fn ryanpeikou2() {
		test!((2p 2p 3p 3p 4p 4p 6m 6m 7m 7m 8m 1s 1s)
			+ 8m => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_high } { 1s 1s }) => {
					ryanpeikou();
				}
				({ 2p 2p } { 3p 3p } { 4p 4p } { 6m 6m } { 7m 7m } { 1s 1s } { 8m 8m }) => {
					chiitoi();
				}
			]
			+ 5m => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6m 7m 8m } { anjun 5m 6m 7m ryanmen_low } { 1s 1s }) => {
					iipeikou();
					pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryanpeikou&oldid=29561
	#[test]
	fn ryanpeikou3() {
		test!((2m 2m 3m 3m 4m 4m 4m 4m 7p 8p 8p 9p 9p)
			+ 7p => [
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 7p 8p 9p penchan } { 4m 4m }) => {
					ryanpeikou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryanpeikou&oldid=29561
	#[test]
	fn ryanpeikou4() {
		test!((2s 2s 3s 3s 4s 4s 5s 5s 6s 6s 7s 7s 8s)
			+ 2s => [
				({ anjun 2s 3s 4s } { anjun 3s 4s 5s } { anjun 5s 6s 7s } { anjun 6s 7s 8s } { 2s 2s }) => {
					tanyao();
					chinitsu();
				}
				({ anjun 3s 4s 5s } { anjun 5s 6s 7s } { anjun 6s 7s 8s } { anjun 2s 3s 4s ryanmen_low } { 2s 2s }) => {
					tanyao();
					chinitsu();
				}
			]
			+ 5s => [
				({ anjun 3s 4s 5s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 5s 6s 7s ryanmen_low } { 2s 2s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 3s 4s 5s } { anjun 5s 6s 7s } { anjun 6s 7s 8s } { anjun 3s 4s 5s ryanmen_high } { 2s 2s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 6s 7s 8s } { 5s 5s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 5s 6s 7s ryanmen_low } { 5s 5s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
			]
			+ 8s => [
				({ anjun 3s 4s 5s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_high } { 2s 2s }) => {
					ryanpeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_high } { 5s 5s }) => {
					ryanpeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 5s 6s 7s } { 8s 8s }) => {
					ryanpeikou();
					tanyao();
					chinitsu();
				}
				({ 2s 2s } { 3s 3s } { 4s 4s } { 5s 5s } { 6s 6s } { 7s 7s } { 8s 8s }) => {
					tanyao();
					chiitoi();
					chinitsu();
					daichikurin();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Twice Pure Double Sequence
	#[test]
	fn ryanpeikou5() {
		test!((1s 2s 3s 1s 2s 3s 2p 3p 4p 2p 3p 4p E)
			+ E => [
				({ anjun 1s 2s 3s } { anjun 1s 2s 3s } { anjun 2p 3p 4p } { anjun 2p 3p 4p } { E E }) => {
					ryanpeikou();
				}
				({ 2p 2p } { 3p 3p } { 4p 4p } { 1s 1s } { 2s 2s } { 3s 3s } { E E }) => {
					chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn isshoku_sanjun1() {
		test!((1m 2m 1s 1s 1s 2s 2s 2s 3s 3s 3s R R)
			+ 3m => [
				({ ankou 1s 1s 1s } { ankou 2s 2s 2s } { ankou 3s 3s 3s } { anjun 1m 2m 3m penchan } { R R }) => {
					sanankou();
					sanrenkou();
				}
				({ anjun 1s 2s 3s } { anjun 1s 2s 3s } { anjun 1s 2s 3s } { anjun 1m 2m 3m penchan } { R R }) => {
					isshoku_sanjun();
					chanta();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Pure Triple Chow
	#[test]
	fn isshoku_sanjun2() {
		test!((8p { minjun 1m 2m 3m } { minjun 1m 2m 3m } { minjun 1m 2m 3m } { minjun 5s 6s 7s })
			+ 8p => [
				({ minjun 1m 2m 3m } { minjun 1m 2m 3m } { minjun 1m 2m 3m } { minjun 5s 6s 7s } { 8p 8p }) => {
					isshoku_sanjun();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn chinitsu1() {
		test!((1p 2p 3p 3p 4p 5p 0p 6p 6p 7p 9p 9p 9p)
			+ 3p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { 3p 3p }) => {
					chinitsu();
				}
				({ anjun 4p 5p 6p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { anjun 1p 2p 3p penchan } { 3p 3p }) => {
					chinitsu();
				}
			]
			+ 6p => [
				({ anjun 1p 2p 3p } { anjun 3p 4p 5p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { 6p 6p }) => {
					chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 3p 4p 5p } { ankou 9p 9p 9p } { anjun 0p 6p 7p kanchan } { 6p 6p }) => {
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=28979
	#[test]
	fn chinitsu2() {
		test!((1p 2p 3p 4p 4p 5p 5p 7p 7p 8p 8p 9p 9p)
			+ 4p => [
				({ anjun 1p 2p 3p } { anjun 7p 8p 9p } { anjun 7p 8p 9p } { ankou 4p 4p 4p shanpon } { 5p 5p }) => {
					chinitsu();
					iipeikou();
				}
			]
			+ 5p => [
				({ anjun 1p 2p 3p } { anjun 7p 8p 9p } { anjun 7p 8p 9p } { ankou 5p 5p 5p shanpon } { 4p 4p }) => {
					chinitsu();
					iipeikou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=28979
	#[test]
	fn chinitsu3() {
		test!((2m 3m 4m 5m 5m 6m 6m 6m 7m 7m 8m 9m 9m)
			+ 1m => [
				({ anjun 4m 5m 6m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 1m 2m 3m ryanmen_low } { 9m 9m }) => {
					chinitsu();
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 4m 5m 6m ryanmen_low } { 9m 9m }) => {
					chinitsu();
				}
				({ anjun 4m 5m 6m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 2m 3m 4m ryanmen_high } { 9m 9m }) => {
					chinitsu();
				}
			]
			+ 7m => [
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 5m 6m 7m } { anjun 6m 7m 8m kanchan } { 9m 9m }) => {
					chinitsu();
					iipeikou();
				}
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 5m 6m 7m ryanmen_high } { 9m 9m }) => {
					chinitsu();
					iipeikou();
				}
			]
			+ 8m => [
				({ anjun 2m 3m 4m } { ankou 6m 6m 6m } { anjun 7m 8m 9m } { anjun 7m 8m 9m kanchan } { 5m 5m }) => {
					chinitsu();
					iipeikou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=28979
	#[test]
	fn chinitsu4() {
		test!((1s 2s 3s 3s 4s 5s 6s 6s 6s 7s 7s 8s 8s)
			+ 3s => [
				({ anjun 1s 2s 3s } { anjun 4s 5s 6s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 3s 3s }) => {
					chinitsu();
					iipeikou();
				}
				({ anjun 4s 5s 6s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { anjun 1s 2s 3s penchan } { 3s 3s }) => {
					chinitsu();
					iipeikou();
				}
			]
			+ 6s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 6s 6s }) => {
					chinitsu();
					iipeikou();
				}
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_low } { 6s 6s }) => {
					chinitsu();
					iipeikou();
				}
			]
			+ 7s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { ankou 7s 7s 7s shanpon } { 8s 8s }) => {
					chinitsu();
				}
			]
			+ 8s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { ankou 8s 8s 8s shanpon } { 7s 7s }) => {
					chinitsu();
				}
			]
			+ 9s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 7s 8s 9s ryanmen_high } { 6s 6s }) => {
					chinitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Full Flush
	#[test]
	fn chinitsu5() {
		test!((9m { minjun 1m 2m 3m } { minjun 2m 3m 4m } { minjun 3m 4m 5m } { minkou 6m 6m 6m })
			+ 9m => [
				({ minjun 1m 2m 3m } { minjun 2m 3m 4m } { minjun 3m 4m 5m } { minkou 6m 6m 6m } { 9m 9m }) => {
					chinitsu();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn kokushi_musou1() {
		test!((1m 9m 1s 9s 1p 9p E S W N Wh Wh R)
			+ G => [
				(1m 9m 1s 9s 1p 9p E S W N Wh Wh R G) => {
					kokushi_musou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Kokushi_musou&oldid=30655
	#[test]
	fn kokushi_musou2() {
		test!((1m 1p 9p 1s 9s E S W N Wh G G R)
			+ 9m => [
				(1m 1p 9p 1s 9s E S W N Wh G G R 9m) => {
					kokushi_musou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Kokushi_musou&oldid=30655
	// Ref: Mahjong Soul -> Yaku Overview -> Thirteen-wait Thirteen Orphans
	#[test]
	fn kokushi_musou3() {
		test!((1m 9m 1p 9p 1s 9s E S W N Wh G R)
			+ 1m => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R 1m) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ 9m => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R 9m) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ 1p => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R 1p) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ 9p => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R 9p) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ 1s => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R 1s) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ 9s => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R 9s) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ E => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R E) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ S => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R S) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ W => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R W) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ N => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R N) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ Wh => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R Wh) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ G => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R G) => {
					kokushi_musou_juusanmen_machi();
				}
			]
			+ R => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R R) => {
					kokushi_musou_juusanmen_machi();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Thirteen Orphans
	#[test]
	fn kokushi_musou4() {
		test!((1m 9m 1p 9p 9p 1s 9s E S W N Wh G)
			+ R => [
				(1m 9m 1p 9p 9p 1s 9s E S W N Wh G R) => {
					kokushi_musou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn suuankou1() {
		test!((2m 2m 2m 4p 4p 4p 8m 8m 8m R R S S)
			+ R => [
				({ ankou 2m 2m 2m } { ankou 4p 4p 4p } { ankou 8m 8m 8m } { ankou R R R shanpon } { S S }) => {
					suuankou();
					chun();
					toitoi();
				}
			]
			+ S => [
				({ ankou 2m 2m 2m } { ankou 4p 4p 4p } { ankou 8m 8m 8m } { ankou S S S shanpon } { R R }) => {
					suuankou();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suuankou&oldid=25891
	#[test]
	fn suuankou2() {
		test!((5p 5p 6p 6p 6p 1s 1s 1s 8s 8s G G G)
			+ 5p => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { ankou 5p 5p 5p shanpon } { 8s 8s }) => {
					suuankou();
					hatsu();
					toitoi();
				}
			]
			+ 5p ron => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { minkou 5p 5p 5p shanpon } { 8s 8s }) => {
					hatsu();
					toitoi();
					sanankou();
				}
			]
			+ 8s => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { ankou 8s 8s 8s shanpon } { 5p 5p }) => {
					suuankou();
					hatsu();
					toitoi();
				}
			]
			+ 8s ron => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { minkou 8s 8s 8s shanpon } { 5p 5p }) => {
					hatsu();
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suuankou&oldid=25891
	#[test]
	fn suuankou3() {
		test!((8p 8p 8p 3s 3s 3s 4s 4s 4s 9m S S S)
			+ 9m => [
				({ ankou 8p 8p 8p } { ankou 3s 3s 3s } { ankou 4s 4s 4s } { ankou S S S } { 9m 9m }) => {
					suuankou_tanki();
					toitoi();
				}
			]
			+ 9m ron => [
				({ ankou 8p 8p 8p } { ankou 3s 3s 3s } { ankou 4s 4s 4s } { ankou S S S } { 9m 9m ron }) => {
					suuankou_tanki();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suuankou&oldid=25891
	#[test]
	fn suuankou4() {
		test!((3p 3p 3p 2s 2s 2s 3s 7s 7s 7s { ankan 1s 1s 1s 1s })
			+ 3s => [
				({ ankou 3p 3p 3p } { ankou 2s 2s 2s } { ankou 7s 7s 7s } { ankan 1s 1s 1s 1s } { 3s 3s }) => {
					suuankou_tanki();
					toitoi();
				}
			]
			+ 4s => [
				({ ankou 3p 3p 3p } { ankou 7s 7s 7s } { ankan 1s 1s 1s 1s } { anjun 2s 3s 4s ryanmen_high } { 2s 2s }) => {
					sanankou();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Four Concealed Triplets
	#[test]
	fn suuankou5() {
		test!((1m 1m 1m 2m 2m 2m 3p 3p 3p 4p 4p 4p 5s)
			+ 5s => [
				({ ankou 1m 1m 1m } { ankou 2m 2m 2m } { ankou 3p 3p 3p } { ankou 4p 4p 4p } { 5s 5s }) => {
					suuankou_tanki();
					toitoi();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Single-wait Four Concealed Triplets
	#[test]
	fn suuankou6() {
		test!((1m 1m 1m 2m 2m 2m 5p 5p 5p 7s 7s 7s N)
			+ N => [
				({ ankou 1m 1m 1m } { ankou 2m 2m 2m } { ankou 5p 5p 5p } { ankou 7s 7s 7s } { N N }) => {
					suuankou_tanki();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn daisangen1() {
		test!((3m 4m 5m 2s Wh Wh Wh R R R { minkou G G G })
			+ 2s => [
				({ anjun 3m 4m 5m } { ankou Wh Wh Wh } { ankou R R R } { minkou G G G } { 2s 2s }) => {
					daisangen();
					haku();
					hatsu();
					chun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Daisangen&oldid=27370
	#[test]
	fn daisangen2() {
		test!((4m 5m 6m 3p 3p Wh Wh { minkou G G G } { minkou R R R })
			+ Wh => [
				({ anjun 4m 5m 6m } { minkou G G G } { minkou R R R } { ankou Wh Wh Wh shanpon } { 3p 3p }) => {
					daisangen();
					haku();
					hatsu();
					chun();
				}
			]
			+ 3p => [
				({ anjun 4m 5m 6m } { minkou G G G } { minkou R R R } { ankou 3p 3p 3p shanpon } { Wh Wh }) => {
					shousangen();
					hatsu();
					chun();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Big Three Dragons
	#[test]
	fn daisangen3() {
		test!((9s { minjun 1s 2s 3s } { minkou Wh Wh Wh } { minkou G G G } { minkou R R R })
			+ 9s => [
				({ minjun 1s 2s 3s } { minkou Wh Wh Wh } { minkou G G G } { minkou R R R } { 9s 9s }) => {
					daisangen();
					haku();
					hatsu();
					chun();
					chanta();
					shiiaru_raotai();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	//
	// > Shousuushii
	#[test]
	fn suushii1() {
		test!((8m 8m 8m E S S S { minkou W W W } { minkou N N N })
			+ E => [
				({ ankou 8m 8m 8m } { ankou S S S } { minkou W W W } { minkou N N N } { E E }) => {
					shousuushii();
					toitoi();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	//
	// > Daisuushii
	#[test]
	fn suushii2() {
		test!((5p E E E S S S N N N { minkou W W W })
			+ 5p => [
				({ ankou E E E } { ankou S S S } { ankou N N N } { minkou W W W } { 5p 5p }) => {
					daisuushii();
					toitoi();
					sanankou();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=30927
	#[test]
	fn suushii3() {
		test!((4p 5p 6p E E E S S W W { minkou N N N })
			+ S => [
				({ anjun 4p 5p 6p } { ankou E E E } { minkou N N N } { ankou S S S shanpon } { W W }) => {
					shousuushii();
					honitsu();
				}
			]
			+ W => [
				({ anjun 4p 5p 6p } { ankou E E E } { minkou N N N } { ankou W W W shanpon } { S S }) => {
					shousuushii();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=30927
	#[test]
	fn suushii4() {
		test!((2m E E E W W W N N N { minkou S S S })
			+ 2m => [
				({ ankou E E E } { ankou W W W } { ankou N N N } { minkou S S S } { 2m 2m }) => {
					daisuushii();
					toitoi();
					sanankou();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=30927
	#[test]
	fn suushii5() {
		test!((7s 7s S S N N N { minkou E E E } { minkan W W W W })
			+ S => [
				({ ankou N N N } { minkou E E E } { minkan W W W W } { ankou S S S shanpon } { 7s 7s }) => {
					daisuushii();
					toitoi();
					honitsu();
				}
			]
			+ 7s => [
				({ ankou N N N } { minkou E E E } { minkan W W W W } { ankou 7s 7s 7s shanpon } { S S }) => {
					shousuushii();
					toitoi();
					honitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Four Little Winds
	#[test]
	fn shousuushii() {
		test!((N { minjun 1p 2p 3p } { minkou E E E } { minkou S S S } { minkou W W W })
			+ N => [
				({ minjun 1p 2p 3p } { minkou E E E } { minkou S S S } { minkou W W W } { N N }) => {
					shousuushii();
					shiiaru_raotai();
					chanta();
					honitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Four Big Winds
	#[test]
	fn daisuushii() {
		test!((5p { minkou E E E } { minkou S S S } { minkou W W W } { minkou N N N })
			+ 5p => [
				({ minkou E E E } { minkou S S S } { minkou W W W } { minkou N N N } { 5p 5p }) => {
					daisuushii();
					shiiaru_raotai();
					toitoi();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn tsuuiisou1() {
		test!((E E E W W Wh Wh { minkou S S S } { minkou G G G })
			+ W => [
				({ ankou E E E } { minkou S S S } { minkou G G G } { ankou W W W shanpon } { Wh Wh }) => {
					tsuuiisou();
					hatsu();
					toitoi();
				}
			]
			+ Wh => [
				({ ankou E E E } { minkou S S S } { minkou G G G } { ankou Wh Wh Wh shanpon } { W W }) => {
					tsuuiisou();
					haku();
					hatsu();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tsuuiisou&oldid=30677
	#[test]
	fn tsuuiisou2() {
		test!((E E E S S S G G N N { minkou R R R })
			+ G => [
				({ ankou E E E } { ankou S S S } { minkou R R R } { ankou G G G shanpon } { N N }) => {
					tsuuiisou();
					hatsu();
					chun();
					toitoi();
					sanankou();
				}
			]
			+ N => [
				({ ankou E E E } { ankou S S S } { minkou R R R } { ankou N N N shanpon } { G G }) => {
					tsuuiisou();
					chun();
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tsuuiisou&oldid=30677
	#[test]
	fn tsuuiisou3() {
		test!((E E S S W W N N Wh Wh G G R)
			+ R => [
				({ E E } { S S } { W W } { N N } { Wh Wh } { G G } { R R }) => {
					tsuuiisou();
					chiitoi();
					daichiishin();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> All Honors
	#[test]
	fn tsuuiisou4() {
		test!((G { minkou E E E } { minkou S S S } { minkou W W W } { minkou Wh Wh Wh })
			+ G => [
				({ minkou E E E } { minkou S S S } { minkou W W W } { minkou Wh Wh Wh } { G G }) => {
					tsuuiisou();
					haku();
					shiiaru_raotai();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn chinroutou1() {
		test!((1m 1m 1m 9m 9m 9m 1s 1s 9s 9s { minkou 1p 1p 1p })
			+ 1s => [
				({ ankou 1m 1m 1m } { ankou 9m 9m 9m } { minkou 1p 1p 1p } { ankou 1s 1s 1s shanpon } { 9s 9s }) => {
					chinroutou();
					toitoi();
					sanankou();
					sanshoku_doukou();
				}
			]
			+ 9s => [
				({ ankou 1m 1m 1m } { ankou 9m 9m 9m } { minkou 1p 1p 1p } { ankou 9s 9s 9s shanpon } { 1s 1s }) => {
					chinroutou();
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chinroutou&oldid=27235
	#[test]
	fn chinroutou2() {
		test!((1m 1m 1m 9p 9p 9p 1p 1p 9m 9m { minkou 1s 1s 1s })
			+ 1p => [
				({ ankou 1m 1m 1m } { ankou 9p 9p 9p } { minkou 1s 1s 1s } { ankou 1p 1p 1p shanpon } { 9m 9m }) => {
					chinroutou();
					toitoi();
					sanankou();
					sanshoku_doukou();
				}
			]
			+ 9m => [
				({ ankou 1m 1m 1m } { ankou 9p 9p 9p } { minkou 1s 1s 1s } { ankou 9m 9m 9m shanpon } { 1p 1p }) => {
					chinroutou();
					toitoi();
					sanankou();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> All Terminals
	#[test]
	fn chinroutou3() {
		test!((1s { minkou 1m 1m 1m } { minkou 9m 9m 9m } { minkou 1p 1p 1p } { minkou 9p 9p 9p })
			+ 1s => [
				({ minkou 1m 1m 1m } { minkou 9m 9m 9m } { minkou 1p 1p 1p } { minkou 9p 9p 9p } { 1s 1s }) => {
					chinroutou();
					shiiaru_raotai();
					toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn ryuuiisou1() {
		test!((2s 2s 3s 3s 4s 4s 6s 6s 6s 8s 8s G G)
			+ 8s => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou 8s 8s 8s shanpon } { G G }) => {
					ryuuiisou();
					iipeikou();
					honitsu();
				}
			]
			+ G => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G shanpon } { 8s 8s }) => {
					ryuuiisou();
					iipeikou();
					hatsu();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=28607
	#[test]
	fn ryuuiisou2() {
		test!((2s 2s 3s 3s 4s 4s 6s 6s 8s 8s G G G)
			+ 6s => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou G G G } { ankou 6s 6s 6s shanpon } { 8s 8s }) => {
					ryuuiisou();
					iipeikou();
					hatsu();
					honitsu();
				}
			]
			+ 8s => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou G G G } { ankou 8s 8s 8s shanpon } { 6s 6s }) => {
					ryuuiisou();
					iipeikou();
					hatsu();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=28607
	#[test]
	fn ryuuiisou3() {
		test!((2s 2s 2s 3s 3s 4s 4s 4s 8s 8s { minkou 6s 6s 6s })
			+ 3s => [
				({ ankou 2s 2s 2s } { ankou 4s 4s 4s } { minkou 6s 6s 6s } { ankou 3s 3s 3s shanpon } { 8s 8s }) => {
					tanyao();
					toitoi();
					sanankou();
					sanrenkou();
					chinitsu();
					chinryuusou();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { minkou 6s 6s 6s } { anjun 2s 3s 4s kanchan } { 8s 8s }) => {
					tanyao();
					chinitsu();
					isshoku_sanjun();
					chinryuusou();
				}
			]
			+ 8s => [
				({ ankou 2s 2s 2s } { ankou 4s 4s 4s } { minkou 6s 6s 6s } { ankou 8s 8s 8s shanpon } { 3s 3s }) => {
					tanyao();
					toitoi();
					sanankou();
					chinitsu();
					chinryuusou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=28607
	#[test]
	fn ryuuiisou4() {
		test!((2s 3s 4s 4s 4s 6s 6s 6s 8s 8s G G G)
			+ 1s => [
				({ ankou 4s 4s 4s } { ankou 6s 6s 6s } { ankou G G G } { anjun 1s 2s 3s ryanmen_low } { 8s 8s }) => {
					hatsu();
					sanankou();
					honitsu();
				}
			]
			+ 4s => [
				({ anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G } { ankou 4s 4s 4s shanpon } { 8s 8s }) => {
					ryuuiisou();
					hatsu();
					sanankou();
					honitsu();
				}
				({ ankou 4s 4s 4s } { ankou 6s 6s 6s } { ankou G G G } { anjun 2s 3s 4s ryanmen_high } { 8s 8s }) => {
					ryuuiisou();
					hatsu();
					sanankou();
					honitsu();
				}
			]
			+ 8s => [
				({ anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G } { ankou 8s 8s 8s shanpon } { 4s 4s }) => {
					ryuuiisou();
					hatsu();
					sanankou();
					honitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> All Green
	#[test]
	fn ryuuiisou5() {
		test!((G { minkou 2s 2s 2s } { minkou 3s 3s 3s } { minkou 4s 4s 4s } { minkou 6s 6s 6s })
			+ G => [
				({ minkou 2s 2s 2s } { minkou 3s 3s 3s } { minkou 4s 4s 4s } { minkou 6s 6s 6s } { G G }) => {
					ryuuiisou();
					shiiaru_raotai();
					toitoi();
					sanrenkou();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn chuuren_poutou1() {
		test!((1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m)
			+ 1m => [
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_low } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { ankou 1m 1m 1m shanpon } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
			]
			+ 2m => [
				({ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 2m 2m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 3m => [
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 3m 4m 5m ryanmen_low } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 1m 2m 3m penchan } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 4m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 4m 5m 6m ryanmen_low } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_high } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 5m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 5m 5m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 6m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 6m 7m 8m ryanmen_low } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 4m 5m 6m ryanmen_high } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 7m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 7m 8m 9m penchan } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 5m 6m 7m ryanmen_high } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 8m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { ankou 9m 9m 9m } { 8m 8m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 9m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { ankou 9m 9m 9m shanpon } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 7m 8m 9m ryanmen_high } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chuuren_poutou&oldid=28336
	#[test]
	fn chuuren_poutou2() {
		test!((1p 1p 1p 2p 3p 4p 5p 5p 7p 8p 9p 9p 9p)
			+ 6p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { ankou 9p 9p 9p } { anjun 6p 7p 8p ryanmen_low } { 5p 5p }) => {
					chuuren_poutou();
					chinitsu();
				}
			]
			+ 5p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { ankou 5p 5p 5p shanpon } { 9p 9p }) => {
					chinitsu();
				}
			]
			+ 9p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { ankou 9p 9p 9p shanpon } { 5p 5p }) => {
					chinitsu();
				}
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { ankou 9p 9p 9p } { anjun 7p 8p 9p ryanmen_high } { 5p 5p }) => {
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chuuren_poutou&oldid=28336
	#[test]
	fn chuuren_poutou3() {
		test!((1p 1p 1p 2p 3p 4p 5p 6p 7p 8p 9p 9p 9p)
			+ 1p => [
				({ ankou 1p 1p 1p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { anjun 1p 2p 3p ryanmen_low } { 9p 9p }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { ankou 1p 1p 1p shanpon } { 9p 9p }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
			]
			+ 2p => [
				({ ankou 1p 1p 1p } { anjun 3p 4p 5p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { 2p 2p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 3p => [
				({ anjun 1p 2p 3p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 3p 4p 5p ryanmen_low } { 1p 1p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ anjun 3p 4p 5p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 1p 2p 3p penchan } { 1p 1p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 4p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { anjun 4p 5p 6p ryanmen_low } { 9p 9p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ ankou 1p 1p 1p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { anjun 2p 3p 4p ryanmen_high } { 9p 9p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 5p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { 5p 5p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 6p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 6p 7p 8p ryanmen_low } { 1p 1p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 4p 5p 6p ryanmen_high } { 1p 1p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 7p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 7p 8p 9p penchan } { 9p 9p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { anjun 5p 6p 7p ryanmen_high } { 9p 9p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 8p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { ankou 9p 9p 9p } { 8p 8p }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 9p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { ankou 9p 9p 9p shanpon } { 1p 1p }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 7p 8p 9p ryanmen_high } { 1p 1p }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Nine Gates
	#[test]
	fn chuuren_poutou4() {
		test!((1m 1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m)
			+ 9m => [
				({ ankou 1m 1m 1m } { anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { 9m 9m }) => {
					chuuren_poutou();
					ittsuu();
					chinitsu();
				}
				({ ankou 1m 1m 1m } { anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m ryanmen_high } { 9m 9m }) => {
					chuuren_poutou();
					ittsuu();
					chinitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> True Nine Gates
	#[test]
	fn chuuren_poutou5() {
		test!((1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m)
			+ 1m => [
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_low } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { ankou 1m 1m 1m shanpon } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
			]
			+ 2m => [
				({ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 2m 2m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 3m => [
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 3m 4m 5m ryanmen_low } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 1m 2m 3m penchan } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 4m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 4m 5m 6m ryanmen_low } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_high } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 5m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 5m 5m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 6m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 6m 7m 8m ryanmen_low } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 4m 5m 6m ryanmen_high } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 7m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 7m 8m 9m penchan } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 5m 6m 7m ryanmen_high } { 9m 9m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 8m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { ankou 9m 9m 9m } { 8m 8m }) => {
					chuuren_poutou_kyuumen_machi();
					chinitsu();
				}
			]
			+ 9m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { ankou 9m 9m 9m shanpon } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 7m 8m 9m ryanmen_high } { 1m 1m }) => {
					chuuren_poutou_kyuumen_machi();
					ittsuu();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=30136
	#[test]
	fn suukantsu1() {
		test!((N { minkan 6p 6p 6p 6p } { minkan 2m 2m 2m 2m } { ankan R R R R } { minkan 4s 4s 4s 4s })
			+ N => [
				({ minkan 6p 6p 6p 6p } { minkan 2m 2m 2m 2m } { ankan R R R R } { minkan 4s 4s 4s 4s } { N N }) => {
					suukantsu();
					chun();
					shiiaru_raotai();
					toitoi();
					uumensai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suukantsu&oldid=29603
	#[test]
	fn suukantsu2() {
		test!((N { ankan 4p 4p 4p 4p } { minkan 1m 1m 1m 1m } { minkan 7s 7s 7s 7s } { ankan G G G G })
			+ N => [
				({ ankan 4p 4p 4p 4p } { minkan 1m 1m 1m 1m } { minkan 7s 7s 7s 7s } { ankan G G G G } { N N }) => {
					suukantsu();
					shiiaru_raotai();
					hatsu();
					toitoi();
					uumensai();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Four Quads
	#[test]
	fn suukantsu3() {
		test!((G { minkan 1m 1m 1m 1m } { minkan 2p 2p 2p 2p } { minkan 3s 3s 3s 3s } { minkan E E E E })
			+ G => [
				({ minkan 1m 1m 1m 1m } { minkan 2p 2p 2p 2p } { minkan 3s 3s 3s 3s } { minkan E E E E } { G G }) => {
					suukantsu();
					shiiaru_raotai();
					toitoi();
					uumensai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn suurenkou1() {
		test!((4s 4s 4s 9s { minkou 2s 2s 2s } { minkou 3s 3s 3s } { minkou 0s 5s 5s })
			+ 9s => [
				({ minkou 2s 2s 2s } { minkou 3s 3s 3s } { ankou 4s 4s 4s } { minkou 5s 5s 0s } { 9s 9s }) => {
					suurenkou();
					toitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn suurenkou2() {
		test!((1m 1m 5m 5m { minkou 2m 2m 2m } { minkou 3m 3m 3m } { minkou 4m 4m 4m })
			+ 1m => [
				({ minkou 2m 2m 2m } { minkou 3m 3m 3m } { minkou 4m 4m 4m } { ankou 1m 1m 1m shanpon } { 5m 5m }) => {
					suurenkou();
					toitoi();
					chinitsu();
				}
			]
			+ 5m => [
				({ minkou 2m 2m 2m } { minkou 3m 3m 3m } { minkou 4m 4m 4m } { ankou 5m 5m 5m shanpon } { 1m 1m }) => {
					suurenkou();
					toitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn suurenkou3() {
		test!((N { minkou 6p 6p 6p } { minkou 5p 5p 5p } { minkan 7p 7p 7p 7p } { minkou 4p 4p 4p })
			+ N => [
				({ minkou 4p 4p 4p } { minkou 5p 5p 5p } { minkou 6p 6p 6p } { minkan 7p 7p 7p 7p } { N N }) => {
					suurenkou();
					shiiaru_raotai();
					toitoi();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn daisharin1() {
		test!((2p 2p 3p 3p 4p 5p 5p 6p 6p 7p 7p 8p 8p)
			+ 4p => [
				({ anjun 3p 4p 5p } { anjun 6p 7p 8p } { anjun 6p 7p 8p } { anjun 3p 4p 5p kanchan } { 2p 2p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 6p 7p 8p } { anjun 6p 7p 8p } { anjun 2p 3p 4p ryanmen_high } { 5p 5p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 5p 6p 7p } { anjun 2p 3p 4p ryanmen_high } { 8p 8p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2p 2p } { 3p 3p } { 5p 5p } { 6p 6p } { 7p 7p } { 8p 8p } { 4p 4p }) => {
					daisharin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Daisharin&oldid=28085
	#[test]
	fn daisharin2() {
		test!((2p 2p 3p 3p 4p 4p 5p 6p 6p 7p 7p 8p 8p)
			+ 5p => [
				({ anjun 3p 4p 5p } { anjun 6p 7p 8p } { anjun 6p 7p 8p } { anjun 3p 4p 5p ryanmen_high } { 2p 2p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6p 7p 8p } { anjun 6p 7p 8p } { 5p 5p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 5p 6p 7p ryanmen_low } { 8p 8p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2p 2p } { 3p 3p } { 4p 4p } { 6p 6p } { 7p 7p } { 8p 8p } { 5p 5p }) => {
					daisharin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
			+ 2p => [
				({ anjun 2p 3p 4p } { anjun 3p 4p 5p } { anjun 6p 7p 8p } { anjun 6p 7p 8p } { 2p 2p }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 3p 4p 5p } { anjun 6p 7p 8p } { anjun 6p 7p 8p } { anjun 2p 3p 4p ryanmen_low } { 2p 2p }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
			]
			+ 8p => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 6p 7p 8p } { 8p 8p }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 6p 7p 8p ryanmen_high } { 8p 8p }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Big Wheels
	#[test]
	fn daisharin3() {
		test!((2p 2p 3p 3p 4p 4p 5p 5p 6p 6p 7p 7p 8p)
			+ 8p => [
				({ anjun 3p 4p 5p } { anjun 3p 4p 5p } { anjun 6p 7p 8p } { anjun 6p 7p 8p ryanmen_high } { 2p 2p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6p 7p 8p } { anjun 6p 7p 8p ryanmen_high } { 5p 5p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 5p 6p 7p } { 8p 8p }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2p 2p } { 3p 3p } { 4p 4p } { 5p 5p } { 6p 6p } { 7p 7p } { 8p 8p }) => {
					daisharin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn daichikurin1() {
		test!((2s 2s 3s 4s 4s 0s 5s 6s 6s 7s 7s 8s 8s)
			+ 3s => [
				({ anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { anjun 3s 4s 0s ryanmen_low } { 2s 2s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { anjun 2s 3s 4s kanchan } { 5s 0s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 0s 6s 7s } { anjun 2s 3s 4s kanchan } { 8s 8s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2s 2s } { 4s 4s } { 5s 0s } { 6s 6s } { 7s 7s } { 8s 8s } { 3s 3s }) => {
					daichikurin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Daisharin&oldid=28085
	#[test]
	fn daichikurin2() {
		test!((2s 3s 3s 4s 4s 5s 5s 6s 6s 7s 7s 8s 8s)
			+ 2s => [
				({ anjun 3s 4s 5s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 2s 2s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { anjun 2s 3s 4s ryanmen_low } { 5s 5s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 5s 6s 7s } { anjun 2s 3s 4s ryanmen_low } { 8s 8s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 3s 3s } { 4s 4s } { 5s 5s } { 6s 6s } { 7s 7s } { 8s 8s } { 2s 2s }) => {
					daichikurin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
			+ 5s => [
				({ anjun 2s 3s 4s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 5s 5s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { anjun 3s 4s 5s ryanmen_high } { 5s 5s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 3s 4s 5s } { anjun 5s 6s 7s } { anjun 5s 6s 7s ryanmen_low } { 8s 8s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 5s 6s 7s } { anjun 3s 4s 5s ryanmen_high } { 8s 8s }) => {
					iipeikou();
					tanyao();
					chinitsu();
				}
			]
			+ 8s => [
				({ anjun 2s 3s 4s } { anjun 3s 4s 5s } { anjun 5s 6s 7s } { anjun 6s 7s 8s } { 8s 8s }) => {
					tanyao();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 3s 4s 5s } { anjun 5s 6s 7s } { anjun 6s 7s 8s ryanmen_high } { 8s 8s }) => {
					tanyao();
					chinitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Bamboo Forest
	#[test]
	fn daichikurin3() {
		test!((2s 2s 3s 3s 4s 4s 5s 5s 6s 6s 7s 7s 8s)
			+ 8s => [
				({ anjun 3s 4s 5s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_high } { 2s 2s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_high } { 5s 5s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 5s 6s 7s } { 8s 8s }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2s 2s } { 3s 3s } { 4s 4s } { 5s 5s } { 6s 6s } { 7s 7s } { 8s 8s }) => {
					daichikurin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn daisuurin1() {
		test!((2m 2m 3m 3m 4m 4m 5m 5m 6m 6m 7m 7m 8m)
			+ 8m => [
				({ anjun 3m 4m 5m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_high } { 2m 2m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_high } { 5m 5m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 5m 6m 7m } { 8m 8m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2m 2m } { 3m 3m } { 4m 4m } { 5m 5m } { 6m 6m } { 7m 7m } { 8m 8m }) => {
					daisuurin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Daisharin&oldid=28085
	#[test]
	fn daisuurin2() {
		test!((2m 2m 3m 3m 4m 4m 5m 5m 6m 7m 7m 8m 8m)
			+ 6m => [
				({ anjun 3m 4m 5m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_low } { 2m 2m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_low } { 5m 5m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 5m 6m 7m kanchan } { 8m 8m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2m 2m } { 3m 3m } { 4m 4m } { 5m 5m } { 7m 7m } { 8m 8m } { 6m 6m }) => {
					daisuurin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
			+ 9m => [
				({ anjun 3m 4m 5m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { anjun 7m 8m 9m ryanmen_high } { 2m 2m }) => {
					iipeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { anjun 7m 8m 9m ryanmen_high } { 5m 5m }) => {
					iipeikou();
					chinitsu();
				}
			]
		);
	}

	// Ref: Mahjong Soul -> Yaku Overview -> Numerous Neighbours
	#[test]
	fn daisuurin3() {
		test!((2m 2m 3m 3m 4m 4m 5m 5m 6m 6m 7m 7m 8m)
			+ 8m => [
				({ anjun 3m 4m 5m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_high } { 2m 2m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_high } { 5m 5m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 5m 6m 7m } { 8m 8m }) => {
					tanyao();
					ryanpeikou();
					chinitsu();
				}
				({ 2m 2m } { 3m 3m } { 4m 4m } { 5m 5m } { 6m 6m } { 7m 7m } { 8m 8m }) => {
					daisuurin();
					tanyao();
					chiitoi();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn isshoku_yonjun1() {
		test!((1m 1m 2p 2p 3p 3p 4p { minjun 2p 3p 4p } { minjun 4p 2p 3p })
			+ 4p => [
				({ anjun 2p 3p 4p } { minjun 2p 3p 4p } { minjun 2p 3p 4p } { anjun 2p 3p 4p ryanmen_high } { 1m 1m }) => {
					isshoku_yonjun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn isshoku_yonjun2() {
		test!((8p 8p 2s 2s 2s 2s 3s 3s 3s 4s 4s 4s 4s)
			+ 3s => [
				({ ankou 2s 2s 2s } { anjun 2s 3s 4s } { ankou 4s 4s 4s } { ankou 3s 3s 3s shanpon } { 8p 8p }) => {
					tanyao();
					sanankou();
					sanrenkou();
				}
				({ ankou 2s 2s 2s } { ankou 3s 3s 3s } { ankou 4s 4s 4s } { anjun 2s 3s 4s kanchan } { 8p 8p }) => {
					tanyao();
					sanankou();
					sanrenkou();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 2s 3s 4s kanchan } { 8p 8p }) => {
					isshoku_yonjun();
					tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn isshoku_yonjun3() {
		test!((5m { minjun 7p 8p 9p } { minjun 8p 7p 9p } { minjun 8p 7p 9p } { minjun 9p 7p 8p })
			+ 5m => [
				({ minjun 7p 8p 9p } { minjun 7p 8p 9p } { minjun 7p 8p 9p } { minjun 7p 8p 9p } { 5m 5m }) => {
					isshoku_yonjun();
					shiiaru_raotai();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn hyakuman_goku1() {
		test!((2m 3m 6m 6m 6m 7m 7m { ankan 8m 8m 8m 8m } { minkan 9m 9m 9m 9m })
			+ 1m => [
				({ ankou 6m 6m 6m } { ankan 8m 8m 8m 8m } { minkan 9m 9m 9m 9m } { anjun 1m 2m 3m ryanmen_low } { 7m 7m }) => {
					hyakuman_goku();
					chinitsu();
				}
			]
			+ 4m => [
				({ ankou 6m 6m 6m } { ankan 8m 8m 8m 8m } { minkan 9m 9m 9m 9m } { anjun 2m 3m 4m ryanmen_high } { 7m 7m }) => {
					hyakuman_goku();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn hyakuman_goku2() {
		test!((2m 2m 5m 6m 7m 9m 9m { minkou 7m 7m 7m } { minkan 8m 8m 8m 8m })
			+ 9m => [
				({ anjun 5m 6m 7m } { minkou 7m 7m 7m } { minkan 8m 8m 8m 8m } { ankou 9m 9m 9m shanpon } { 2m 2m }) => {
					hyakuman_goku();
					sanrenkou();
					chinitsu();
				}
			]
			+ 2m => [
				({ anjun 5m 6m 7m } { minkou 7m 7m 7m } { minkan 8m 8m 8m 8m } { ankou 2m 2m 2m shanpon } { 9m 9m }) => {
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn hyakuman_goku3() {
		test!((5m 5m 5m 6m 7m 9m 9m { minkou 7m 7m 7m } { minkou 8m 8m 8m })
			+ 9m => [
				({ anjun 5m 6m 7m } { minkou 7m 7m 7m } { minkou 8m 8m 8m } { ankou 9m 9m 9m shanpon } { 5m 5m }) => {
					hyakuman_goku();
					sanrenkou();
					chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn hyakuman_goku4() {
		test!((5m { minkan 6m 6m 6m 6m } { minkan 7m 7m 7m 7m } { minkan 8m 8m 8m 8m } { ankan 9m 9m 9m 9m })
			+ 5m => [
				({ minkan 6m 6m 6m 6m } { minkan 7m 7m 7m 7m } { minkan 8m 8m 8m 8m } { ankan 9m 9m 9m 9m } { 5m 5m }) => {
					hyakuman_goku();
					shiiaru_raotai();
					toitoi();
					chinitsu();
					suukantsu();
					suurenkou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn kouitten() {
		test!((2s 2s 3s 4s 4s 6s 6s { minjun 4s 2s 3s } { minkou R R R })
			+ 3s => [
				({ anjun 2s 3s 4s } { minjun 2s 3s 4s } { minkou R R R } { anjun 2s 3s 4s kanchan } { 6s 6s }) => {
					kouitten();
					chun();
					honitsu();
					isshoku_sanjun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn benikujaku() {
		test!((5s 7s 7s 7s 9s 9s 9s { minkou 1s 1s 1s } { minkou R R R })
			+ 0s => [
				({ minkou 1s 1s 1s } { ankou 7s 7s 7s } { ankou 9s 9s 9s } { minkou R R R } { 5s 0s }) => {
					benikujaku();
					chun();
					toitoi();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn kokuiisou1() {
		test!((4p 8p 8p 8p E E E W W W { minkou 2p 2p 2p })
			+ 4p => [
				({ minkou 2p 2p 2p } { ankou 8p 8p 8p } { ankou E E E } { ankou W W W } { 4p 4p }) => {
					kokuiisou();
					toitoi();
					sanankou();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn kokuiisou2() {
		test!((2p 2p 4p 4p 8p 8p E E S S W W N)
			+ N => [
				({ 2p 2p } { 4p 4p } { 8p 8p } { E E } { S S } { W W } { N N }) => {
					kokuiisou();
					chiitoi();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn golden_gate_bridge() {
		test!((9m 9m 1p 2p 3p 3p 4p 5p 5p 6p 7p 7p 9p)
			+ 8p => [
				({ anjun 1p 2p 3p } { anjun 3p 4p 5p } { anjun 5p 6p 7p } { anjun 7p 8p 9p kanchan } { 9m 9m }) => {
					golden_gate_bridge();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn touhoku_shinkansen1() {
		test!((1s 2s 3s 4s 5s 6s 7s 8s 9s E E E N)
			+ N => [
				({ anjun 1s 2s 3s } { anjun 4s 5s 6s } { anjun 7s 8s 9s } { ankou E E E } { N N }) => {
					touhoku_shinkansen();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn touhoku_shinkansen2() {
		test!((1p 2p 3p 4p 5p 6p 7p 8p 9p E E N N)
			+ N => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { ankou N N N shanpon } { E E }) => {
					touhoku_shinkansen();
					honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn daichiishin1() {
		test!((E E S S W N N Wh Wh G G R R)
			+ W => [
				({ E E } { S S } { N N } { Wh Wh } { G G } { R R } { W W }) => {
					daichiishin();
					chiitoi();
					tsuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tsuuiisou&oldid=30677
	// Ref: Mahjong Soul -> Yaku Overview -> Numerous Neighbours
	#[test]
	fn daichiishin2() {
		test!((E E S S W W N N Wh Wh G G R)
			+ R => [
				({ E E } { S S } { W W } { N N } { Wh Wh } { G G } { R R }) => {
					daichiishin();
					chiitoi();
					tsuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Local_yaku&oldid=29862
	#[test]
	fn chinryuusou() {
		test!((3s 4s 6s 6s 6s 8s 8s { minjun 3s 2s 4s } { minjun 3s 2s 4s })
			+ 2s => [
				({ minjun 2s 3s 4s } { minjun 2s 3s 4s } { ankou 6s 6s 6s } { anjun 2s 3s 4s ryanmen_low } { 8s 8s }) => {
					chinryuusou();
					tanyao();
					chinitsu();
					isshoku_sanjun();
				}
			]
		);
	}

	#[test]
	fn chanta_routou() {
		const EXPECTED_TANYAO: [bool; 7] = { let mut result = [false; _]; result[0] = true; result };
		const EXPECTED_CHANTA: [bool; 7] = { let mut result = [false; _]; result[1] = true; result };
		const EXPECTED_HONROUTOU: [bool; 7] = { let mut result = [false; _]; result[2] = true; result };
		const EXPECTED_JUNCHAN: [bool; 7] = { let mut result = [false; _]; result[3] = true; result };
		const EXPECTED_TSUUIISOU: [bool; 7] = { let mut result = [false; _]; result[4] = true; result };
		const EXPECTED_CHINROUTOU: [bool; 7] = { let mut result = [false; _]; result[5] = true; result };
		const EXPECTED_OTHER: [bool; 7] = { let mut result = [false; _]; result[6] = true; result };

		for (input_lhs, input_rhs, expected) in [
			(ChantaRoutou::has_terminals(), ChantaRoutou::has_terminals(), EXPECTED_JUNCHAN),
			(ChantaRoutou::has_terminals(), ChantaRoutou::all_terminals(), EXPECTED_JUNCHAN),
			(ChantaRoutou::has_terminals(), ChantaRoutou::all_honors(), EXPECTED_CHANTA),
			(ChantaRoutou::has_terminals(), ChantaRoutou::other(), EXPECTED_OTHER),
			(ChantaRoutou::all_terminals(), ChantaRoutou::has_terminals(), EXPECTED_JUNCHAN),
			(ChantaRoutou::all_terminals(), ChantaRoutou::all_terminals(), EXPECTED_CHINROUTOU),
			(ChantaRoutou::all_terminals(), ChantaRoutou::all_honors(), EXPECTED_HONROUTOU),
			(ChantaRoutou::all_terminals(), ChantaRoutou::other(), EXPECTED_OTHER),
			(ChantaRoutou::all_honors(), ChantaRoutou::has_terminals(), EXPECTED_CHANTA),
			(ChantaRoutou::all_honors(), ChantaRoutou::all_terminals(), EXPECTED_HONROUTOU),
			(ChantaRoutou::all_honors(), ChantaRoutou::all_honors(), EXPECTED_TSUUIISOU),
			(ChantaRoutou::all_honors(), ChantaRoutou::other(), EXPECTED_OTHER),
			(ChantaRoutou::other(), ChantaRoutou::has_terminals(), EXPECTED_OTHER),
			(ChantaRoutou::other(), ChantaRoutou::all_terminals(), EXPECTED_OTHER),
			(ChantaRoutou::other(), ChantaRoutou::all_honors(), EXPECTED_OTHER),
			(ChantaRoutou::other(), ChantaRoutou::other(), EXPECTED_TANYAO),
		] {
			let actual = input_lhs | input_rhs;
			let actual = [actual.is_tanyao(), actual.is_chanta(), actual.is_honroutou(), actual.is_junchan(), actual.is_tsuuiisou(), actual.is_chinroutou(), actual.is_other()];
			assert_eq!(actual, expected, "{input_lhs:?} | {input_rhs:?} = {actual:?}, expected {expected:?}");
		}
	}

	#[test]
	fn win_with_akadora() {
		test!((1p 2p 3p 3p 3p 4p 5p 6p 6p 7p 9p 9p 9p)
			+ 0p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 0p 6p 7p ryanmen_low } { 3p 3p }) => {
					chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 5p 6p 7p } { ankou 9p 9p 9p } { anjun 4p 0p 6p kanchan } { 3p 3p }) => {
					chinitsu();
				}
			]
		);

		test!((1p 2p 3p 3p 3p 4p 0p 6p 6p 7p 9p 9p 9p)
			+ 5p => [
				({ anjun 1p 2p 3p } { anjun 4p 0p 6p } { ankou 9p 9p 9p } { anjun 5p 6p 7p ryanmen_low } { 3p 3p }) => {
					chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { anjun 4p 5p 6p kanchan } { 3p 3p }) => {
					chinitsu();
				}
			]
		);
	}

	#[test]
	fn scorable_hand_set_tsumo_or_ron() {
		let test_cases: [(ScorableHand, ScorableHand); _] = [
			// Ankan(Tanki)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { ankan 6s 6s 6s 6s } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { ankan 6s 6s 6s 6s } { S S ron }).into(),
			),
			// Minkan(Tanki)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minkan 6s 6s 6s 6s } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minkan 6s 6s 6s 6s } { S S ron }).into(),
			),
			// Ankou(Tanki)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { ankou 6s 6s 6s } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { ankou 6s 6s 6s } { S S ron }).into(),
			),
			// Minkou(Tanki)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minkou 6s 6s 6s } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minkou 6s 6s 6s } { S S ron }).into(),
			),
			// Anjun(Tanki)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s } { S S ron }).into(),
			),
			// Minjun(Tanki)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s } { S S ron }).into(),
			),
			// Kou(Shanpon)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { ankou 6s 6s 6s shanpon } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minkou 6s 6s 6s shanpon } { S S }).into(),
			),
			// Shun(Kanchan)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s kanchan } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s kanchan } { S S }).into(),
			),
			// Shun(Penchan)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 7s 8s 9s penchan } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 7s 8s 9s penchan } { S S }).into(),
			),
			// Shun(RyanmenLow)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s ryanmen_low } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s ryanmen_low } { S S }).into(),
			),
			// Shun(RyanmenHigh)
			(
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s ryanmen_high } { S S }).into(),
				make_scorable_hand!({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s ryanmen_high } { S S }).into(),
			),
			// Chiitoi
			(
				make_scorable_hand!({ 1m 1m } { 2m 2m } { 3m 3m } { 4m 4m } { 5m 5m } { 6m 6m } { 7m 7m }).into(),
				make_scorable_hand!({ 1m 1m } { 2m 2m } { 3m 3m } { 4m 4m } { 5m 5m } { 6m 6m } { 7m 7m ron }).into(),
			),
			// KokushiMusou
			(
				make_scorable_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R R).into(),
				make_scorable_hand!(1m 9m 1p 9p 1s 9s E S W N Wh G R R ron).into(),
			),
		];
		for (h_tsumo, h_ron) in test_cases {
			for input in [h_tsumo, h_ron] {
				for tsumo_or_ron in [TsumoOrRon::Tsumo, TsumoOrRon::Ron] {
					let expected = match tsumo_or_ron {
						TsumoOrRon::Tsumo => h_tsumo,
						TsumoOrRon::Ron => h_ron,
					};
					let mut actual = input;
					actual.set_tsumo_or_ron(tsumo_or_ron);
					assert_eq!(actual, expected);
				}
			}
		}
	}

	#[test]
	fn scorable_hand_kokushi_musou_display() {
		for (duplicate, expected, expected_juusanmen) in [
			(t!(1m), "1m 1m 1p 9p 1s 9s E S W N Wh G R 9m", "1m 9m 1p 9p 1s 9s E S W N Wh G R 1m"),
			(t!(9m), "9m 9m 1p 9p 1s 9s E S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R 9m"),
			(t!(1p), "9m 1p 1p 9p 1s 9s E S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R 1p"),
			(t!(9p), "9m 1p 9p 9p 1s 9s E S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R 9p"),
			(t!(1s), "9m 1p 9p 1s 1s 9s E S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R 1s"),
			(t!(9s), "9m 1p 9p 1s 9s 9s E S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R 9s"),
			(t!(E), "9m 1p 9p 1s 9s E E S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R E"),
			(t!(S), "9m 1p 9p 1s 9s E S S W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R S"),
			(t!(W), "9m 1p 9p 1s 9s E S W W N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R W"),
			(t!(N), "9m 1p 9p 1s 9s E S W N N Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R N"),
			(t!(Wh), "9m 1p 9p 1s 9s E S W N Wh Wh G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R Wh"),
			(t!(G), "9m 1p 9p 1s 9s E S W N Wh G G R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R G"),
			(t!(R), "9m 1p 9p 1s 9s E S W N Wh G R R 1m", "1m 9m 1p 9p 1s 9s E S W N Wh G R R"),
		] {
			let t14 = if duplicate == t!(1m) { t!(9m) } else { t!(1m) };
			let hand = ScorableHandKokushiMusou { duplicate, t14, tsumo_or_ron: TsumoOrRon::Tsumo };
			let actual = std::string::ToString::to_string(&hand);
			assert_eq!(actual, expected);

			let t14 = if duplicate == t!(1m) { t!(9m) } else { t!(1m) };
			let hand = ScorableHandKokushiMusou { duplicate, t14, tsumo_or_ron: TsumoOrRon::Ron };
			let actual = std::string::ToString::to_string(&hand);
			assert_eq!(actual, std::format!("{expected} ron"));

			let t14 = duplicate;
			let hand = ScorableHandKokushiMusou { duplicate, t14, tsumo_or_ron: TsumoOrRon::Tsumo };
			let actual = std::string::ToString::to_string(&hand);
			assert_eq!(actual, expected_juusanmen);

			let t14 = duplicate;
			let hand = ScorableHandKokushiMusou { duplicate, t14, tsumo_or_ron: TsumoOrRon::Ron };
			let actual = std::string::ToString::to_string(&hand);
			assert_eq!(actual, std::format!("{expected_juusanmen} ron"));
		}
	}

	#[test]
	fn scorable_hand_meld_display() {
		for (m, expected) in [
			(make_scorable_hand!(@meld { ankan 1m 1m 1m 1m }), "{ ankan 1m 1m 1m 1m }"),
			(make_scorable_hand!(@meld { minkan 1m 1m 1m 1m }), "{ minkan 1m 1m 1m 1m }"),
			(make_scorable_hand!(@meld { ankou 1m 1m 1m }), "{ ankou 1m 1m 1m }"),
			(make_scorable_hand!(@meld { minkou 1m 1m 1m }), "{ minkou 1m 1m 1m }"),
			(make_scorable_hand!(@meld { anjun 1m 2m 3m }), "{ anjun 1m 2m 3m }"),
			(make_scorable_hand!(@meld { minjun 1m 2m 3m }), "{ minjun 1m 2m 3m }"),
		] {
			let actual = std::string::ToString::to_string(&m);
			assert_eq!(actual, expected);
		}
	}

	#[test]
	fn scorable_hand_fourth_meld_display() {
		for (m, expected) in [
			(make_scorable_hand!(@meldr4 { ankan 1m 1m 1m 1m }), "{ ankan 1m 1m 1m 1m }"),
			(make_scorable_hand!(@meldr4 { minkan 1m 1m 1m 1m }), "{ minkan 1m 1m 1m 1m }"),
			(make_scorable_hand!(@meldr4 { ankou 1m 1m 1m }), "{ ankou 1m 1m 1m }"),
			(make_scorable_hand!(@meldr4 { ankou 1m 1m 1m shanpon }), "{ ankou 1m 1m 1m shanpon }"),
			(make_scorable_hand!(@meldr4 { minkou 1m 1m 1m }), "{ minkou 1m 1m 1m }"),
			(make_scorable_hand!(@meldr4 { minkou 1m 1m 1m shanpon }), "{ minkou 1m 1m 1m shanpon }"),
			(make_scorable_hand!(@meldr4 { anjun 1m 2m 3m }), "{ anjun 1m 2m 3m }"),
			(make_scorable_hand!(@meldr4 { anjun 1m 2m 3m kanchan }), "{ anjun 1m 2m 3m kanchan }"),
			(make_scorable_hand!(@meldr4 { anjun 1m 2m 3m penchan }), "{ anjun 1m 2m 3m penchan }"),
			(make_scorable_hand!(@meldr4 { anjun 1m 2m 3m ryanmen_low }), "{ anjun 1m 2m 3m ryanmen_low }"),
			(make_scorable_hand!(@meldr4 { anjun 1m 2m 3m ryanmen_high }), "{ anjun 1m 2m 3m ryanmen_high }"),
			(make_scorable_hand!(@meldr4 { minjun 1m 2m 3m }), "{ minjun 1m 2m 3m }"),
			(make_scorable_hand!(@meldr4 { minjun 1m 2m 3m kanchan }), "{ minjun 1m 2m 3m kanchan }"),
			(make_scorable_hand!(@meldr4 { minjun 1m 2m 3m penchan }), "{ minjun 1m 2m 3m penchan }"),
			(make_scorable_hand!(@meldr4 { minjun 1m 2m 3m ryanmen_low }), "{ minjun 1m 2m 3m ryanmen_low }"),
			(make_scorable_hand!(@meldr4 { minjun 1m 2m 3m ryanmen_high }), "{ minjun 1m 2m 3m ryanmen_high }"),
		] {
			let actual = std::string::ToString::to_string(&m);
			assert_eq!(actual, expected);
		}
	}
}
