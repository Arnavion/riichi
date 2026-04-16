use crate::{
	CmpIgnoreRed,
	DragonTile,
	HandMeld,
	Number, NumberSuit, NumberTileClassified, NumberTile,
	ShunLowNumber, ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile, Tile34Set, TsumoOrRon,
	WindTile,
};

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
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
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
/// This type expects that its variant data is consistent. This means:
///
/// - The array of of [`ScorableHandMeld`]s is in sorted order.
///
/// - All [`ScorableHandMeld`]s, the [`ScorableHandFourthMeld`]s and the [`ScorableHandPair`] are themselves consistent.
///   See their docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
// Enforce field order.
//
// `m1`, `m2` and `m3` are `repr(align(2))`, m4 is `repr(align(4))`, and `pair` is `repr(align(1))`.
// Without `repr(C)`, rustc lays them out as `m4:m1:m2:m3:pair`, which has the diadvantage that `m4` comes before the other `m*`s.
// This means any operation that wants to vectorize over all the melds ignoring the fourth meld's wait, like operations on `self.melds_()`,
// must do reads at offsets of 0, 4, 6, 8 which does not stride.
//
// By using `repr(C)` we can force the fields to be laid out in order so that `self.melds_()` can interpret the 2..10 bytes of `self` as `[ScorableHandMeld; 4]`.
// Also `self.melds_and_pair()` can interpret the 0..10 bytes as `[ScorableHandMeld; 5]`.
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
/// This type expects that its variant data is consistent. This means:
///
/// - All [`ScorableHandPair`]s are themselves consistent. See its docs for details.
///
/// - Mo two pairs have the same tiles.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ScorableHandChiitoi(pub [ScorableHandPair; 7]);

/// Kokushi musou hand shape containing one of each terminal and honor tile and one duplicate.
///
/// This type expects that its variant data is consistent. This means that the `duplicate` tile is valid for a kokushi musou hand.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct ScorableHandKokushiMusou {
	pub duplicate: Tile,
	pub was_juusanmen_wait: bool,
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(C, align(2))] // See comment in `ScorableHandMeld::cmp`.
pub struct ScorableHandRegularPair {
	pub tag: ScorableHandRegularPairTag,
	pub inner: ScorableHandPair,
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ScorableHandRegularPairTag {
	// Same tag as `ScorableHandMeld::Ankou`, so that a pair can pretend to be an ankou for algorithms that benefit from it (`fn chanta_routou()`).
	//
	// It also makes `ScorableHandRegular` store its discriminant in this field instead of any other. If this tag was not there,
	// the discriminant would be stored in `ScorableHandRegular::m1`, which would push `ScorableHandChiitoi` and `ScorableHandKokushiMusou` variant data
	// to offset 3 instead of offset 1.
	Pair = 2,
}

/// A single meld inside a [`ScorableHand`].
///
/// Only the lowest tile is held, since that is sufficient to uniquely determine the whole meld.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Clone, Copy)]
#[repr(C, u8, align(2))] // See comment in `ScorableHandMeldSortCriteria::new`.
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
/// Only the lowest tile in the meld is held, since that is sufficient to uniquely determine the whole meld.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Clone, Copy)]
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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum KanWait {
	Tanki = 0,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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

/// A single pair inside a [`ScorableHand`].
///
/// Only one of the tiles in the pair is held, since that is sufficient to uniquely determine the whole pair.
///
/// If the pair is of one `Five` and one `FiveRed` tile, then the `FiveRed` is held.
/// Thus if the held tile is a `FiveRed`, the other tile in the pair is assumed to be a `Five`.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Clone, Copy, Eq)]
#[repr(transparent)]
pub struct ScorableHandPair(pub Tile);

assert_size_of!(ScorableHand, 12);
assert_size_of!(ScorableHandRegular, 12);
assert_size_of!(ScorableHandChiitoi, 7);
assert_size_of!(ScorableHandKokushiMusou, 2);
assert_size_of!(ScorableHandMeld, 2);
assert_size_of!(ScorableHandFourthMeld, 4);
assert_size_of!(ScorableHandPair, 1);

impl ScorableHand {
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

impl ScorableHandRegular {
	pub fn new(ma: ScorableHandMeld, mb: ScorableHandMeld, mc: ScorableHandMeld, md: ScorableHandFourthMeld, pair: ScorableHandPair) -> Self {
		let (m1, m2, m3, m4) =
			if let Some(md) = md.to_tanki() {
				let mut ms = [ma, mb, mc, md];
				SortingNetwork::sort(&mut ms);
				let [m1, m2, m3, m4] = ms;
				(m1, m2, m3, m4.into())
			}
			else {
				let mut m123 = [ma, mb, mc];
				SortingNetwork::sort(&mut m123);
				let [m1, m2, m3] = m123;
				(m1, m2, m3, md)
			};
		Self { m1, m2, m3, m4, pair: ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Pair, inner: pair } }
	}

	fn for_each_tile(&self, mut f: impl FnMut(Tile)) {
		for m in self.melds() {
			m.for_each_tile(&mut f);
		}
		self.pair.inner.for_each_tile(f);
	}

	const fn melds(&self) -> &[ScorableHandMeld; 4] {
		unsafe { &*<*const ScorableHandMeld>::cast::<[ScorableHandMeld; 4]>(&raw const self.m1) }
	}

	const fn melds_types(&self) -> [u8; 4] {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10]>(self) };
		[this[2], this[4], this[6], this[8]]
	}

	const fn melds_tiles(&self) -> [u8; 4] {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10]>(self) };
		[this[3], this[5], this[7], this[9]]
	}

	const fn melds_and_pair(&self) -> &[ScorableHandMeld; 5] {
		unsafe { &*<*const Self>::cast::<[ScorableHandMeld; 5]>(self) }
	}

	const fn melds_and_pair_tiles(&self) -> [u8; 5] {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10]>(self) };
		[this[1], this[3], this[5], this[7], this[9]]
	}

	pub(crate) fn is_menzen(&self) -> bool {
		let Self { m1, m2, m3, m4, .. } = self;
		// Note that `m4.is_menzen()` is *not* the same as `ScorableHandMeld::from(*m4).is_menzen()`.
		// If `m4` was completed by ron, the latter returns `true` because the hand is still closed,
		// but the former returns `false` because the meld itself is open.
		m1.is_menzen() & m2.is_menzen() & m3.is_menzen() & m4.is_menzen()
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
		let Self { m1, m2, m3, m4, pair } = self;
		let [m1_d, _] = m1.parts();
		let [m2_d, _] = m2.parts();
		let [m3_d, _] = m3.parts();
		let [_, _, m4_w] = m4.parts();
		#[expect(clippy::needless_bitwise_bool)]
		{
			// Self::Anjun == 4
			(m1_d == 4) & (m2_d == 4) & (m3_d == 4) &
				// Don't need to check `m4_d == Anjun || m4_d == Minjun`, because the `ShunWait::Ryanmen*` values are not used by any `KanWait` or `KouWait` vriants.
				(m4_w == ShunWait::RyanmenLow as u8 || m4_w == ShunWait::RyanmenHigh as u8) &
				(pair.inner.num_yakuhai(round_wind, seat_wind) == 0)
		}
	}

	pub(crate) fn num_peikou(&self) -> usize {
		let Self { m1, m2, m3, m4, .. } = self;

		// `[[2, 2, 2, 2, 2, 2, 2, 0, 0]; 3]` packed into two bits per element.
		let mut counts = 0x2AAA0AAA82AAA_u64;
		// Micro-optimization: Use a flag instead of returning early to generate branchless code.
		let mut is_valid = self.is_menzen();
		let mut result = 0;

		// Micro-optimization: `match` on `m*` generates verbose code, so work with the integer parts directly.

		let [m1_d, m1_t] = m1.parts();
		let [m2_d, m2_t] = m2.parts();
		let [m3_d, m3_t] = m3.parts();
		let [m4_d, m4_t, _] = m4.parts();

		{
			let consider_m1 = u64::from(m1_d == 4); // Anjun
			let offset = m1_t & !0b1;
			counts -= consider_m1.wrapping_shl(offset.into());
		}

		{
			let consider_m2 = u64::from(m2_d == 4); // Anjun
			let offset = m2_t & !0b1;
			let count = counts.wrapping_shr(offset.into()) & 0b11;
			result += (consider_m2 & count) as usize;
			counts -= consider_m2.wrapping_shl(offset.into());
		}

		{
			let consider_m3 = u64::from(m3_d == 4); // Anjun
			let offset = m3_t & !0b1;
			let count = counts.wrapping_shr(offset.into()) & 0b11;
			is_valid &= consider_m3 != 1 || count != 0; // Sanankou or suuankou
			result += (consider_m3 & count) as usize;
			counts -= consider_m3.wrapping_shl(offset.into());
		}

		{
			let consider_m4 = u64::from(m4_d >= 4); // Anjun, or minjun non-tanki (since minjun tanki already caused `is_valid = self.is_menzen()` above to be `false`.)
			let offset = m4_t & !0b1;
			let count = counts.wrapping_shr(offset.into()) & 0b11;
			is_valid &= consider_m4 != 1 || count != 0; // Sanankou or suuankou
			result += (consider_m4 & count) as usize;
		}

		if is_valid { result } else { 0 }
	}

	pub(crate) fn chanta_routou(&self) -> ChantaRoutou {
		cfg_select! {
			all(target_arch = "riscv64", target_feature = "v") => {
				const SHUN_TERMINALS: Tile34Set = t34set! { 1m, 7m, 1p, 7p, 1s, 7s };
				const KOU_KAN_TERMINALS: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };
				const KOU_KAN_HONORS: Tile34Set = t34set! { E, S, W, G, N, Wh, G, R };

				let result: u8;
				unsafe {
					core::arch::asm!(
						// let chanta_routou_other /* : v12:v12 */ = ChantaRoutou::other();
						"vsetivli zero, 5, e8, m1, ta, ma",
						"vmv.v.i v12, {chanta_routou_other}",

						// let ds: v4:v4;
						// let ts: v5:v5;
						"vlseg2e8.v v4, ({ms})",

						// let ts /* : v5:v5 */ = ts >> 1;
						"vsrl.vi v5, v5, 1",
						// let ts /* : v16:v19 */ = ts.cast::<u64>();
						"vsetvli zero, zero, e64, m4, ta, ma",
						"vzext.vf8 v16, v5",
						// let masks /* : v8:v11 */ = 1 << ts;
						"vmv.v.i v8, 1",
						"vsll.vv v8, v8, v16",

						// let shun_terminals_contains_t /* : v0:v0 */ = (masks & SHUN_TERMINALS) != 0;
						"vand.vx v16, v8, {shun_terminals}",
						"vmsne.vi v0, v16, 0",
						// let temp1 /* : v13:v13 */ = select(shun_terminals_contains_t, chanta_routou_has_terminals, chanta_routou_other);
						"vsetvli zero, zero, e8, m1, ta, ma",
						"vmerge.vim v13, v12, {chanta_routou_has_terminals}, v0",

						// let kou_kan_honors_contains_t /* : v0:v0 */ = (masks & KOU_KAN_HONORS) != 0;
						"vsetvli zero, zero, e64, m4, ta, ma",
						"vand.vx v16, v8, {kou_kan_honors}",
						"vmsne.vi v0, v16, 0",
						// let temp2 /* : v12:v12 */ = select(kou_kan_honors_contains_t, chanta_routou_all_honors, chanta_routou_other);
						"vsetvli zero, zero, e8, m1, ta, ma",
						"vmerge.vim v12, v12, {chanta_routou_all_honors}, v0",

						// let kou_kan_terminals_contains_t /* : v0:v0 */ = (masks & KOU_KAN_TERMINALS) != 0;
						"vsetvli zero, zero, e64, m4, ta, ma",
						"vand.vx v16, v8, {kou_kan_terminals}",
						"vmsne.vi v0, v16, 0",
						// let temp3 /* : v12:v12 */ = select(kou_kan_terminals_contains_t, chanta_routou_all_terminals, temp2);
						"vsetvli zero, zero, e8, m1, ta, ma",
						"vmerge.vim v12, v12, {chanta_routou_all_terminals}, v0",

						// let is_shun /* : v0:v0 */ = ds >= 4;
						"vmsgeu.vi v0, v4, 4",
						// let chanta_routous /* : v8:v8 */ = select(is_shun, temp1, temp3);
						"vmerge.vvm v8, v12, v13, v0",

						// let result = chanta_routous.reduce_or();
						"vredor.vs v9, v8, v8",
						"vmv.x.s {result}, v9",

						ms = in(reg) self,
						shun_terminals = in(reg) SHUN_TERMINALS.present,
						kou_kan_terminals = in(reg) KOU_KAN_TERMINALS.present,
						kou_kan_honors = in(reg) KOU_KAN_HONORS.present,
						chanta_routou_has_terminals = const ChantaRoutou::has_terminals().0,
						chanta_routou_all_terminals = const ChantaRoutou::all_terminals().0,
						chanta_routou_all_honors = const ChantaRoutou::all_honors().0,
						chanta_routou_other = const ChantaRoutou::other().0,
						result = lateout(reg) result,
						out("v0") _,
						out("v4") _,
						out("v5") _,
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
						options(nostack),
					);
				}
				ChantaRoutou(result)
			},

			_ => {
				fn chanta_routou(m: ScorableHandMeld) -> ChantaRoutou {
					const SHUN_TERMINALS: Tile34Set = t34set! { 1m, 7m, 1p, 7p, 1s, 7s };
					const KOU_KAN_TERMINALS: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };
					const KOU_KAN_HONORS: Tile34Set = t34set! { E, S, W, G, N, Wh, G, R };

					let (t, is_shun) = match m {
						ScorableHandMeld::Ankan(t) |
						ScorableHandMeld::Minkan(t) |
						ScorableHandMeld::Ankou(t) |
						ScorableHandMeld::Minkou(t) => (t, false),
						ScorableHandMeld::Anjun(t) |
						ScorableHandMeld::Minjun(t) => (t.remove_red().into(), true),
					};

					// Micro-optimization: `if is_shun { ... } else { ... } generates a branch on `discriminant(&self) & 0b100 == 0`.
					// Using `select_unpredictable` generate branchless selects (with that same condition) instead.
					core::hint::select_unpredictable(
						is_shun,
						core::hint::select_unpredictable(
							SHUN_TERMINALS.contains(t),
							ChantaRoutou::has_terminals(),
							ChantaRoutou::other()
						),
						core::hint::select_unpredictable(
							KOU_KAN_TERMINALS.contains(t),
							ChantaRoutou::all_terminals(),
							core::hint::select_unpredictable(
								KOU_KAN_HONORS.contains(t),
								ChantaRoutou::all_honors(),
								ChantaRoutou::other(),
							),
						),
					)
				}

				self.melds_and_pair().iter().fold(ChantaRoutou(0), |acc, &m| acc | chanta_routou(m))
			},
		}
	}

	pub(crate) fn num_wind_yakuhai(&self, wind: WindTile, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		// Micro-optimization: `.contains()` generates a branch for each element test.
		#[expect(clippy::manual_contains)]
		let is_wind = self.melds_tiles().iter().any(|&t| t == wind as u8);
		let num_round_winds = u8::from(wind == round_wind);
		let num_seat_winds = u8::from(wind == seat_wind);
		core::hint::select_unpredictable(is_wind, num_round_winds + num_seat_winds, 0)
	}

	pub(crate) fn is_dragon_yakuhai(&self, dragon: DragonTile) -> bool {
		// Micro-optimization: `.contains()` generates a branch for each element test.
		#[expect(clippy::manual_contains)]
		self.melds_tiles().iter().any(|&t| t == dragon as u8)
	}

	pub(crate) fn is_sanshoku_doujun(&self) -> bool {
		self.is_sanshoku(|m| {
			let (ScorableHandMeld::Anjun(t) | ScorableHandMeld::Minjun(t)) = m else { return None; };
			Some(t.remove_red().into())
		})
	}

	pub(crate) fn is_ittsuu(&self) -> bool {
		const MASK: u32 = 0b001001001_u32;

		let counts =
			self.melds().iter()
			.fold(0b000000000_000000000_000000000_u32, |counts, m| {
				let [d, t] = m.parts();
				counts | u32::from(d >= 4).wrapping_shl((t >> 1).into())
			});

		[counts, counts >> 9, counts >> 18].iter().any(|&counts| counts & MASK == MASK)
	}

	pub(crate) fn is_toitoi(&self) -> bool {
		self.melds_types().iter().all(|&d| d <= 3)
	}

	pub(crate) fn num_ankou(&self) -> NumAnkou {
		let count = self.melds_types().iter().filter(|&&d| d & 0b101 == 0b000).count();
		let result = 2 - u8::from(count <= 3) - u8::from(count <= 2);
		let result = result << u8::from((count == 4) & self.m4.is_tanki());
		NumAnkou(result)
	}

	pub(crate) fn is_sanshoku_doukou(&self) -> bool {
		self.is_sanshoku(|m| {
			let (
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t)
			) = m else { return None; };
			let t = NumberTile::try_from(*t).ok()?;
			Some(t)
		})
	}

	pub(crate) fn num_kantsu(&self) -> NumKantsu {
		let count =
			self.melds_types().iter()
			.filter(|&&d| d <= 1)
			.count();
		#[expect(clippy::cast_possible_truncation)]
		NumKantsu(count as u8)
	}

	pub(crate) fn suushii_sangen(&self) -> SuushiiSangen {
		let (num_wind_melds, num_dragon_melds) =
			self.melds_tiles().iter()
			.fold((0, 0), |(num_wind_melds, num_dragon_melds), &t| {
				// SAFETY: If `t` is in the range of wind or dragon tiles, it must have been from the `*kan` or `*kou` variants,
				// in which case it was a valid `Tile` and thus meets the safety requirement of `try_from_raw`.
				let num_wind_melds = num_wind_melds + u8::from((unsafe { WindTile::try_from_raw(t) }).is_ok());
				let num_dragon_melds = num_dragon_melds + u8::from((unsafe { DragonTile::try_from_raw(t) }).is_ok());
				(num_wind_melds, num_dragon_melds)
			});
		let pair = {
			let t = self.pair.inner.0 as u8;
			let pair = 2 - u8::from(t < t!(Wh) as u8) - u8::from(t < t!(E) as u8);
			unsafe { core::mem::transmute::<u8, WindOrDragon>(pair) }
		};
		SuushiiSangen { num_wind_melds, num_dragon_melds, pair }
	}

	pub(crate) fn honchinitsu(&self) -> Honchinitsu {
		Honchinitsu::new(self.melds_and_pair_tiles())
	}

	pub(crate) fn is_ryuuiisou(&self) -> bool {
		// Note: Having G is not required.

		const KOU_KAN_PAIR_VALID: Tile34Set = t34set! { 2s, 3s, 4s, 6s, 8s, G };
		const SHUN_VALID: Tile34Set = t34set! { 2s };

		self.melds_and_pair().iter()
			.fold(true, |is_valid, &m| {
				let (set, t) = match m {
					ScorableHandMeld::Ankan(t) |
					ScorableHandMeld::Minkan(t) |
					ScorableHandMeld::Ankou(t) |
					ScorableHandMeld::Minkou(t) => (&KOU_KAN_PAIR_VALID, t),
					ScorableHandMeld::Anjun(t) |
					ScorableHandMeld::Minjun(t) => (&SHUN_VALID, Tile::from(t.remove_red())),
				};
				is_valid & set.contains(t)
			})
	}

	pub(crate) fn num_chuuren_poutou(&self) -> u8 {
		fn meld_tiles(m: ScorableHandMeld, suit_expected: &mut Option<NumberSuit>) -> Option<(Number, Number, Number)> {
			let n1;
			let n2;
			let n3;

			match m {
				ScorableHandMeld::Ankan(_) |
				ScorableHandMeld::Minkan(_) |
				ScorableHandMeld::Minkou(_) |
				ScorableHandMeld::Minjun(_) => return None,

				ScorableHandMeld::Ankou(t) => {
					let t = NumberTile::try_from(t).ok()?;
					let number =
						if let Some(suit_expected) = *suit_expected {
							t.is_in_suit(suit_expected)?
						}
						else {
							let NumberTileClassified { suit, number } = t.into();
							*suit_expected = Some(suit);
							number
						};
					n1 = number;
					n2 = number;
					n3 = number;
				},

				ScorableHandMeld::Anjun(t) => {
					let t = t.remove_red();
					let number =
						if let Some(suit_expected) = *suit_expected {
							t.is_in_suit(suit_expected)?
						}
						else {
							let NumberTileClassified { suit, number } = NumberTile::from(t).into();
							*suit_expected = Some(suit);
							unsafe { core::mem::transmute::<u8, ShunLowNumber>(number as u8) }
						};
					n1 = number.into();
					(n2, n3) = number.shun_rest();
				},
			}

			Some((n1, n2, n3))
		}

		fn fourth_meld_and_pair_old_and_new_tiles(m4: ScorableHandFourthMeld, pair: ScorableHandPair, suit_expected: NumberSuit) -> Option<(Number, Number, Number, Number, Number)> {
			let old1;
			let old2;
			let old3;
			let old4;
			let new;

			// Micro-optimization: `match m4 { ... }` generates a multi-level jump table. `match m4.dw()` generates a simple single-level one.
			let [_, m4_t, _] = m4.parts();
			match m4.dw() {
				// Ankan / minkan / minkou tanki / minjun tanki
				0 | 1 | 3 | 5 => return None,

				// Ankou tanki
				2 => {
					let t = unsafe { core::mem::transmute::<u8, Tile>(m4_t) };

					{
						let t = NumberTile::try_from(t).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old1 = number;
						old2 = number;
						old3 = number;
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old4 = number;
						new = number;
					}
				},

				// Anjun tanki
				4 => {
					let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(m4_t) };

					{
						let t = t.remove_red();
						let number = t.is_in_suit(suit_expected)?;
						old1 = number.into();
						(old2, old3) = number.shun_rest();
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old4 = number;
						new = number;
					}
				},

				// Ankou shanpon / minkou shanpon
				6 | 7 => {
					let t = unsafe { core::mem::transmute::<u8, Tile>(m4_t) };

					{
						let t = NumberTile::try_from(t).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old1 = number;
						old2 = number;
						new = number;
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old3 = number;
						old4 = number;
					}
				},

				// Anjun penchan / minjun penchan
				8 | 9 => {
					let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(m4_t) };

					{
						let t = t.remove_red();
						let number = t.is_in_suit(suit_expected)?;
						old1 = number.into();
						(new, old2) = number.shun_rest();
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old3 = number;
						old4 = number;
					}
				},

				// Anjun kanchan / minjun kanchan
				12 | 13 => {
					let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(m4_t) };

					{
						let t = t.remove_red();
						let number = t.is_in_suit(suit_expected)?;

						if Number::from(number).value() == 1 {
							old1 = number.into();
							(old2, new) = number.shun_rest();
						}
						else {
							(old1, old2) = number.shun_rest();
							new = number.into();
						}
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old3 = number;
						old4 = number;
					}
				},

				// Anjun ryanmen low / minjun ryanmen low
				16 | 17 => {
					let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(m4_t) };

					{
						let t = t.remove_red();
						let number = t.is_in_suit(suit_expected)?;
						(old1, old2) = number.shun_rest();
						new = number.into();
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old3 = number;
						old4 = number;
					}
				},

				// Anjun ryanmen high / minjun ryanmen high
				20 | 21 => {
					let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(m4_t) };

					{
						let t = t.remove_red();

						let number = t.is_in_suit(suit_expected)?;
						old1 = number.into();
						(old2, new) = number.shun_rest();
					}

					{
						let t = NumberTile::try_from(pair.0).ok()?;
						let number = t.is_in_suit(suit_expected)?;
						old3 = number;
						old4 = number;
					}
				},

				_ => unsafe { core::hint::unreachable_unchecked(); },
			}

			Some((old1, old2, old3, old4, new))
		}

		const fn sub(counts: &mut u32, n: Number) {
			let offset = (n.value() - 1) * 2;
			let count = (*counts >> offset) & 0b11;
			if count > 0 {
				*counts -= 0b1 << offset;
			}
		}

		let Self { m1, m2, m3, m4, pair } = self;

		// [3, 1, 1, 1, 1, 1, 1, 1, 3] packed into two bits per element.
		let mut counts = 0b11_01_01_01_01_01_01_01_11_u32;
		let mut suit_expected = None;

		for m in [m1, m2, m3] {
			let Some((n1, n2, n3)) = meld_tiles(*m, &mut suit_expected) else { return 0; };
			sub(&mut counts, n1);
			sub(&mut counts, n2);
			sub(&mut counts, n3);
		}

		let suit_expected = unsafe { suit_expected.unwrap_unchecked() };

		let Some((old1, old2, old3, old4, new)) = fourth_meld_and_pair_old_and_new_tiles(*m4, pair.inner, suit_expected) else { return 0; };
		sub(&mut counts, old1);
		sub(&mut counts, old2);
		sub(&mut counts, old3);
		sub(&mut counts, old4);

		let counts_without_new_tile = counts;

		sub(&mut counts, new);

		match (counts, counts_without_new_tile) {
			(0, 0) => 2,
			(0, _) => 1,
			_ => 0,
		}
	}

	fn is_sanshoku(&self, f: impl FnMut(&ScorableHandMeld) -> Option<NumberTile>) -> bool {
		const MASK: u64 = 0b000000001_000000001_000000001_000000001_000000001_u64;

		let mut counts = 0b000000000_000000000_000000000_u32;

		self.melds().iter()
			.filter_map(f)
			.fold(false, |result, t| {
				let offset = (t as u8) >> 1;

				counts |= 0b1 << offset;

				#[expect(clippy::cast_possible_truncation)]
				let mask = ((MASK << offset) >> 18) as u32;
				#[expect(clippy::needless_bitwise_bool)]
				{
					result | (counts & mask == mask & 0x7FFFFFF)
				}
			})
	}
}

impl core::fmt::Debug for ScorableHandRegular {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandRegular {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self { m1, m2, m3, m4, pair } = self;
		write!(f, "{m1} {m2} {m3} {m4} {}", pair.inner)
	}
}

impl ScorableHandChiitoi {
	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		for p in self.0 {
			p.for_each_tile(&mut f);
		}
	}

	pub(crate) fn chanta_routou(self) -> ChantaRoutou {
		cfg_select! {
			all(target_arch = "riscv64", target_feature = "v") => {
				const TERMINALS: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };
				const HONORS: Tile34Set = t34set! { E, S, W, G, N, Wh, G, R };

				let result: u8;
				unsafe {
					core::arch::asm!(
						// let chanta_routou_other: v12:v12 = ChantaRoutou::other();
						"vsetivli zero, 7, e8, m1, ta, ma",
						"vmv.v.i v12, {chanta_routou_other}",

						// let ts: v5:v5;
						"vle8.v v5, ({ts})",

						// let ts: v5:v5 = ts >> 1;
						"vsrl.vi v5, v5, 1",
						// let ts: v16:v19 = ts.cast::<u64>();
						"vsetvli zero, zero, e64, m4, ta, ma",
						"vzext.vf8 v16, v5",
						// let masks: v8:v11 = 1 << ts;
						"vmv.v.i v8, 1",
						"vsll.vv v8, v8, v16",

						// let honors_contains_t: v0:v0 = (masks & HONORS) != 0;
						"vand.vx v16, v8, {honors}",
						"vmsne.vi v0, v16, 0",
						// let temp2: v12:v12 = select(honors_contains_t, chanta_routou_all_honors, chanta_routou_other);
						"vsetvli zero, zero, e8, m1, ta, ma",
						"vmerge.vim v12, v12, {chanta_routou_all_honors}, v0",

						// let terminals_contains_t: v0:v0 = (masks & TERMINALS) != 0;
						"vsetvli zero, zero, e64, m4, ta, ma",
						"vand.vx v16, v8, {terminals}",
						"vmsne.vi v0, v16, 0",
						// let chanta_routous: v12:v12 = select(terminals_contains_t, chanta_routou_all_terminals, temp2);
						"vsetvli zero, zero, e8, m1, ta, ma",
						"vmerge.vim v12, v12, {chanta_routou_all_terminals}, v0",

						// let result = chanta_routous.reduce_or();
						"vredor.vs v9, v12, v12",
						"vmv.x.s {result}, v9",

						ts = in(reg) &raw const self.0,
						terminals = in(reg) TERMINALS.present,
						honors = in(reg) HONORS.present,
						chanta_routou_all_terminals = const ChantaRoutou::all_terminals().0,
						chanta_routou_all_honors = const ChantaRoutou::all_honors().0,
						chanta_routou_other = const ChantaRoutou::other().0,
						result = lateout(reg) result,
						out("v0") _,
						out("v5") _,
						out("v8") _,
						out("v9") _,
						out("v10") _,
						out("v11") _,
						out("v12") _,
						out("v16") _,
						out("v17") _,
						out("v18") _,
						out("v19") _,
						options(nostack),
					);
				}
				ChantaRoutou(result)
			},

			_ => {
				const fn chanta_routou(p: ScorableHandPair) -> ChantaRoutou {
					const TERMINALS: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };
					const HONORS: Tile34Set = t34set! { E, S, W, G, N, Wh, G, R };

					if TERMINALS.contains(p.0) {
						ChantaRoutou::all_terminals()
					}
					else if HONORS.contains(p.0) {
						ChantaRoutou::all_honors()
					}
					else {
						ChantaRoutou::other()
					}
				}

				self.0.iter().fold(ChantaRoutou(0), |acc, &p| acc | chanta_routou(p))
			},
		}
	}

	pub(crate) fn honchinitsu(self) -> Honchinitsu {
		Honchinitsu::new(self.0.iter().map(|ScorableHandPair(t)| *t as u8))
	}
}

impl core::fmt::Debug for ScorableHandChiitoi {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandChiitoi {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self([p1, p2, p3, p4, p5, p6, p7]) = self;
		write!(f, "{p1} {p2} {p3} {p4} {p5} {p6} {p7}")
	}
}

impl ScorableHandKokushiMusou {
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
		// Micro-optimization: `f.write_str(match self.duplicate { ... })` causes each string to be stored as a separate constant
		// and generates a jump table to load the corresponding constant and length.
		// Making a single string and indexing it manually replaces the jump table with a LUT, and calculating the length using arithmetic avoids a second LUT.
		const STRINGS: &str = "\
			1m 1m 9m 1p 9p 1s 9s E S W N Wh G R\
			1m 9m 9m 1p 9p 1s 9s E S W N Wh G R\
			1m 9m 1p 1p 9p 1s 9s E S W N Wh G R\
			1m 9m 1p 9p 9p 1s 9s E S W N Wh G R\
			1m 9m 1p 9p 1s 1s 9s E S W N Wh G R\
			1m 9m 1p 9p 1s 9s 9s E S W N Wh G R\
			1m 9m 1p 9p 1s 9s E E S W N Wh G R\
			1m 9m 1p 9p 1s 9s E S S W N Wh G R\
			1m 9m 1p 9p 1s 9s E S W W N Wh G R\
			1m 9m 1p 9p 1s 9s E S W N N Wh G R\
			1m 9m 1p 9p 1s 9s E S W N Wh Wh G R\
			1m 9m 1p 9p 1s 9s E S W N Wh G G R\
			1m 9m 1p 9p 1s 9s E S W N Wh G R R\
		";
		// Micro-optimization: It would be nice to make this `[MaybeUninit<u16>; 34]` and use `uninit()` for the unreachable elements,
		// but then rustc generates a test that `offset` points to an initialized element. So we set the unreachable elements to zeros instead.
		const STARTS: [u16; 34] = {
			let mut result = [0; 34];

			let start = 0;
			result[t!(1m) as usize >> 1] = start;

			let start = start + 35;
			result[t!(9m) as usize >> 1] = start;

			let start = start + 35;
			result[t!(1p) as usize >> 1] = start;

			let start = start + 35;
			result[t!(9p) as usize >> 1] = start;

			let start = start + 35;
			result[t!(1s) as usize >> 1] = start;

			let start = start + 35;
			result[t!(9s) as usize >> 1] = start;

			let start = start + 35;
			result[t!(E) as usize >> 1] = start;

			let start = start + 34;
			result[t!(S) as usize >> 1] = start;

			let start = start + 34;
			result[t!(W) as usize >> 1] = start;

			let start = start + 34;
			result[t!(N) as usize >> 1] = start;

			let start = start + 34;
			result[t!(Wh) as usize >> 1] = start;

			let start = start + 35;
			result[t!(G) as usize >> 1] = start;

			let start = start + 34;
			result[t!(R) as usize >> 1] = start;

			result
		};

		let offset = self.duplicate as u8 >> 1;
		let start = usize::from(STARTS[usize::from(offset)]);
		let len = 34 + usize::from(self.duplicate < t!(E)) + usize::from(self.duplicate == t!(Wh));
		let end = start + len;
		// Micro-optimization: rustc does not notice that all the ranges are valid and emits a str slice check, so assert that they are valid.
		unsafe { core::hint::assert_unchecked(end <= STRINGS.len()); }
		let s = &STRINGS[start..end];
		f.write_str(s)?;

		if self.was_juusanmen_wait { f.write_str(" juusanmen")?; }

		Ok(())
	}
}

impl ScorableHandMeld {
	/// Construct a `ScorableHandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Ankan(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub unsafe fn ankan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let t = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Ankan(t)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let t = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Minkan(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub unsafe fn minkan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let t = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Minkan(t)
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankou`](Self::Ankou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub fn ankou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Ankou(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankou`](Self::Ankou) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn ankou_unchecked(t1: Tile, t2: Tile, t3: Tile) -> Self {
		let t = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Ankou(t)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Minkou(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn minkou_unchecked(t1: Tile, t2: Tile, t3: Tile) -> Self {
		let t = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Minkou(t)
	}

	/// Construct a `ScorableHandMeld` of kind [`Anjun`](Self::Anjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn anjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Anjun(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Anjun`](Self::Anjun) using the given tiles.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn anjun_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::Anjun(t)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Minjun(t))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minjun`](Self::Minjun) using the given tiles.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn minjun_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::Minjun(t)
	}

	/// `[d, t]`
	const fn parts(self) -> [u8; 2] {
		let m = unsafe { core::mem::transmute::<Self, [core::mem::MaybeUninit<u8>; core::mem::size_of::<Self>()]>(self) };
		// TODO(rustup): Use `MaybeUninit::array_assume_init` when that is stabilized.
		let m = unsafe { core::mem::transmute::<[core::mem::MaybeUninit<u8>; 2], [u8; 2]>(m) };
		// Remove bounds check in callers that use `d` to index an array.
		unsafe { core::hint::assert_unchecked(m[0] <= 5); }
		unsafe { core::hint::assert_unchecked(m[1] <= t!(R) as u8); }
		m
	}

	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		match self {
			Self::Ankan(t1) |
			Self::Minkan(t1) => {
				let t_rest = t1.remove_red();
				f(t_rest);
				f(t_rest);
				f(t_rest);
				f(t1);
			},

			Self::Ankou(t1) |
			Self::Minkou(t1) => {
				let t_rest = t1.remove_red();
				f(t_rest);
				f(t_rest);
				f(t1);
			},

			Self::Anjun(t) |
			Self::Minjun(t) => {
				let (t1, t2, t3) = t.shun();
				f(t1.into());
				f(t2.into());
				f(t3.into());
			}
		}
	}

	const fn is_menzen(self) -> bool {
		match self {
			Self::Ankan(_) |
			Self::Ankou(_) |
			Self::Anjun(_)
				=> true,
			Self::Minkan(_) |
			Self::Minkou(_) |
			Self::Minjun(_)
				=> false,
		}
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

		let mut is_ok = true;
		self.for_each_tile(|t| { is_ok = is_ok && write!(f, "{t} ").is_ok(); });

		if is_ok { f.write_str("}") } else { Err(core::fmt::Error) }
	}
}

impl From<HandMeld> for ScorableHandMeld {
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
impl From<ScorableHandFourthMeld> for ScorableHandMeld {
	fn from(meld: ScorableHandFourthMeld) -> Self {
		*meld.as_ref()
	}
}

impl Eq for ScorableHandMeld {}

/// `ScorableHandMeld`s differing only in the presence of akadora are considered equal.
impl Ord for ScorableHandMeld {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		let sc = ScorableHandMeldSortCriteria::new(self);
		let sc_other = ScorableHandMeldSortCriteria::new(other);
		sc.cmp_ignore_red(&sc_other)
	}
}

/// `ScorableHandMeld`s differing only in the presence of akadora are considered equal.
impl PartialEq for ScorableHandMeld {
	fn eq(&self, other: &Self) -> bool {
		let sc = ScorableHandMeldSortCriteria::new(self);
		let sc_other = ScorableHandMeldSortCriteria::new(other);
		sc.eq_ignore_red(&sc_other)
	}
}

/// `ScorableHandMeld`s differing only in the presence of akadora are considered equal.
impl PartialOrd for ScorableHandMeld {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

// Micro-optimization: `arr.sort_unstable()` generates excessively verbose code as of Rust 1.91 and contemporary nightly,
// because the impl uses insertion sort for all array sizes between 2 and 20.
//
// Specifically, on both x86_64 and RV, the `sort_unstable` codegen ends up using stack space and has many branches,
// while this three-swap version fits entirely in registers, has no branches, and is shorter to boot (three / five `maxu; minu` pairs on RV).

impl SortingNetwork for [ScorableHandMeld; 3] {
	fn sort(&mut self) {
		for (i, j) in [(0, 2), (0, 1), (1, 2)] {
			let a = self[i];
			let b = self[j];
			let sc_i = ScorableHandMeldSortCriteria::new(&a);
			let sc_j = ScorableHandMeldSortCriteria::new(&b);
			if sc_i >= sc_j {
				self[i] = b;
				self[j] = a;
			}
		}
	}
}

impl SortingNetwork for [ScorableHandMeld; 4] {
	fn sort(&mut self) {
		for (i, j) in [(0, 2), (1, 3), (0, 1), (2, 3), (1, 2)] {
			let a = self[i];
			let b = self[j];
			let sc_i = ScorableHandMeldSortCriteria::new(&a);
			let sc_j = ScorableHandMeldSortCriteria::new(&b);
			if sc_i >= sc_j {
				self[i] = b;
				self[j] = a;
			}
		}
	}
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct ScorableHandMeldSortCriteria(u16);

impl ScorableHandMeldSortCriteria {
	// Taking `ScorableHandMeld` as clippy recommends makes it more complicated to use this fn point-free with `core::cmp::minmax_by_key()`.
	#[expect(clippy::trivially_copy_pass_by_ref)]
	pub(crate) const fn new(m: &ScorableHandMeld) -> Self {
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
		Self(u16::from_le_bytes(m.parts()))
	}
}

impl CmpIgnoreRed for ScorableHandMeldSortCriteria {
	fn cmp_ignore_red(&self, other: &Self) -> core::cmp::Ordering {
		// We want to treat `Red` and non-`Red`s the same so we set the LSB of each `Tile` field.
		// Masking it out would be clearer, but setting is equivalent and generates simpler code.
		let this = self.0 | (0b1 << 8);
		let other = other.0 | (0b1 << 8);
		this.cmp(&other)
	}

	fn eq_ignore_red(&self, other: &Self) -> bool {
		(self.0 ^ other.0) & !(0b1 << 8) == 0
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
	pub fn shanpon(t1: Tile, t2: Tile, t3: Tile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::kou(t, tsumo_or_ron, KouWait::Shanpon))
	}

	/// Construct a [`ScorableHandFourthMeld::Ankou`] or [`ScorableHandFourthMeld::Minkou`] with a [`KouWait::Shanpon`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn shanpon_unchecked(t1: Tile, t2: Tile, t3: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		let t = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::kou(t, tsumo_or_ron, KouWait::Shanpon)
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
	pub fn kanchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::Kanchan))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::Kanchan`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn kanchan_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::shun(t, tsumo_or_ron, ShunWait::Kanchan)
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::Penchan`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn penchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::Penchan))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::Penchan`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn penchan_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::shun(t, tsumo_or_ron, ShunWait::Penchan)
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::RyanmenLow`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn ryanmen_low(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::RyanmenLow))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::RyanmenLow`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn ryanmen_low_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::shun(t, tsumo_or_ron, ShunWait::RyanmenLow)
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::RyanmenHigh`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn ryanmen_high(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let t = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::shun(t, tsumo_or_ron, ShunWait::RyanmenHigh))
	}

	/// Construct a [`ScorableHandFourthMeld::Anjun`] or [`ScorableHandFourthMeld::Minjun`] with a [`ShunWait::RyanmenHigh`] wait using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn ryanmen_high_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let t = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::shun(t, tsumo_or_ron, ShunWait::RyanmenHigh)
	}

	pub(crate) fn to_tanki(self) -> Option<ScorableHandMeld> {
		self.is_tanki().then(|| self.into())
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
	///
	///  d | w | d + w * 4 | Meld
	/// ===+===+===========+=====================
	///  0 | 0 | 0         | Ankan
	///  1 | 0 | 1         | Minkan
	///  2 | 0 | 2         | Ankou tanki
	///  3 | 0 | 3         | Minkou tanki
	///  4 | 0 | 4         | Anjun tanki
	///  5 | 0 | 5         | Minjun tanki
	/// ===+===+===========+=====================
	///  2 | 1 | 6         | Ankou shanpon
	///  3 | 1 | 7         | Minkou shanpon
	/// ===+===+===========+=====================
	///  4 | 1 | 8         | Anjun penchan
	///  5 | 1 | 9         | Minjun penchan
	/// ===+===+===========+=====================
	///  4 | 2 | 12        | Anjun kanchan
	///  5 | 2 | 13        | Minjun kanchan
	/// ===+===+===========+=====================
	///  4 | 3 | 16        | Anjun ryanmen low
	///  5 | 3 | 17        | Minjun ryanmen low
	/// ===+===+===========+=====================
	///  4 | 4 | 20        | Anjun ryanmen high
	///  5 | 4 | 21        | Minjun ryanmen high
	pub(crate) const fn dw(self) -> u8 {
		let [d, _, w] = self.parts();
		let result = d + w * 4;
		unsafe { core::hint::assert_unchecked(result != 10); }
		unsafe { core::hint::assert_unchecked(result != 11); }
		unsafe { core::hint::assert_unchecked(result != 14); }
		unsafe { core::hint::assert_unchecked(result != 15); }
		unsafe { core::hint::assert_unchecked(result != 18); }
		unsafe { core::hint::assert_unchecked(result != 19); }
		unsafe { core::hint::assert_unchecked(result <= 21); }
		result
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
impl AsRef<ScorableHandMeld> for ScorableHandFourthMeld {
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

		let mut is_ok = true;
		self.as_ref().for_each_tile(|t| { is_ok = is_ok && write!(f, "{t} ").is_ok(); });

		if is_ok {
			let dw = self.dw();
			let start = (5 - (usize::from(dw < 6) + usize::from(dw < 8) + usize::from(dw < 12) + usize::from(dw < 16) + usize::from(dw < 20))) * 14;
			let len = 14 - (usize::from(dw < 6) * 8 + usize::from(dw < 16) * 4 + usize::from(dw < 20));
			let end = start + len;
			// Micro-optimization: rustc does not notice that all the ranges are valid and emits a str slice check, so assert that they are valid.
			unsafe { core::hint::assert_unchecked(start <= end); }
			unsafe { core::hint::assert_unchecked(end <= SUFFIX_STRINGS.len()); }
			let s = &SUFFIX_STRINGS[start..end];
			f.write_str(s)
		}
		else {
			Err(core::fmt::Error)
		}
	}
}

/// Converts a `ScorableHandMeld` to a `ScorableHandFourthMeld` with a `Tanki` wait.
impl From<ScorableHandMeld> for ScorableHandFourthMeld {
	fn from(meld: ScorableHandMeld) -> Self {
		match meld {
			ScorableHandMeld::Ankan(t) => Self::Ankan(t, KanWait::Tanki),
			ScorableHandMeld::Minkan(t) => Self::Minkan(t, KanWait::Tanki),
			ScorableHandMeld::Ankou(t) => Self::Ankou(t, KouWait::Tanki),
			ScorableHandMeld::Minkou(t) => Self::Minkou(t, KouWait::Tanki),
			ScorableHandMeld::Anjun(t) => Self::Anjun(t, ShunWait::Tanki),
			ScorableHandMeld::Minjun(t) => Self::Minjun(t, ShunWait::Tanki),
		}
	}
}

impl Eq for ScorableHandFourthMeld {}

impl Ord for ScorableHandFourthMeld {
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

			let sc = m.parts();

			// sc is `[d, t, w]`. Transform it to `[w, zero, d, t]` and then to `t:d:zero:w`.
			//
			// `zero:t:d:w` or `t:d:w:zero` would also work but those arrangements require more instructions to produce.
			// `rotate_left(8)` aka `rotate_right(24)` compiles to a single instruction on RV (`roriw 24`) and x86_64 (`rorx 24`).

			// `[d, t, w]` -> `[zero, d, t, w]`
			//
			// Note that rustc stores `[u8; 3]` in a register like a `u32`, and is smart enough to notice that this is just `<< 8` on that `u32`.
			let sc = [0, sc[0], sc[1], sc[2]];

			// `[zero, d, t, w]` -> `w:t:d:zero`
			let sc = u32::from_le_bytes(sc);

			let sc = sc | (0b1 << 16);

			// `w:t:d:zero` -> `t:d:zero:w`
			sc.rotate_left(8)
		}

		let sc = sort_criteria(*self);
		let sc_other = sort_criteria(*other);
		sc.cmp(&sc_other)
	}
}

impl PartialEq for ScorableHandFourthMeld {
	fn eq(&self, other: &Self) -> bool {
		// Micro-optimization: We don't want to use `derive(PartialEq)` because the auto-generated impl has the branchy element-by-element comparison problem
		// mentioned in `ScorableHandFourthMeld::cmp` above.
		//
		// Note that rustc is smart enough to elide the `.rotate_right(16)` because it understands that the rotation would not change the result of equality comparison.
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

impl PartialOrd for ScorableHandFourthMeld {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl ScorableHandPair {
	/// Construct a `ScorableHandPair` using the given tiles.
	///
	/// Returns `Some` if `t1.eq_ignore_red(&t2)`, `None` otherwise.
	pub fn new(t1: Tile, t2: Tile) -> Option<Self> {
		let t = Tile::pair_representative(t1, t2)?;
		Some(Self(t))
	}

	/// Construct a `ScorableHandPair` using the given tiles.
	///
	/// # Safety
	///
	/// Requires `t1.eq_ignore_red(&t2)`.
	pub unsafe fn new_unchecked(t1: Tile, t2: Tile) -> Self {
		let t = unsafe { Tile::pair_representative_unchecked(t1, t2) };
		Self(t)
	}

	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		f(self.0.remove_red());
		f(self.0);
	}

	pub(crate) fn num_yakuhai(self, round_wind: WindTile, seat_wind: WindTile) -> u8 {
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

		let mut is_ok = true;
		self.for_each_tile(|t| { is_ok = is_ok && write!(f, "{t} ").is_ok(); });

		if is_ok { f.write_str("}") } else { Err(core::fmt::Error) }
	}
}

impl Ord for ScorableHandPair {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		self.0.cmp_ignore_red(&other.0)
	}
}

impl PartialEq for ScorableHandPair {
	fn eq(&self, other: &Self) -> bool {
		self.0.eq_ignore_red(&other.0)
	}
}

impl PartialOrd for ScorableHandPair {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

// [     3     ][        2         ][      1            0       ]
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
// Has | None = Has
// Has | Has = Has
// Has | All = Has
// All | None = All
// All | Has = Has
// All | All = All
//
// Tested exhaustively in the `chanta_routou` test.
#[derive(Clone, Copy)]
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

impl core::ops::BitOr for ChantaRoutou {
	type Output = ChantaRoutou;

	fn bitor(self, rhs: Self) -> Self::Output {
		Self(self.0 | rhs.0)
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

// 0 => Neither
// 1 => Sanankou
// 2 => Suuankou
// 4 => Suuankou tanki
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct NumAnkou(u8);

impl NumAnkou {
	pub(crate) const fn is_sanankou(self) -> bool {
		self.0 == 1
	}

	pub(crate) const fn num_suuankou(self) -> u8 {
		self.0 >> 1
	}
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct NumKantsu(u8);

impl NumKantsu {
	pub(crate) fn is_sankantsu(self) -> bool {
		self.0 == 3
	}

	pub(crate) fn is_suukantsu(self) -> bool {
		self.0 == 4
	}
}

#[derive(Clone, Copy)]
pub(crate) struct Honchinitsu(u8);

impl Honchinitsu {
	fn new(ts: impl IntoIterator<Item = u8>) -> Self {
		fn inner(result: &mut u8, suit: &mut Option<NumberSuit>, t: u8) {
			if let Some(suit_) = NumberSuit::of(t) {
				if let Some(suit) = *suit {
					// suit != t.suit() => Neither
					//
					// Micro-optimization: Any way to generate a value >= 0b10 is sufficient, but `+ << 1` generates the simplest code on RV - an `sh1add`.
					// On x86_64 both `| << 1` and `+ << 1` generate `add; add`.
					*result += u8::from(suit != suit_) << 1;
				}
				// Micro-optimization: Doing this always instead of inside an `else` seems redundant, but generates smaller code with fewer branches.
				*suit = Some(suit_);
			}
			else {
				// Honitsu
				*result |= 0b01;
			}
		}

		let mut suit = None;

		// 0x00 => Chinitsu
		// 0x01 => Honitsu
		//    _ => Neither
		//
		// This is effectively a tri-state like `Option<bool>`, but avoids needing to make the effort to encode `None` as `0x02` specifically.
		// With this approach, any value > 0x01 acts as `None`.
		//
		// Start as Chinitsu, then weaken it to Honitsu or Neither.
		let mut result = 0b00;

		for t in ts {
			inner(&mut result, &mut suit, t);
		}

		// suit.is_none() => Neither
		result += u8::from(suit.is_none()) << 1;

		Self(result)
	}

	pub(crate) const fn is_honitsu(self) -> bool {
		self.0 == 0b01
	}

	pub(crate) const fn is_chinitsu(self) -> bool {
		self.0 == 0b00
	}
}

#[derive(Clone, Copy)]
pub(crate) struct SuushiiSangen {
	num_wind_melds: u8,
	num_dragon_melds: u8,
	pair: WindOrDragon,
}

#[derive(Clone, Copy)]
#[repr(u8)]
#[expect(unused)] // Constructed via `transmute`
enum WindOrDragon {
	Neither = 0,
	Wind = 1,
	Dragon = 2,
}

impl SuushiiSangen {
	pub(crate) const fn is_shousuushii(self) -> bool {
		self.num_wind_melds == 3 && matches!(self.pair, WindOrDragon::Wind)
	}

	pub(crate) const fn is_daisuushii(self) -> bool {
		self.num_wind_melds == 4
	}

	pub(crate) const fn is_shousangen(self) -> bool {
		self.num_dragon_melds == 2 && matches!(self.pair, WindOrDragon::Dragon)
	}

	pub(crate) const fn is_daisangen(self) -> bool {
		self.num_dragon_melds == 3
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

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
				Self::Regular(h) => h.num_peikou() == 1,
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
			match *self {
				Self::Regular(h) => h.num_wind_yakuhai(wind, round_wind, seat_wind),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => 0,
			}
		}

		fn is_dragon_yakuhai(&self, dragon: DragonTile) -> bool {
			match *self {
				Self::Regular(h) => h.is_dragon_yakuhai(dragon),
				Self::Chiitoi(_) |
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
			match *self {
				Self::Regular(h) => h.is_sanshoku_doujun(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_ittsuu(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_ittsuu(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_toitoi(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_toitoi(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanankou(&self) -> bool {
			match self {
				Self::Regular(h) => h.num_ankou().is_sanankou(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sanshoku_doukou(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_sanshoku_doukou(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_sankantsu(&self) -> bool {
			match *self {
				Self::Regular(h) => h.num_kantsu().is_sankantsu(),
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
			match *self {
				Self::Regular(h) => h.is_shousangen(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_honitsu(&self) -> bool {
			match self {
				Self::Regular(h) => h.honchinitsu().is_honitsu(),
				Self::Chiitoi(h) => h.honchinitsu().is_honitsu(),
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
				Self::Regular(h) => h.num_peikou() == 2,
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_chinitsu(&self) -> bool {
			match self {
				Self::Regular(h) => h.honchinitsu().is_chinitsu(),
				Self::Chiitoi(h) => h.honchinitsu().is_chinitsu(),
				Self::KokushiMusou(_) => false,
			}
		}

		const fn is_kokushi_musou(&self) -> bool {
			matches!(self, Self::KokushiMusou(_))
		}

		fn num_suuankou(&self) -> u8 {
			match self {
				Self::Regular(h) => h.num_ankou().num_suuankou(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => 0,
			}
		}

		fn is_daisangen(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_daisangen(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_shousuushii(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_shousuushii(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_daisuushii(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_daisuushii(),
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
				Self::Regular(h) => h.is_ryuuiisou(),
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
			match *self {
				Self::Regular(h) => h.num_kantsu().is_suukantsu(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}
	}

	impl ScorableHandRegular {
		pub(crate) fn is_shousangen(&self) -> bool {
			self.suushii_sangen().is_shousangen()
		}

		pub(crate) fn is_daisangen(&self) -> bool {
			self.suushii_sangen().is_daisangen()
		}

		pub(crate) fn is_shousuushii(&self) -> bool {
			self.suushii_sangen().is_shousuushii()
		}

		pub(crate) fn is_daisuushii(&self) -> bool {
			self.suushii_sangen().is_daisuushii()
		}
	}

	#[test]
	fn num_yakuhai() {
		for &t in Tile::each(crate::GameType::Yonma) {
			let p = unsafe { ScorableHandPair::new_unchecked(t, t) };
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

	macro_rules! test {
		(@inner_new_tile $hand:ident) => {};

		(@inner_new_tile $hand:ident + $new_tile:tt => [ $( $scorable_hand:tt => { $($funcs:tt)* } )* ] $($rest:tt)*) => {{
			{
				std::println!("hand: {:?} + {}", $hand, t!($new_tile));
				let mut hands: std::collections::BTreeSet<_> = $hand.to_scorable_hands(t!($new_tile), $crate::TsumoOrRon::Tsumo).collect();
				$({
					let hand = hands.pop_first().unwrap();
					assert_eq!(hand, make_scorable_hand! $scorable_hand);
					test!(@inner_func hand $($funcs)*);
				})*
				assert!(hands.is_empty());
			}
			test!(@inner_new_tile $hand $($rest)* );
		}};

		(@inner_new_tile $hand:ident + $new_tile:tt ron => [ $( $scorable_hand:tt => { $($funcs:tt)* } )* ] $($rest:tt)*) => {{
			{
				std::println!("hand: {:?} + {}", $hand, t!($new_tile));
				let mut hands: std::collections::BTreeSet<_> = $hand.to_scorable_hands(t!($new_tile), $crate::TsumoOrRon::Ron).collect();
				$({
					let hand = hands.pop_first().unwrap();
					assert_eq!(hand, make_scorable_hand! $scorable_hand);
					test!(@inner_func hand $($funcs)*);
				})*
				assert!(hands.is_empty());
			}
			test!(@inner_new_tile $hand $($rest)* );
		}};

		(@inner_func $hand:ident) => {};

		(@inner_func $hand:ident $func:ident $args:tt ; $($rest:tt)*) => {{
			assert!($hand.$func $args);
			test!(@inner_func $hand $($rest)*);
		}};

		(@inner_func $hand:ident ! $func:ident $args:tt ; $($rest:tt)*) => {{
			assert!(! $hand.$func $args);
			test!(@inner_func $hand $($rest)*);
		}};

		(@inner_func $hand:ident $func:ident $args:tt == $value:expr ; $($rest:tt)*) => {{
			assert_eq!($hand.$func $args, $value);
			test!(@inner_func $hand $($rest)*);
		}};

		($hand:tt $($new_tile:tt)*) => {{
			let hand: $crate::HandStable = ($crate::make_hand! $hand).into();
			test!(@inner_new_tile hand $($new_tile)*);
		}};
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn pinfu1() {
		test!((2m 3m 4m 4p 5p 7p 8p 9p 4s 5s 6s 8s 8s)
			+ 3p => [
				({ anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 4s 5s 6s } { anjun 3p 4p 5p ryanmen_low } { 8s 8s }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 6p => [
				({ anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 4s 5s 6s } { anjun 4p 5p 6p ryanmen_high } { 8s 8s }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
	#[test]
	fn pinfu2() {
		test!((1m 2m 3m 2s 3s 4s 7s 8s 5p 6p 7p 9p 9p)
			+ 6s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 6s 7s 8s ryanmen_low } { 9p 9p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 9s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 7s 8s 9s ryanmen_high } { 9p 9p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
	//
	// > Counter examples
	// >
	// > Every tile group is a sequence, but this hand is open.
	#[test]
	fn pinfu3() {
		test!((4m 5m 6m 3p 4p 5p 7p 8p 5s 5s { minjun 5s 6s 7s })
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 3p 4p 5p } { minjun 5s 6s 7s } { anjun 6p 7p 8p ryanmen_low } { 5s 5s }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 9p => [
				({ anjun 4m 5m 6m } { anjun 3p 4p 5p } { minjun 5s 6s 7s } { anjun 7p 8p 9p ryanmen_high } { 5s 5s }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
	//
	// > Counter examples
	// >
	// > The pair of east winds invalidates pinfu if won by the dealer or by any player in the east round.
	#[test]
	fn pinfu4() {
		test!((2m 3m 1p 2p 3p 6s 7s 8s 3m 4m 5m E E)
			+ 1m => [
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 1m 2m 3m ryanmen_low } { E E }) => {
					!is_pinfu(tw!(E), tw!(E));
					!is_pinfu(tw!(E), tw!(S));
					!is_pinfu(tw!(E), tw!(W));
					!is_pinfu(tw!(E), tw!(N));
					!is_pinfu(tw!(S), tw!(E));
					is_pinfu(tw!(S), tw!(S));
					is_pinfu(tw!(S), tw!(W));
					is_pinfu(tw!(S), tw!(N));
					!is_pinfu(tw!(W), tw!(E));
					is_pinfu(tw!(W), tw!(S));
					is_pinfu(tw!(W), tw!(W));
					is_pinfu(tw!(W), tw!(N));
					!is_pinfu(tw!(N), tw!(E));
					is_pinfu(tw!(N), tw!(S));
					is_pinfu(tw!(N), tw!(W));
					is_pinfu(tw!(N), tw!(N));
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m kanchan } { E E }) => {
					!is_pinfu(tw!(E), tw!(E));
					!is_pinfu(tw!(E), tw!(S));
					!is_pinfu(tw!(E), tw!(W));
					!is_pinfu(tw!(E), tw!(N));
					!is_pinfu(tw!(S), tw!(E));
					!is_pinfu(tw!(S), tw!(S));
					!is_pinfu(tw!(S), tw!(W));
					!is_pinfu(tw!(S), tw!(N));
					!is_pinfu(tw!(W), tw!(E));
					!is_pinfu(tw!(W), tw!(S));
					!is_pinfu(tw!(W), tw!(W));
					!is_pinfu(tw!(W), tw!(N));
					!is_pinfu(tw!(N), tw!(E));
					!is_pinfu(tw!(N), tw!(S));
					!is_pinfu(tw!(N), tw!(W));
					!is_pinfu(tw!(N), tw!(N));
				}
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 2m 3m 4m ryanmen_high } { E E }) => {
					!is_pinfu(tw!(E), tw!(E));
					!is_pinfu(tw!(E), tw!(S));
					!is_pinfu(tw!(E), tw!(W));
					!is_pinfu(tw!(E), tw!(N));
					!is_pinfu(tw!(S), tw!(E));
					is_pinfu(tw!(S), tw!(S));
					is_pinfu(tw!(S), tw!(W));
					is_pinfu(tw!(S), tw!(N));
					!is_pinfu(tw!(W), tw!(E));
					is_pinfu(tw!(W), tw!(S));
					is_pinfu(tw!(W), tw!(W));
					is_pinfu(tw!(W), tw!(N));
					!is_pinfu(tw!(N), tw!(E));
					is_pinfu(tw!(N), tw!(S));
					is_pinfu(tw!(N), tw!(W));
					is_pinfu(tw!(N), tw!(N));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
	//
	// > Counter examples
	// >
	// > The pair wait invalidates pinfu.
	#[test]
	fn pinfu5() {
		test!((1p 2p 3p 4p 5p 6p 7m 8m 9m 5s 6s 7s 3m)
			+ 3m => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7m 8m 9m } { anjun 5s 6s 7s } { 3m 3m }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
	//
	// > Counter examples
	// >
	// > The dragon pair invalidates pinfu.
	#[test]
	fn pinfu6() {
		test!((2m 3m 1p 2p 3p 6s 7s 8s 3m 4m 5m Wh Wh)
			+ 1m => [
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 1m 2m 3m ryanmen_low } { Wh Wh }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m kanchan } { Wh Wh }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 2m 3m 4m ryanmen_high } { Wh Wh }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
	//
	// > Counter examples
	// >
	// > The kanchan wait invalidates pinfu.
	#[test]
	fn pinfu7() {
		test!((1m 2m 3m 2s 3s 4s 7s 9s 2p 2p 5p 6p 7p)
			+ 8s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 7s 8s 9s kanchan } { 2p 2p }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744
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
					!is_pinfu(tw!(E), tw!(E));
				}
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 6p 7p 8p ryanmen_low } { 6p 6p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 9p => [
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 7p 8p 9p ryanmen_high } { 6p 6p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 3p => [
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 4p 5p 6p } { anjun 6p 7p 8p } { 3p 3p }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);
	}

	// Ref: https://mahjongsoul.game.yo-star.com/?paipu=260122-eb23da04-3945-40c2-b154-a6f55eb1ed1c_a909728900
	#[test]
	fn iipeikou() {
		test!((8m 8m 2s 3s 4s 5s 0s 6s 6s 7s 7s E E)
			+ 8m => [
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 0s 6s 7s } { ankou 8m 8m 8m shanpon } { E E }) => {
					is_iipeikou();
				}
			]
			+ E => [
				({ anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 0s 6s 7s } { ankou E E E shanpon } { 8m 8m }) => {
					is_iipeikou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn tanyao1() {
		test!((3m 3m 3m 4m 4m 2p 2p 2p 5p 6p 7p 8p 8p)
			+ 8p => [
				({ ankou 3m 3m 3m } { ankou 2p 2p 2p } { anjun 5p 6p 7p } { ankou 8p 8p 8p shanpon } { 4m 4m }) => {
					is_tanyao();
				}
			]
			+ 4m => [
				({ ankou 3m 3m 3m } { ankou 2p 2p 2p } { anjun 5p 6p 7p } { ankou 4m 4m 4m shanpon } { 8p 8p }) => {
					is_tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tanyao&oldid=27461
	#[test]
	fn tanyao2() {
		test!((3s 3s 3s 6s 7s 8s 4m 5m 6m 3p 3p 5p 5p)
			+ 3p => [
				({ ankou 3s 3s 3s } { anjun 6s 7s 8s } { anjun 4m 5m 6m } { ankou 3p 3p 3p shanpon } { 5p 5p }) => {
					is_tanyao();
				}
			]
			+ 5p => [
				({ ankou 3s 3s 3s } { anjun 6s 7s 8s } { anjun 4m 5m 6m } { ankou 5p 5p 5p shanpon } { 3p 3p }) => {
					is_tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tanyao&oldid=27461
	#[test]
	fn tanyao3() {
		test!((6m 7m 8m 4s 5s 3p 3p 3p 6p 6p { minkou 2m 2m 2m })
			+ 3s => [
				({ anjun 6m 7m 8m } { ankou 3p 3p 3p } { minkou 2m 2m 2m } { anjun 3s 4s 5s ryanmen_low } { 6p 6p }) => {
					is_tanyao();
				}
			]
			+ 6s => [
				({ anjun 6m 7m 8m } { ankou 3p 3p 3p } { minkou 2m 2m 2m } { anjun 4s 5s 6s ryanmen_high } { 6p 6p }) => {
					is_tanyao();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn yakuhai1() {
		test!((1p 2p 3p 5s 5s G G { minkou 9p 9p 9p } { minkou E E E })
			+ 5s => [
				({ anjun 1p 2p 3p } { minkou 9p 9p 9p } { minkou E E E } { ankou 5s 5s 5s shanpon } { G G }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 2;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
					!is_dragon_yakuhai(td!(Wh));
					!is_dragon_yakuhai(td!(G));
					!is_dragon_yakuhai(td!(R));
				}
			]
			+ G => [
				({ anjun 1p 2p 3p } { minkou 9p 9p 9p } { minkou E E E } { ankou G G G shanpon } { 5s 5s }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 2;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
					!is_dragon_yakuhai(td!(Wh));
					is_dragon_yakuhai(td!(G));
					!is_dragon_yakuhai(td!(R));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Yakuhai&oldid=25808
	#[test]
	fn yakuhai2() {
		test!((G G 3p 4p 5p 9m 9m { minjun 1m 2m 3m } { minkou 6s 6s 6s })
			+ G => [
				({ anjun 3p 4p 5p } { minjun 1m 2m 3m } { minkou 6s 6s 6s } { ankou G G G shanpon } { 9m 9m }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
					!is_dragon_yakuhai(td!(Wh));
					is_dragon_yakuhai(td!(G));
					!is_dragon_yakuhai(td!(R));
				}
			]
			+ 9m => [
				({ anjun 3p 4p 5p } { minjun 1m 2m 3m } { minkou 6s 6s 6s } { ankou 9m 9m 9m shanpon } { G G }) => {
					num_wind_yakuhai(tw!(E), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(S), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(W), tw!(E), tw!(E)) == 0;
					num_wind_yakuhai(tw!(N), tw!(E), tw!(E)) == 0;
					!is_dragon_yakuhai(td!(Wh));
					!is_dragon_yakuhai(td!(G));
					!is_dragon_yakuhai(td!(R));
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn chanta1() {
		test!((1m 1m 7p 8p 9p 1s 2s 3s S S { minjun 2p 1p 3p })
			+ 1m => [
				({ anjun 7p 8p 9p } { anjun 1s 2s 3s } { minjun 2p 1p 3p } { ankou 1m 1m 1m shanpon } { S S }) => {
					is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ S => [
				({ anjun 7p 8p 9p } { anjun 1s 2s 3s } { minjun 2p 1p 3p } { ankou S S S shanpon } { 1m 1m }) => {
					is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chanta&oldid=27929
	#[test]
	fn chanta2() {
		test!((1p 2p 3p 9s 9s 9s N N 2m 3m 7m 8m 9m)
			+ 1m => [
				({ anjun 1p 2p 3p } { ankou 9s 9s 9s } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_low } { N N }) => {
					is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ 4m => [
				({ anjun 1p 2p 3p } { ankou 9s 9s 9s } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_high } { N N }) => {
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=27023
	#[test]
	fn sanshoku_doujun1() {
		test!((1m 2m 3m 1p 2p 3p 1s 2s 3s 6s 7s 8s E)
			+ E => [
				({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s } { E E }) => {
					is_sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=27023
	#[test]
	fn sanshoku_doujun2() {
		test!((1m 2m 3m 1p 2p 3p 1s 2s 3s E { minjun 6s 7s 8s })
			+ E => [
				({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s } { E E }) => {
					is_sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=27023
	#[test]
	fn sanshoku_doujun3() {
		test!((1p 2p 3p 6s 7s E E { minjun 1m 2m 3m } { minjun 3s 1s 2s})
			+ 8s => [
				({ anjun 1p 2p 3p } { minjun 1m 2m 3m } { minjun 3s 1s 2s } { anjun 6s 7s 8s ryanmen_high } { E E }) => {
					is_sanshoku_doujun();
				}
			]
			+ 5s => [
				({ anjun 1p 2p 3p } { minjun 1m 2m 3m } { minjun 3s 1s 2s } { anjun 5s 6s 7s ryanmen_low } { E E }) => {
					is_sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=27023
	#[test]
	fn sanshoku_doujun4() {
		test!((4m 5m 6m 4s 5s 6s 4p 5p S S S G G)
			+ 3p => [
				({ anjun 4m 5m 6m } { anjun 4s 5s 6s } { ankou S S S } { anjun 3p 4p 5p ryanmen_low } { G G }) => {
					!is_sanshoku_doujun();
				}
			]
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 4s 5s 6s } { ankou S S S } { anjun 4p 5p 6p ryanmen_high } { G G }) => {
					is_sanshoku_doujun();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ikki_tsuukan&oldid=27851
	#[test]
	fn ittsuu1() {
		test!((1m 2m 3m 4m 0m 6m 7m 8m 9m 3p 4p 5s 5s)
			+ 2p => [
				({ anjun 1m 2m 3m } { anjun 4m 0m 6m } { anjun 7m 8m 9m } { anjun 2p 3p 4p ryanmen_low } { 5s 5s }) => {
					is_ittsuu();
				}
			]
			+ 5p => [
				({ anjun 1m 2m 3m } { anjun 4m 0m 6m } { anjun 7m 8m 9m } { anjun 3p 4p 5p ryanmen_high } { 5s 5s }) => {
					is_ittsuu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ikki_tsuukan&oldid=27851
	#[test]
	fn ittsuu2() {
		test!((2m 2m 2m 4s 6s Wh Wh { minjun 1s 2s 3s } { minjun 7s 8s 9s })
			+ 5s => [
				({ ankou 2m 2m 2m } { minjun 1s 2s 3s } { minjun 7s 8s 9s } { anjun 4s 5s 6s kanchan } { Wh Wh }) => {
					is_ittsuu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ikki_tsuukan&oldid=27851
	#[test]
	fn ittsuu3() {
		test!((1m 2m 3m 4m 4m 5p 6p { minjun 5m 6m 7m } { minjun 7m 8m 9m })
			+ 4p => [
				({ anjun 1m 2m 3m } { minjun 5m 6m 7m } { minjun 7m 8m 9m } { anjun 4p 5p 6p ryanmen_low } { 4m 4m }) => {
					!is_ittsuu();
				}
			]
			+ 7p => [
				({ anjun 1m 2m 3m } { minjun 5m 6m 7m } { minjun 7m 8m 9m } { anjun 5p 6p 7p ryanmen_high } { 4m 4m }) => {
					!is_ittsuu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn toitoi1() {
		test!((1m 1m 1m 7p 7p 4s 4s S S S { minkou 8p 8p 8p })
			+ 7p => [
				({ ankou 1m 1m 1m } { ankou S S S } { minkou 8p 8p 8p } { ankou 7p 7p 7p shanpon } { 4s 4s }) => {
					is_toitoi();
				}
			]
			+ 4s => [
				({ ankou 1m 1m 1m } { ankou S S S } { minkou 8p 8p 8p } { ankou 4s 4s 4s shanpon } { 7p 7p }) => {
					is_toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=27883
	#[test]
	fn toitoi2() {
		test!((1p 1p 1p 4p 4p 4p 8s 8s R R { minkou W W W })
			+ 8s => [
				({ ankou 1p 1p 1p } { ankou 4p 4p 4p } { minkou W W W } { ankou 8s 8s 8s shanpon } { R R }) => {
					is_toitoi();
				}
			]
			+ R => [
				({ ankou 1p 1p 1p } { ankou 4p 4p 4p } { minkou W W W } { ankou R R R shanpon } { 8s 8s }) => {
					is_toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=27883
	#[test]
	fn toitoi3() {
		test!((2m 2m 2m 9p 9p Wh Wh { ankan 4p 4p 4p 4p } { minkou W W W })
			+ 9p => [
				({ ankou 2m 2m 2m } { ankan 4p 4p 4p 4p } { minkou W W W } { ankou 9p 9p 9p shanpon } { Wh Wh }) => {
					is_toitoi();
				}
			]
			+ Wh => [
				({ ankou 2m 2m 2m } { ankan 4p 4p 4p 4p } { minkou W W W } { ankou Wh Wh Wh shanpon } { 9p 9p }) => {
					is_toitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=27883
	#[test]
	fn toitoi4() {
		test!((N N N 3p 3p 3p 6s 6s 6s 7m 7m G G)
			+ 7m => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { ankou 7m 7m 7m shanpon } { G G }) => {
					num_suuankou() == 1;
				}
			]
			+ 7m ron => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { minkou 7m 7m 7m shanpon } { G G }) => {
					is_toitoi();
					is_sanankou();
					num_suuankou() == 0;
				}
			]
			+ G => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { ankou G G G shanpon } { 7m 7m }) => {
					num_suuankou() == 1;
				}
			]
			+ G ron => [
				({ ankou N N N } { ankou 3p 3p 3p } { ankou 6s 6s 6s } { minkou G G G shanpon } { 7m 7m }) => {
					is_toitoi();
					is_sanankou();
					num_suuankou() == 0;
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn sanankou1() {
		test!((6m 6m 6m 2p 3p 8p 8p 4s 4s 4s N N N)
			+ 1p => [
				({ ankou 6m 6m 6m } { ankou 4s 4s 4s } { ankou N N N } { anjun 1p 2p 3p ryanmen_low } { 8p 8p }) => {
					is_sanankou();
				}
			]
			+ 4p => [
				({ ankou 6m 6m 6m } { ankou 4s 4s 4s } { ankou N N N } { anjun 2p 3p 4p ryanmen_high } { 8p 8p }) => {
					is_sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=27270
	#[test]
	fn sanankou2() {
		test!((1p 1p 1p 3p 3p 3p 5p 5p 5p 6s { minjun 1s 2s 3s })
			+ 6s => [
				({ ankou 1p 1p 1p } { ankou 3p 3p 3p } { ankou 5p 5p 5p } { minjun 1s 2s 3s } { 6s 6s }) => {
					is_sanankou();
				}
			]
			+ 6s ron => [
				({ ankou 1p 1p 1p } { ankou 3p 3p 3p } { ankou 5p 5p 5p } { minjun 1s 2s 3s } { 6s 6s }) => {
					is_sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=27270
	#[test]
	fn sanankou3() {
		test!((1m 2m 3m 1p 1p 1p 3p 3p 6p 6p 6s 6s 6s)
			+ 3p => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { ankou 3p 3p 3p shanpon } { 6p 6p }) => {
					is_sanankou();
				}
			]
			+ 3p ron => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { minkou 3p 3p 3p shanpon } { 6p 6p }) => {
					!is_sanankou();
				}
			]
			+ 6p => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { ankou 6p 6p 6p shanpon } { 3p 3p }) => {
					is_sanankou();
				}
			]
			+ 6p ron => [
				({ anjun 1m 2m 3m } { ankou 1p 1p 1p } { ankou 6s 6s 6s } { minkou 6p 6p 6p shanpon } { 3p 3p }) => {
					!is_sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=27270
	//
	// > Note: A tsumo results in the suuankou yakuman.
	#[test]
	fn sanankou4() {
		test!((7m 7m 7m 8p 8p 8p 3s 3s E E R R R)
			+ 3s => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { ankou 3s 3s 3s shanpon } { E E }) => {
					num_suuankou() == 1;
				}
			]
			+ 3s ron => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { minkou 3s 3s 3s shanpon } { E E }) => {
					is_sanankou();
				}
			]
			+ E => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { ankou E E E shanpon } { 3s 3s }) => {
					num_suuankou() == 1;
				}
			]
			+ E ron => [
				({ ankou 7m 7m 7m } { ankou 8p 8p 8p } { ankou R R R } { minkou E E E shanpon } { 3s 3s }) => {
					is_sanankou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn sanshoku_doukou1() {
		test!((4m 5m 6m 7m 7m 7m 5s { minkou 7s 7s 7s } { minkou 7p 7p 7p })
			+ 5s => [
				({ anjun 4m 5m 6m } { ankou 7m 7m 7m } { minkou 7s 7s 7s } { minkou 7p 7p 7p } { 5s 5s }) => {
					is_sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=27024
	#[test]
	fn sanshoku_doukou2() {
		test!((3m 3m 3m 3s 3s 3s 6s 7s W W { minkou 3p 3p 3p })
			+ 5s => [
				({ ankou 3m 3m 3m } { ankou 3s 3s 3s } { minkou 3p 3p 3p } { anjun 5s 6s 7s ryanmen_low } { W W }) => {
					is_sanshoku_doukou();
				}
			]
			+ 8s => [
				({ ankou 3m 3m 3m } { ankou 3s 3s 3s } { minkou 3p 3p 3p } { anjun 6s 7s 8s ryanmen_high } { W W }) => {
					is_sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=27024
	#[test]
	fn sanshoku_doukou3() {
		test!((3m 3m 3m 3s 3s 4s 5s 6s 6s 6s { minkou 3p 3p 3p })
			+ 3s => [
				({ ankou 3m 3m 3m } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 3s 4s 5s ryanmen_low } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
				({ ankou 3m 3m 3m } { anjun 4s 5s 6s } { minkou 3p 3p 3p } { ankou 3s 3s 3s shanpon } { 6s 6s }) => {
					is_sanshoku_doukou();
				}
			]
			+ 6s => [
				({ ankou 3m 3m 3m } { anjun 4s 5s 6s } { minkou 3p 3p 3p } { ankou 6s 6s 6s shanpon } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 4s 5s 6s ryanmen_high } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=27024
	#[test]
	fn sanshoku_doukou4() {
		test!((3m 3m 3m 3s 3s 6s 7s 8s W W { minkou 3p 3p 3p })
			+ 3s => [
				({ ankou 3m 3m 3m } { anjun 6s 7s 8s } { minkou 3p 3p 3p } { ankou 3s 3s 3s shanpon } { W W }) => {
					is_sanshoku_doukou();
				}
			]
			+ W => [
				({ ankou 3m 3m 3m } { anjun 6s 7s 8s } { minkou 3p 3p 3p } { ankou W W W shanpon } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn sankantsu1() {
		test!((4m 5m 6m 2s { minkan 6p 6p 6p 6p } { minkan 9s 9s 9s 9s } { ankan 5s 5s 5s 5s })
			+ 2s => [
				({ anjun 4m 5m 6m } { minkan 6p 6p 6p 6p } { minkan 9s 9s 9s 9s } { ankan 5s 5s 5s 5s } { 2s 2s }) => {
					is_sankantsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Sankantsu&oldid=27944
	#[test]
	fn sankantsu2() {
		test!((3p 4p 5p E { minkan 4m 4m 4m 4m } { ankan 8s 8s 8s 8s } { minkan 2p 2p 2p 2p })
			+ E => [
				({ anjun 3p 4p 5p } { minkan 4m 4m 4m 4m } { ankan 8s 8s 8s 8s } { minkan 2p 2p 2p 2p } { E E }) => {
					is_sankantsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn chiitoi1() {
		test!((1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh)
			+ S => [
				({ 1p 1p } { 7p 7p } { W W } { 5m 5m } { S S } { 4s 4s } { Wh Wh }) => {
					is_chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiitoitsu&oldid=27947
	#[test]
	fn chiitoi2() {
		test!((1m 1m 3m 3m 4m 5p 5p 2s 2s W W Wh Wh)
			+ 4m => [
				({ 1m 1m } { 3m 3m } { 4m 4m } { 5p 5p } { 2s 2s } { W W } { Wh Wh }) => {
					is_chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn honroutou1() {
		test!((1m 1m 1m 9m 9m S S { minkou 9s 9s 9s } { minkou N N N })
			+ 9m => [
				({ ankou 1m 1m 1m } { minkou 9s 9s 9s } { minkou N N N } { ankou 9m 9m 9m shanpon } { S S }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ S => [
				({ ankou 1m 1m 1m } { minkou 9s 9s 9s } { minkou N N N } { ankou S S S shanpon } { 9m 9m }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727
	#[test]
	fn honroutou2() {
		test!((1p 1p 1p 9s 9s 9s E E 1m 1m { minkou S S S })
			+ E => [
				({ ankou 1p 1p 1p } { ankou 9s 9s 9s } { minkou S S S } { ankou E E E shanpon } { 1m 1m }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ 1m => [
				({ ankou 1p 1p 1p } { ankou 9s 9s 9s } { minkou S S S } { ankou 1m 1m 1m shanpon } { E E }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727
	#[test]
	fn honroutou3() {
		test!((1p 1p 9s 9s { minkou 9m 9m 9m } { minkou N N N } { minkou W W W })
			+ 1p => [
				({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { ankou 1p 1p 1p shanpon } { 9s 9s }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ 9s => [
				({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { ankou 9s 9s 9s shanpon } { 1p 1p }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727
	#[test]
	fn honroutou4() {
		test!((9m 9m 1p 1p 1s 1s 9s 9s S S W W N)
			+ N => [
				({ 9m 9m } { 1p 1p } { 1s 1s } { 9s 9s } { S S } { W W } { N N }) => {
					is_honroutou();
					!is_chanta();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn shousangen1() {
		test!((6s 7s 8s Wh Wh Wh G G R R { minjun 2m 3m 4m })
			+ G => [
				({ anjun 6s 7s 8s } { ankou Wh Wh Wh } { minjun 2m 3m 4m } { ankou G G G shanpon } { R R }) => {
					is_shousangen();
				}
			]
			+ R => [
				({ anjun 6s 7s 8s } { ankou Wh Wh Wh } { minjun 2m 3m 4m } { ankou R R R shanpon } { G G }) => {
					is_shousangen();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371
	#[test]
	fn shousangen2() {
		test!((2m 3m 3p 4p 0p R R G G G { minkou Wh Wh Wh })
			+ 1m => [
				({ anjun 3p 4p 0p } { ankou G G G } { minkou Wh Wh Wh } { anjun 1m 2m 3m ryanmen_low } { R R }) => {
					is_shousangen();
				}
			]
			+ 4m => [
				({ anjun 3p 4p 0p } { ankou G G G } { minkou Wh Wh Wh } { anjun 2m 3m 4m ryanmen_high } { R R }) => {
					is_shousangen();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371
	#[test]
	fn shousangen3() {
		test!((6m 7m 8m 4s 4s Wh Wh R R R { minkou G G G })
			+ 4s => [
				({ anjun 6m 7m 8m } { ankou R R R } { minkou G G G } { ankou 4s 4s 4s shanpon } { Wh Wh }) => {
					is_shousangen();
				}
			]
			+ Wh => [
				({ anjun 6m 7m 8m } { ankou R R R } { minkou G G G } { ankou Wh Wh Wh shanpon } { 4s 4s }) => {
					!is_shousangen();
					is_daisangen();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371
	#[test]
	fn shousangen4() {
		test!((2p 3p 4p 3s 4s G G { minkou Wh Wh Wh } { minkou R R R })
			+ 5s ron => [
				({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_high } { G G }) => {
					is_shousangen();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371
	#[test]
	fn shousangen5() {
		test!((5m 6m 7m 1s 2s 3s G G R R { minkou Wh Wh Wh })
			+ G ron => [
				({ anjun 5m 6m 7m } { anjun 1s 2s 3s }  { minkou Wh Wh Wh }{ minkou G G G shanpon } { R R }) => {
					is_shousangen();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn honitsu1() {
		test!((6p 6p 7p 8p 9p S S N N N { minjun 2p 1p 3p })
			+ 6p => [
				({ anjun 7p 8p 9p } { ankou N N N } { minjun 2p 1p 3p } { ankou 6p 6p 6p shanpon } { S S }) => {
					is_honitsu();
				}
			]
			+ S => [
				({ anjun 7p 8p 9p } { ankou N N N } { minjun 2p 1p 3p } { ankou S S S shanpon } { 6p 6p }) => {
					is_honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Honiisou&oldid=28041
	#[test]
	fn honitsu2() {
		test!((1m 1m 1m 2m 3m 4m 8m 8m G G { minkou W W W })
			+ 8m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { minkou W W W } { ankou 8m 8m 8m shanpon } { G G }) => {
					is_honitsu();
				}
			]
			+ G => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { minkou W W W } { ankou G G G shanpon } { 8m 8m }) => {
					is_honitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn junchan1() {
		test!((1m 9m 9m 9m 7p 8p 9p 1s 2s 3s { minjun 2s 1s 3s })
			+ 1m => [
				({ ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 1s 2s 3s } { minjun 2s 1s 3s } { 1m 1m }) => {
					is_junchan();
					!is_chanta();
					!is_honroutou();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Junchantaiyaochuu&oldid=27930
	#[test]
	fn junchan2() {
		test!((1m 2m 3m 9m 9m 9m 7p 8p 9p 1s 1s 7s 8s)
			+ 9s => [
				({ anjun 1m 2m 3m } { ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 7s 8s 9s ryanmen_high } { 1s 1s }) => {
					is_junchan();
					!is_chanta();
					!is_honroutou();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ 6s => [
				({ anjun 1m 2m 3m } { ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 6s 7s 8s ryanmen_low } { 1s 1s }) => {
					!is_junchan();
					!is_chanta();
					!is_honroutou();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn ryanpeikou1() {
		test!((4m 4m 5m 5m 6m 6m 6p 6p 7p 8p 8p 2s 2s)
			+ 7p => [
				({ anjun 4m 5m 6m } { anjun 4m 5m 6m } { anjun 6p 7p 8p } { anjun 6p 7p 8p kanchan } { 2s 2s }) => {
					is_ryanpeikou();
					!is_chiitoi();
				}
				({ 4m 4m } { 5m 5m } { 6m 6m } { 6p 6p } { 7p 7p } { 8p 8p } { 2s 2s }) => {
					!is_ryanpeikou();
					is_chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryanpeikou&oldid=27706
	#[test]
	fn ryanpeikou2() {
		test!((2p 2p 3p 3p 4p 4p 6m 6m 7m 7m 8m 1s 1s)
			+ 8m => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_high } { 1s 1s }) => {
					is_ryanpeikou();
					!is_chiitoi();
				}
				({ 2p 2p } { 3p 3p } { 4p 4p } { 6m 6m } { 7m 7m } { 8m 8m } { 1s 1s }) => {
					!is_ryanpeikou();
					is_chiitoi();
				}
			]
			+ 5m => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6m 7m 8m } { anjun 5m 6m 7m ryanmen_low } { 1s 1s }) => {
					!is_ryanpeikou();
					is_iipeikou();
					is_pinfu(tw!(E), tw!(E));
					!is_chiitoi();
				}
			]
		);
	}

	#[test]
	fn ryanpeikou3() {
		test!((2m 2m 3m 3m 4m 4m 4m 4m 7p 8p 8p 9p 9p)
			+ 7p => [
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 7p 8p 9p penchan } { 4m 4m }) => {
					is_ryanpeikou();
					!is_chiitoi();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn chinitsu1() {
		test!((1p 2p 3p 3p 4p 5p 0p 6p 6p 7p 9p 9p 9p)
			+ 3p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { 3p 3p }) => {
					is_chinitsu();
				}
				({ anjun 4p 5p 6p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { anjun 1p 2p 3p penchan } { 3p 3p }) => {
					is_chinitsu();
				}
			]
			+ 6p => [
				({ anjun 1p 2p 3p } { anjun 3p 4p 5p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { 6p 6p }) => {
					is_chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 3p 4p 5p } { ankou 9p 9p 9p } { anjun 0p 6p 7p kanchan } { 6p 6p }) => {
					is_chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=27271
	#[test]
	fn chinitsu2() {
		test!((1p 2p 3p 4p 4p 5p 5p 7p 7p 8p 8p 9p 9p)
			+ 4p => [
				({ anjun 1p 2p 3p } { anjun 7p 8p 9p } { anjun 7p 8p 9p } { ankou 4p 4p 4p shanpon } { 5p 5p }) => {
					is_chinitsu();
				}
			]
			+ 5p => [
				({ anjun 1p 2p 3p } { anjun 7p 8p 9p } { anjun 7p 8p 9p } { ankou 5p 5p 5p shanpon } { 4p 4p }) => {
					is_chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=27271
	#[test]
	fn chinitsu3() {
		test!((2m 3m 4m 5m 5m 6m 6m 6m 7m 7m 8m 9m 9m)
			+ 1m => [
				({ anjun 4m 5m 6m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 1m 2m 3m ryanmen_low } { 9m 9m }) => {
					is_chinitsu();
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 4m 5m 6m ryanmen_low } { 9m 9m }) => {
					is_chinitsu();
				}
				({ anjun 4m 5m 6m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 2m 3m 4m ryanmen_high } { 9m 9m }) => {
					is_chinitsu();
				}
			]
			+ 7m => [
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 5m 6m 7m } { anjun 6m 7m 8m kanchan } { 9m 9m }) => {
					is_chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 5m 6m 7m ryanmen_high } { 9m 9m }) => {
					is_chinitsu();
				}
			]
			+ 8m => [
				({ anjun 2m 3m 4m } { ankou 6m 6m 6m } { anjun 7m 8m 9m } { anjun 7m 8m 9m kanchan } { 5m 5m }) => {
					is_chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=27271
	#[test]
	fn chinitsu4() {
		test!((1s 2s 3s 3s 4s 5s 6s 6s 6s 7s 7s 8s 8s)
			+ 3s => [
				({ anjun 1s 2s 3s } { anjun 4s 5s 6s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 3s 3s }) => {
					is_chinitsu();
				}
				({ anjun 4s 5s 6s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { anjun 1s 2s 3s penchan } { 3s 3s }) => {
					is_chinitsu();
				}
			]
			+ 6s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 6s 6s }) => {
					is_chinitsu();
				}
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_low } { 6s 6s }) => {
					is_chinitsu();
				}
			]
			+ 7s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { ankou 7s 7s 7s shanpon } { 8s 8s }) => {
					is_chinitsu();
				}
			]
			+ 8s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { ankou 8s 8s 8s shanpon } { 7s 7s }) => {
					is_chinitsu();
				}
			]
			+ 9s => [
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 7s 8s 9s ryanmen_high } { 6s 6s }) => {
					is_chinitsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn kokushi_musou1() {
		test!((1m 9m 1s 9s 1p 9p E S W N Wh Wh R)
			+ G => [
				(1m 9m 1s 9s 1p 9p E S W N Wh Wh G R) => {
					is_kokushi_musou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Kokushi_musou&oldid=28089
	#[test]
	fn kokushi_musou2() {
		test!((1m 1p 9p 1s 9s E S W N Wh G G R)
			+ 9m => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G G R) => {
					is_kokushi_musou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Kokushi_musou&oldid=28089
	#[test]
	fn kokushi_musou3() {
		test!((1m 9m 1p 9p 1s 9s E S W N Wh G R)
			+ 1m => [
				(1m 1m 9m 1p 9p 1s 9s E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ 9m => [
				(1m 9m 9m 1p 9p 1s 9s E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ 1p => [
				(1m 9m 1p 1p 9p 1s 9s E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ 9p => [
				(1m 9m 1p 9p 9p 1s 9s E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ 1s => [
				(1m 9m 1p 9p 1s 1s 9s E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ 9s => [
				(1m 9m 1p 9p 1s 9s 9s E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ E => [
				(1m 9m 1p 9p 1s 9s E E S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ S => [
				(1m 9m 1p 9p 1s 9s E S S W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ W => [
				(1m 9m 1p 9p 1s 9s E S W W N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ N => [
				(1m 9m 1p 9p 1s 9s E S W N N Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ Wh => [
				(1m 9m 1p 9p 1s 9s E S W N Wh Wh G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ G => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G G R juusanmen) => {
					is_kokushi_musou();
				}
			]
			+ R => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G R R juusanmen) => {
					is_kokushi_musou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn suuankou1() {
		test!((2m 2m 2m 4p 4p 4p 8m 8m 8m R R S S)
			+ R => [
				({ ankou 2m 2m 2m } { ankou 4p 4p 4p } { ankou 8m 8m 8m } { ankou R R R shanpon } { S S }) => {
					num_suuankou() == 1;
				}
			]
			+ S => [
				({ ankou 2m 2m 2m } { ankou 4p 4p 4p } { ankou 8m 8m 8m } { ankou S S S shanpon } { R R }) => {
					num_suuankou() == 1;
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
					num_suuankou() == 1;
				}
			]
			+ 5p ron => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { minkou 5p 5p 5p shanpon } { 8s 8s }) => {
					num_suuankou() == 0;
					is_toitoi();
					is_sanankou();
				}
			]
			+ 8s => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { ankou 8s 8s 8s shanpon } { 5p 5p }) => {
					num_suuankou() == 1;
				}
			]
			+ 8s ron => [
				({ ankou 6p 6p 6p } { ankou 1s 1s 1s } { ankou G G G } { minkou 8s 8s 8s shanpon } { 5p 5p }) => {
					num_suuankou() == 0;
					is_toitoi();
					is_sanankou();
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
					num_suuankou() == 2;
				}
			]
			+ 9m ron => [
				({ ankou 8p 8p 8p } { ankou 3s 3s 3s } { ankou 4s 4s 4s } { ankou S S S } { 9m 9m }) => {
					num_suuankou() == 2;
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
					num_suuankou() == 2;
				}
			]
			+ 4s => [
				({ ankou 3p 3p 3p } { ankou 7s 7s 7s } { ankan 1s 1s 1s 1s } { anjun 2s 3s 4s ryanmen_high } { 2s 2s }) => {
					num_suuankou() == 0;
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn daisangen1() {
		test!((3m 4m 5m 2s Wh Wh Wh R R R { minkou G G G })
			+ 2s => [
				({ anjun 3m 4m 5m } { ankou Wh Wh Wh } { ankou R R R } { minkou G G G } { 2s 2s }) => {
					is_daisangen();
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
					is_daisangen();
					!is_shousangen();
				}
			]
			+ 3p => [
				({ anjun 4m 5m 6m } { minkou G G G } { minkou R R R } { ankou 3p 3p 3p shanpon } { Wh Wh }) => {
					!is_daisangen();
					is_shousangen();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	//
	// > Shousuushii
	#[test]
	fn suushii1() {
		test!((8m 8m 8m E S S S { minkou W W W } { minkou N N N })
			+ E => [
				({ ankou 8m 8m 8m } { ankou S S S } { minkou W W W } { minkou N N N } { E E }) => {
					is_shousuushii();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	//
	// > Daisuushii
	#[test]
	fn suushii2() {
		test!((5p E E E S S S N N N { minkou W W W })
			+ 5p => [
				({ ankou E E E } { ankou S S S } { ankou N N N } { minkou W W W } { 5p 5p }) => {
					is_daisuushii();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=25800
	#[test]
	fn suushii3() {
		test!((4p 5p 6p E E E S S W W { minkou N N N })
			+ S => [
				({ anjun 4p 5p 6p } { ankou E E E } { minkou N N N } { ankou S S S shanpon } { W W }) => {
					is_shousuushii();
				}
			]
			+ W => [
				({ anjun 4p 5p 6p } { ankou E E E } { minkou N N N } { ankou W W W shanpon } { S S }) => {
					is_shousuushii();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=25800
	#[test]
	fn suushii4() {
		test!((2m E E E W W W N N N { minkou S S S })
			+ 2m => [
				({ ankou E E E } { ankou W W W } { ankou N N N } { minkou S S S } { 2m 2m }) => {
					is_daisuushii();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=25800
	#[test]
	fn suushii5() {
		test!((7s 7s S S N N N { minkou E E E } { minkou W W W })
			+ S => [
				({ ankou N N N } { minkou E E E } { minkou W W W } { ankou S S S shanpon } { 7s 7s }) => {
					is_daisuushii();
					!is_shousuushii();
				}
			]
			+ 7s => [
				({ ankou N N N } { minkou E E E } { minkou W W W } { ankou 7s 7s 7s shanpon } { S S }) => {
					!is_daisuushii();
					is_shousuushii();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn tsuuiisou1() {
		test!((E E E W W Wh Wh { minkou S S S } { minkou G G G })
			+ W => [
				({ ankou E E E } { minkou S S S } { minkou G G G } { ankou W W W shanpon } { Wh Wh }) => {
					is_tsuuiisou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_chinroutou();
				}
			]
			+ Wh => [
				({ ankou E E E } { minkou S S S } { minkou G G G } { ankou Wh Wh Wh shanpon } { W W }) => {
					is_tsuuiisou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tsuuiisou&oldid=25888
	#[test]
	fn tsuuiisou2() {
		test!((E E E S S S G G N N { minkou R R R })
			+ G => [
				({ ankou E E E } { ankou S S S } { minkou R R R } { ankou G G G shanpon } { N N }) => {
					is_tsuuiisou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_chinroutou();
				}
			]
			+ N => [
				({ ankou E E E } { ankou S S S } { minkou R R R } { ankou N N N shanpon } { G G }) => {
					is_tsuuiisou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Tsuuiisou&oldid=25888
	#[test]
	fn tsuuiisou3() {
		test!((E E S S W W N N Wh Wh G G R)
			+ R => [
				({ E E } { S S } { W W } { N N } { Wh Wh } { G G } { R R }) => {
					is_tsuuiisou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_chinroutou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn chinroutou1() {
		test!((1m 1m 1m 9m 9m 9m 1s 1s 9s 9s { minkou 1p 1p 1p })
			+ 1s => [
				({ ankou 1m 1m 1m } { ankou 9m 9m 9m } { minkou 1p 1p 1p } { ankou 1s 1s 1s shanpon } { 9s 9s }) => {
					is_chinroutou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
				}
			]
			+ 9s => [
				({ ankou 1m 1m 1m } { ankou 9m 9m 9m } { minkou 1p 1p 1p } { ankou 9s 9s 9s shanpon } { 1s 1s }) => {
					is_chinroutou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
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
					is_chinroutou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
				}
			]
			+ 9m => [
				({ ankou 1m 1m 1m } { ankou 9p 9p 9p } { minkou 1s 1s 1s } { ankou 9m 9m 9m shanpon } { 1p 1p }) => {
					is_chinroutou();
					!is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn ryuuiisou1() {
		test!((2s 2s 3s 3s 4s 4s 6s 6s 6s 8s 8s G G)
			+ 8s => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou 8s 8s 8s shanpon } { G G }) => {
					is_ryuuiisou();
				}
			]
			+ G => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G shanpon } { 8s 8s }) => {
					is_ryuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=25760
	#[test]
	fn ryuuiisou2() {
		test!((2s 2s 3s 3s 4s 4s 6s 6s 8s 8s G G G)
			+ 6s => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou G G G } { ankou 6s 6s 6s shanpon } { 8s 8s }) => {
					is_ryuuiisou();
				}
			]
			+ 8s => [
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { ankou G G G } { ankou 8s 8s 8s shanpon } { 6s 6s }) => {
					is_ryuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=25760
	#[test]
	fn ryuuiisou3() {
		test!((2s 2s 2s 3s 3s 4s 4s 4s 8s 8s { minkou 6s 6s 6s })
			+ 3s => [
				({ ankou 2s 2s 2s } { ankou 4s 4s 4s } { minkou 6s 6s 6s } { ankou 3s 3s 3s shanpon } { 8s 8s }) => {
					is_ryuuiisou();
				}
				({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { minkou 6s 6s 6s } { anjun 2s 3s 4s kanchan } { 8s 8s }) => {
					is_ryuuiisou();
				}
			]
			+ 8s => [
				({ ankou 2s 2s 2s } { ankou 4s 4s 4s } { minkou 6s 6s 6s } { ankou 8s 8s 8s shanpon } { 3s 3s }) => {
					is_ryuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=25760
	#[test]
	fn ryuuiisou4() {
		test!((2s 3s 4s 4s 4s 6s 6s 6s 8s 8s G G G)
			+ 1s => [
				({ ankou 4s 4s 4s } { ankou 6s 6s 6s } { ankou G G G } { anjun 1s 2s 3s ryanmen_low } { 8s 8s }) => {
					!is_ryuuiisou();
				}
			]
			+ 4s => [
				({ anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G } { ankou 4s 4s 4s shanpon } { 8s 8s }) => {
					is_ryuuiisou();
				}
				({ ankou 4s 4s 4s } { ankou 6s 6s 6s } { ankou G G G } { anjun 2s 3s 4s ryanmen_high } { 8s 8s }) => {
					is_ryuuiisou();
				}
			]
			+ 8s => [
				({ anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G } { ankou 8s 8s 8s shanpon } { 4s 4s }) => {
					is_ryuuiisou();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn chuuren_poutou1() {
		test!((1m 1m 1m 2m 3m 4m 5m 6m 7m 8m 9m 9m 9m)
			+ 1m => [
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_low } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { ankou 1m 1m 1m shanpon } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 2m => [
				({ ankou 1m 1m 1m } { anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 2m 2m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 3m => [
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 3m 4m 5m ryanmen_low } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 1m 2m 3m penchan } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 4m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 4m 5m 6m ryanmen_low } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_high } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 5m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 5m 5m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 6m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 6m 7m 8m ryanmen_low } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 4m 5m 6m ryanmen_high } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 7m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 7m 8m 9m penchan } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 5m 6m 7m ryanmen_high } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 8m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { ankou 9m 9m 9m } { 8m 8m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 9m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { ankou 9m 9m 9m shanpon } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 7m 8m 9m ryanmen_high } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chuuren_poutou&oldid=27609
	#[test]
	fn chuuren_poutou2() {
		test!((1p 1p 1p 2p 3p 4p 5p 5p 7p 8p 9p 9p 9p)
			+ 6p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { ankou 9p 9p 9p } { anjun 6p 7p 8p ryanmen_low } { 5p 5p }) => {
					num_chuuren_poutou() == 1;
				}
			]
			+ 5p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { ankou 5p 5p 5p shanpon } { 9p 9p }) => {
					num_chuuren_poutou() == 0;
				}
			]
			+ 9p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { ankou 9p 9p 9p shanpon } { 5p 5p }) => {
					num_chuuren_poutou() == 0;
				}
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { ankou 9p 9p 9p } { anjun 7p 8p 9p ryanmen_high } { 5p 5p }) => {
					num_chuuren_poutou() == 0;
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Chuuren_poutou&oldid=27609
	#[test]
	fn chuuren_poutou3() {
		test!((1p 1p 1p 2p 3p 4p 5p 6p 7p 8p 9p 9p 9p)
			+ 1p => [
				({ ankou 1p 1p 1p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { anjun 1p 2p 3p ryanmen_low } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { ankou 1p 1p 1p shanpon } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 2p => [
				({ ankou 1p 1p 1p } { anjun 3p 4p 5p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { 2p 2p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 3p => [
				({ anjun 1p 2p 3p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 3p 4p 5p ryanmen_low } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 3p 4p 5p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 1p 2p 3p penchan } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 4p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { anjun 4p 5p 6p ryanmen_low } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1p 1p 1p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { anjun 2p 3p 4p ryanmen_high } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 5p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { 5p 5p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 6p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 6p 7p 8p ryanmen_low } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1p 2p 3p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 4p 5p 6p ryanmen_high } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 7p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 7p 8p 9p penchan } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { anjun 5p 6p 7p ryanmen_high } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 8p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { ankou 9p 9p 9p } { 8p 8p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 9p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { ankou 9p 9p 9p shanpon } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 7p 8p 9p ryanmen_high } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560
	#[test]
	fn suukantsu1() {
		test!((N { minkan 6p 6p 6p 6p } { minkan 2m 2m 2m 2m } { ankan R R R R } { minkan 4s 4s 4s 4s })
			+ N => [
				({ minkan 6p 6p 6p 6p } { minkan 2m 2m 2m 2m } { ankan R R R R } { minkan 4s 4s 4s 4s } { N N }) => {
					is_suukantsu();
				}
			]
		);
	}

	// Ref: https://riichi.wiki/index.php?title=Suukantsu&oldid=25770
	#[test]
	fn suukantsu2() {
		test!((N { ankan 4p 4p 4p 4p } { minkan 1m 1m 1m 1m } { minkan 7s 7s 7s 7s } { ankan G G G G })
			+ N => [
				({ ankan 4p 4p 4p 4p } { minkan 1m 1m 1m 1m } { minkan 7s 7s 7s 7s } { ankan G G G G } { N N }) => {
					is_suukantsu();
				}
			]
		);
	}

	#[test]
	fn chanta_routou() {
		const EXPECTED_TANYAO: (bool, bool, bool, bool, bool, bool, bool) = (true, false, false, false, false, false, false);
		const EXPECTED_CHANTA: (bool, bool, bool, bool, bool, bool, bool) = (false, true, false, false, false, false, false);
		const EXPECTED_HONROUTOU: (bool, bool, bool, bool, bool, bool, bool) = (false, false, true, false, false, false, false);
		const EXPECTED_JUNCHAN: (bool, bool, bool, bool, bool, bool, bool) = (false, false, false, true, false, false, false);
		const EXPECTED_TSUUIISOU: (bool, bool, bool, bool, bool, bool, bool) = (false, false, false, false, true, false, false);
		const EXPECTED_CHINROUTOU: (bool, bool, bool, bool, bool, bool, bool) = (false, false, false, false, false, true, false);
		const EXPECTED_OTHER: (bool, bool, bool, bool, bool, bool, bool) = (false, false, false, false, false, false, true);

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
			let actual = (actual.is_tanyao(), actual.is_chanta(), actual.is_honroutou(), actual.is_junchan(), actual.is_tsuuiisou(), actual.is_chinroutou(), actual.is_other());
			assert_eq!(actual, expected, "{input_lhs:?} | {input_rhs:?} = {actual:?}, expected {expected:?}");
		}
	}

	#[test]
	fn win_with_akadora() {
		test!((1p 2p 3p 3p 3p 4p 5p 6p 6p 7p 9p 9p 9p)
			+ 0p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 0p 6p 7p ryanmen_low } { 3p 3p }) => {
					is_chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 5p 6p 7p } { ankou 9p 9p 9p } { anjun 4p 0p 6p kanchan } { 3p 3p }) => {
					is_chinitsu();
				}
			]
		);

		test!((1p 2p 3p 3p 3p 4p 0p 6p 6p 7p 9p 9p 9p)
			+ 5p => [
				({ anjun 1p 2p 3p } { anjun 4p 0p 6p } { ankou 9p 9p 9p } { anjun 5p 6p 7p ryanmen_low } { 3p 3p }) => {
					is_chinitsu();
				}
				({ anjun 1p 2p 3p } { anjun 0p 6p 7p } { ankou 9p 9p 9p } { anjun 4p 5p 6p kanchan } { 3p 3p }) => {
					is_chinitsu();
				}
			]
		);
	}

	#[test]
	fn scorable_hand_kokushi_musou_display() {
		for (duplicate, expected) in [
			(t!(1m), "1m 1m 9m 1p 9p 1s 9s E S W N Wh G R"),
			(t!(9m), "1m 9m 9m 1p 9p 1s 9s E S W N Wh G R"),
			(t!(1p), "1m 9m 1p 1p 9p 1s 9s E S W N Wh G R"),
			(t!(9p), "1m 9m 1p 9p 9p 1s 9s E S W N Wh G R"),
			(t!(1s), "1m 9m 1p 9p 1s 1s 9s E S W N Wh G R"),
			(t!(9s), "1m 9m 1p 9p 1s 9s 9s E S W N Wh G R"),
			(t!(E), "1m 9m 1p 9p 1s 9s E E S W N Wh G R"),
			(t!(S), "1m 9m 1p 9p 1s 9s E S S W N Wh G R"),
			(t!(W), "1m 9m 1p 9p 1s 9s E S W W N Wh G R"),
			(t!(N), "1m 9m 1p 9p 1s 9s E S W N N Wh G R"),
			(t!(Wh), "1m 9m 1p 9p 1s 9s E S W N Wh Wh G R"),
			(t!(G), "1m 9m 1p 9p 1s 9s E S W N Wh G G R"),
			(t!(R), "1m 9m 1p 9p 1s 9s E S W N Wh G R R"),
		] {
			let hand = ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: false };
			let actual = std::string::ToString::to_string(&hand);
			assert_eq!(actual, expected);

			let expected = std::format!("{expected} juusanmen");
			let hand = ScorableHandKokushiMusou { duplicate, was_juusanmen_wait: true };
			let actual = std::string::ToString::to_string(&hand);
			assert_eq!(actual, expected);
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
