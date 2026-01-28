use crate::{
	ArrayVec,
	CmpIgnoreRed,
	DragonTile,
	HandMeld,
	Number, NumberTileClassified, NumberTile,
	ShunLowTile, SortingNetwork,
	Tile, TsumoOrRon,
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
/// - For `KokushiMusou`, the array of [`Tile`]s really does form a kokushi musou.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive_const(Eq, PartialEq)]
#[derive(Copy, Ord, PartialOrd)]
pub enum ScorableHand {
	/// Regular hand shape containing four melds and one pair.
	Regular(ScorableHandRegular),

	/// Chiitoi hand shape containing seven pairs.
	Chiitoi(ScorableHandChiitoi),

	/// Kokushi musou hand shape containing one of each terminal and honor tile and one duplicate.
	KokushiMusou {
		tiles: [Tile; 14],
		/// The winning tile was a duplicate of one of the other thirteen unique tiles.
		was_juusanmen_wait: bool,
	},
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
#[derive_const(Eq, PartialEq)]
#[derive(Copy, Ord, PartialOrd)]
pub struct ScorableHandRegular {
	pub melds: ([ScorableHandMeld; 3], ScorableHandFourthMeld),
	pub pair: ScorableHandPair,
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
#[derive_const(Eq, PartialEq)]
#[derive(Copy, Ord, PartialOrd)]
pub struct ScorableHandChiitoi(pub [ScorableHandPair; 7]);

/// A single meld inside a [`ScorableHand`].
///
/// Only the lowest tile is held, since that is sufficient to uniquely determine the whole meld.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means that there are not more of any one [`Tile`] than are present in a game.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive_const(Clone)]
#[derive(Copy)]
pub enum ScorableHandMeld {
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

	/// Closed triplet held in hand.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Ankou(Tile),

	/// Open triplet formed by pon.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	Minkou(Tile),

	/// Closed sequence held in hand.
	Anjun { tile: ShunLowTile, has_five_red: bool },

	/// Open sequence formed by chii.
	Minjun { tile: ShunLowTile, has_five_red: bool },
}

/// The fourth meld of a [`ScorableHand::Regular`]. In addition to the content of the meld, this indicates what wait the hand had.
///
/// Only the lowest tile in the meld is held, since that is sufficient to uniquely determine the whole meld.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means:
///
/// - For `Tanki`, the [`ScorableHandMeld`] is itself consistent. See its docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program may have undefined behavior.
#[derive_const(Eq)]
#[derive(Copy)]
pub enum ScorableHandFourthMeld {
	/// This meld was already complete. One of the tiles of the [`ScorableHand::Regular::pair`] was the wait.
	Tanki(ScorableHandMeld),

	/// This meld is a kou and one of its tiles completed the hand.
	///
	/// If one of the tiles in this meld is a `FiveRed`, then the `FiveRed` is held.
	/// Thus if the held tile is a `FiveRed`, the other tiles are assumed to be `Five`s.
	///
	/// Eg 111m => 1m completed the hand.
	Shanpon {
		tile: Tile,
		/// Whether this kou was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a middle wait.
	///
	/// Eg 123m => 2m completed the hand.
	Kanchan {
		tile: ShunLowTile,
		has_five_red: bool,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a one-sided wait.
	///
	/// Eg 123m => 3m completed the hand, 789p => 7p completed the hand.
	Penchan {
		tile: ShunLowTile,
		has_five_red: bool,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a double-sided wait. The lowest number tile (the first tile) completed the hand.
	///
	/// Eg 123m => 1m completed the hand, 234m => 2m completed the hand, 678p => 6p completed the hand.
	RyanmenLow {
		tile: ShunLowTile,
		has_five_red: bool,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a double-sided wait. The highest number tile (the last tile) completed the hand.
	///
	/// Eg 234m => 4m completed the hand, 678p => 8p completed the hand, 789p => 9p completed the hand.
	RyanmenHigh {
		tile: ShunLowTile,
		has_five_red: bool,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},
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
#[derive_const(Eq)]
#[derive(Copy)]
pub struct ScorableHandPair(pub Tile);

assert_size_of!(ScorableHand, 15);
assert_size_of!(ScorableHandRegular, 14);
assert_size_of!(ScorableHandChiitoi, 7);
assert_size_of!(ScorableHandMeld, 3);
assert_size_of!(ScorableHandMeld, 3);
assert_size_of!(ScorableHandFourthMeld, 4);
assert_size_of!(ScorableHandPair, 1);

impl ScorableHand {
	pub(crate) fn for_each_tile(&self, mut f: impl FnMut(Tile)) {
		match self {
			Self::Regular(h) => h.for_each_tile(f),
			Self::Chiitoi(h) => h.for_each_tile(f),
			Self::KokushiMusou { tiles, .. } => for t in tiles { f(*t); },
		}
	}

	fn for_each_unique_tile(&self, mut f: impl FnMut(Tile)) {
		match self {
			Self::Regular(h) => h.for_each_unique_tile(f),
			Self::Chiitoi(h) => h.for_each_unique_tile(f),
			Self::KokushiMusou { tiles, .. } => for t in tiles { f(*t); },
		}
	}

	pub(crate) fn is_menzen(&self) -> bool {
		match self {
			Self::Regular(h) => h.is_menzen(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => true,
		}
	}

	pub(crate) fn chanta_routou(&self) -> ChantaRoutou {
		match *self {
			Self::Regular(h) => h.chanta_routou(),
			Self::Chiitoi(h) => h.chanta_routou(),
			Self::KokushiMusou { .. } => ChantaRoutou::other(),
		}
	}

	pub(crate) fn num_ankou(&self) -> NumAnkou {
		match self {
			Self::Regular(h) => h.num_ankou(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => NumAnkou::Neither,
		}
	}

	pub(crate) fn honchinitsu(&self) -> Honchinitsu {
		if matches!(self, Self::KokushiMusou { .. }) {
			return Honchinitsu::Neither;
		}

		let mut suit = None;
		// 00 => Chinitsu
		// 01 => Honitsu
		// 1x => Neither
		//
		// Start as Chinitsu, then weaken it to Honitsu or Neither.
		let mut result = 0b00;
		self.for_each_unique_tile(|t| {
			if let Ok(t) = NumberTile::try_from(t) {
				if let Some(suit) = suit {
					if suit != t.suit() {
						// Neither
						result |= 0b10;
					}
				}
				else {
					suit = Some(t.suit());
				}
			}
			else {
				// Honitsu
				result |= 0b01;
			}
		});

		if suit.is_some() {
			match result {
				0b00 => Honchinitsu::Chinitsu,
				0b01 => Honchinitsu::Honitsu,
				_ => Honchinitsu::Neither,
			}
		}
		else {
			Honchinitsu::Neither
		}
	}

	#[cfg(test)]
	fn is_pinfu(&self, round_wind: WindTile, seat_wind: WindTile) -> bool {
		match self {
			Self::Regular(h) => h.is_pinfu(round_wind, seat_wind),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_iipeikou(&self) -> bool {
		match self {
			Self::Regular(h) => h.num_peikou() == 1,
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}

	}

	pub(crate) fn is_tanyao(&self) -> bool {
		match self {
			Self::Regular(h) => h.is_tanyao(),
			Self::Chiitoi(h) => h.is_tanyao(),
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn num_wind_yakuhai(&self, wind: WindTile, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		match *self {
			Self::Regular(h) => h.num_wind_yakuhai(wind, round_wind, seat_wind),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => 0,
		}
	}

	#[cfg(test)]
	fn is_dragon_yakuhai(&self, dragon: DragonTile) -> bool {
		match *self {
			Self::Regular(h) => h.is_dragon_yakuhai(dragon),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_chanta(&self) -> bool {
		self.chanta_routou().is_chanta()
	}

	#[cfg(test)]
	fn is_sanshoku_doujun(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_sanshoku_doujun(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_ittsuu(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_ittsuu(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_toitoi(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_toitoi(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_sanankou(&self) -> bool {
		self.num_ankou().is_sanankou()
	}

	#[cfg(test)]
	fn is_sanshoku_doukou(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_sanshoku_doukou(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_sankantsu(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_sankantsu(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	const fn is_chiitoi(&self) -> bool {
		matches!(self, Self::Chiitoi(_))
	}

	#[cfg(test)]
	fn is_honroutou(&self) -> bool {
		self.chanta_routou().is_honroutou()
	}

	#[cfg(test)]
	fn is_shousangen(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_shousangen(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)] fn is_honitsu(&self) -> bool {
		self.honchinitsu().is_honitsu()
	}

	#[cfg(test)]
	fn is_junchan(&self) -> bool {
		self.chanta_routou().is_junchan()
	}

	#[cfg(test)]
	fn is_ryanpeikou(&self) -> bool {
		match self {
			Self::Regular(h) => h.num_peikou() == 2,
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_chinitsu(&self) -> bool {
		self.honchinitsu().is_chinitsu()
	}

	#[cfg(test)]
	const fn is_kokushi_musou(&self) -> bool {
		matches!(self, Self::KokushiMusou { .. })
	}

	#[cfg(test)]
	fn num_suuankou(&self) -> u8 {
		self.num_ankou().num_suuankou()
	}

	#[cfg(test)]
	fn is_daisangen(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_daisangen(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_shousuushii(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_shousuushii(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_daisuushii(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_daisuushii(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn is_tsuuiisou(&self) -> bool {
		self.chanta_routou().is_tsuuiisou()
	}

	#[cfg(test)]
	fn is_chinroutou(&self) -> bool {
		self.chanta_routou().is_chinroutou()
	}

	#[cfg(test)]
	fn is_ryuuiisou(&self) -> bool {
		match self {
			Self::Regular(h) => h.is_ryuuiisou(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	fn num_chuuren_poutou(&self) -> u8 {
		match self {
			Self::Regular(h) => h.num_chuuren_poutou(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => 0,
		}
	}

	#[cfg(test)]
	fn is_suukantsu(&self) -> bool {
		match *self {
			Self::Regular(h) => h.is_suukantsu(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl const Clone for ScorableHand {
	fn clone(&self) -> Self {
		*self
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
			Self::KokushiMusou { tiles: [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14], was_juusanmen_wait: false } =>
				write!(f, "{t1} {t2} {t3} {t4} {t5} {t6} {t7} {t8} {t9} {t10} {t11} {t12} {t13} {t14}"),
			Self::KokushiMusou { tiles: [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14], was_juusanmen_wait: true } =>
				write!(f, "{t1} {t2} {t3} {t4} {t5} {t6} {t7} {t8} {t9} {t10} {t11} {t12} {t13} {t14} juusanmen"),
		}
	}
}

impl ScorableHandRegular {
	pub fn new(mut ms: [ScorableHandMeld; 3], m4: ScorableHandFourthMeld, pair: ScorableHandPair) -> Self {
		let melds = match m4 {
			ScorableHandFourthMeld::Tanki(m4) => {
				let [m1, m2, m3] = ms;
				let mut ms = [m1, m2, m3, m4];
				ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
				let [m1, m2, m3, m4] = ms;
				([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
			},
			m4 => {
				ms.sort_unstable_by_key(ScorableHandMeld::sort_criteria);
				(ms, m4)
			},
		};
		Self { melds, pair }
	}

	fn for_each_tile(&self, mut f: impl FnMut(Tile)) {
		for m in self.melds.0 {
			m.for_each_tile(&mut f);
		}
		self.melds.1.for_each_tile(&mut f);
		self.pair.for_each_tile(f);
	}

	fn for_each_unique_tile(&self, mut f: impl FnMut(Tile)) {
		for m in self.melds.0 {
			m.for_each_unique_tile(&mut f);
		}
		self.melds.1.for_each_unique_tile(&mut f);
		self.pair.for_each_unique_tile(f);
	}

	fn melds(&self) -> impl Iterator<Item = ScorableHandMeld> {
		let Self { melds: (ms, m4), .. } = self;
		ms.iter().copied().chain(core::iter::once((*m4).into()))
	}

	fn is_menzen(&self) -> bool {
		let Self { melds: (ms, m4), .. } = self;
		ms.iter().all(|m| m.is_menzen()) && m4.is_menzen()
	}

	pub(crate) fn num_peikou(&self) -> usize {
		let Self { melds: ([m1, m2, m3], m4), .. } = self;

		// `[2; 27]` packed into two bits per element.
		let mut counts = 0x2AAAAAAAAAAAAA_u64;
		let mut result = 0;

		// Micro-optimization: We want to do the same thing for `m1`, `m2` and `m3`. rustc unrolls the loop, which is good.
		// But rustc fails to notice that the `m1` case will simply update a count of 2 to a count of 1, so it generates the same code for it
		// as the m2 and m3 cases. So we handle `m1` manually.

		match m1 {
			ScorableHandMeld::Ankan(_) |
			ScorableHandMeld::Ankou(_) => (),

			ScorableHandMeld::Anjun { tile, .. } => {
				let offset = *tile as u8 & !0b1;
				counts -= 0b1 << offset;
			},

			ScorableHandMeld::Minkan(_) |
			ScorableHandMeld::Minkou(_) |
			ScorableHandMeld::Minjun { .. } => return 0,
		}

		for m in [m2, m3] {
			match m {
				ScorableHandMeld::Ankan(_) | ScorableHandMeld::Ankou(_) => (),
				ScorableHandMeld::Anjun { tile, .. } => {
					let offset = *tile as u8 & !0b1;
					// Micro-optimization: Although these ops seem more complex than arithmetic, they compile to simple bit extract/clear/invert instructions.
					//
					// This is equivalent to:
					//
					//     let count = (counts >> offset) & 0b11;
					//     if count == 0 { return 0; }
					//     if count == 1 { result += 1; }

					if counts & (0b11_u64 << offset) == 0 {
						// Sanankou or suuankou
						return 0;
					}
					if counts & (0b1_u64 << offset) != 0 {
						result += 1;
					}

					// Micro-optimization: `new_count = count - 1`, but we know that `count` is either 1 or 2.
					//
					//  count | new_count
					// =======+===========
					//   0b01 | 0b00
					//   0b10 | 0b01
					//
					// We could do `counts = (counts ^ (0b1_u64 << offset)) & !(0b1_u64 << (offset + 1))`, which on RV would be three instructions
					// `binv counts, counts, offset; ori offset, offset, 1; bclr counts, counts, offset`. We can do better with
					// `counts -= 0b1_u64 << offset;`, which on RV would be just two instructions
					// `bset temp, zero, offset; sub counts, counts, temp`. (This works because `count > 0`, so the subtraction is guaranteed
					// to not borrow from the left element.)
					//
					// TODO(rustup): That said, rustc insists on compiling it to a longer sequence anyway -
					// `li temp, -1; sll temp, temp, offset; add counts, counts, temp`. As usual, wrapping `1 << offset` in `core::hint::black_box()`
					// makes rustc emit the expected sequence, but inserts a stack store and load of the blackboxed value.
					//
					// Ref: https://github.com/llvm/llvm-project/issues/178588

					counts -= 0b1_u64 << offset;
				},
				ScorableHandMeld::Minkan(_) | ScorableHandMeld::Minkou(_) | ScorableHandMeld::Minjun { .. } => return 0,
			}
		}

		match m4 {
			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(_) | ScorableHandMeld::Ankou(_)) |
			ScorableHandFourthMeld::Shanpon { .. } => (),

			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun { tile, .. }) |
			ScorableHandFourthMeld::Kanchan { tile, .. } |
			ScorableHandFourthMeld::Penchan { tile, .. } |
			ScorableHandFourthMeld::RyanmenLow { tile, .. } |
			ScorableHandFourthMeld::RyanmenHigh { tile, .. } => {
				let offset = *tile as u8 & !0b1;
				if counts & (0b11_u64 << offset) == 0 {
					// Sanankou or suuankou
					return 0;
				}
				if counts & (0b1_u64 << offset) != 0 {
					result += 1;
				}
			},

			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Minkan(_) | ScorableHandMeld::Minkou(_) | ScorableHandMeld::Minjun { .. }) => return 0,
		}

		result
	}

	fn chanta_routou(&self) -> ChantaRoutou {
		self.melds().fold(ChantaRoutou(0), |prev, curr| prev | curr.chanta_routou()) | self.pair.chanta_routou()
	}

	fn is_sanshoku(&self, mut f: impl FnMut(ScorableHandMeld) -> Option<NumberTile>) -> bool {
		const MASK: u32 = 0b000000001_000000001_000000001_u32;

		let mut counts = 0b000000000_000000000_000000000_u32;

		for m in self.melds() {
			let Some(t) = f(m) else { continue; };

			counts |= 0b1 << (t as u8 >> 1);

			let group_offset = t.number().value() - 1;
			if (counts >> group_offset) & MASK == MASK {
				return true;
			}
		}

		false
	}

	fn num_ankou(&self) -> NumAnkou {
		let Self { melds: (ms, m4), .. } = self;
		let mut num_closed_triplets = 0_u8;
		let mut num_closed_quads = 0_u8;
		for m in ms {
			match m {
				ScorableHandMeld::Ankan(_) => num_closed_quads += 1,
				ScorableHandMeld::Ankou(_) => num_closed_triplets += 1,
				_ => (),
			}
		}
		match m4 {
			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(_)) => num_closed_quads += 1,
			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(_)) |
			ScorableHandFourthMeld::Shanpon { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => num_closed_triplets += 1,
			_ => (),
		}
		match num_closed_triplets + num_closed_quads {
			3 => NumAnkou::Sanankou,
			4 => NumAnkou::Suuankou { is_tanki_wait: matches!(m4, ScorableHandFourthMeld::Tanki(_)) },
			_ => NumAnkou::Neither,
		}
	}

	pub(crate) fn is_pinfu(&self, round_wind: WindTile, seat_wind: WindTile) -> bool {
		if let Self { melds: (ms, ScorableHandFourthMeld::RyanmenLow { .. } | ScorableHandFourthMeld::RyanmenHigh { .. }), pair } = self {
			ms.iter().all(|m| matches!(m, ScorableHandMeld::Anjun { .. })) && pair.num_yakuhai(round_wind, seat_wind) == 0
		}
		else {
			false
		}
	}

	fn is_tanyao(&self) -> bool {
		// Micro-optimization: Using `.all(is_tanyao)` and using `&&` to combine the bools generates branches due to the short-circuiting.
		self.melds().fold(true, |prev, curr| prev & curr.is_tanyao()) & self.pair.is_tanyao()
	}

	pub(crate) fn num_wind_yakuhai(&self, wind: WindTile, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		self.melds()
			.map(|m| m.num_wind_yakuhai(wind, round_wind, seat_wind))
			.sum()
	}

	pub(crate) fn is_dragon_yakuhai(&self, dragon: DragonTile) -> bool {
		// Micro-optimization: Using `.any(is_dragon_yakuhai)` and using `||` to combine the bools generates branches due to the short-circuiting.
		self.melds().fold(false, |prev, curr| prev | curr.is_dragon_yakuhai(dragon))
	}

	pub(crate) fn is_sanshoku_doujun(&self) -> bool {
		self.is_sanshoku(|m| {
			let (ScorableHandMeld::Anjun { tile, .. } | ScorableHandMeld::Minjun { tile, .. }) = m else { return None; };
			Some(tile.into())
		})
	}

	pub(crate) fn is_ittsuu(&self) -> bool {
		const MASK: u32 = 0b001001001_u32;

		let mut counts = 0b000000000_000000000_000000000_u32;

		for m in self.melds() {
			let (ScorableHandMeld::Anjun { tile, .. } | ScorableHandMeld::Minjun { tile, .. }) = m else { continue; };

			counts |= 0b1 << (tile as u8 >> 1);

			let group_offset = tile.suit() as u8 * 9;
			if (counts >> group_offset) & MASK == MASK {
				return true;
			}
		}

		false
	}

	pub(crate) fn is_toitoi(&self) -> bool {
		self.melds().all(|m| matches!(
			m,
			ScorableHandMeld::Ankan(_) |
			ScorableHandMeld::Minkan(_) |
			ScorableHandMeld::Ankou(_) |
			ScorableHandMeld::Minkou(_),
		))
	}

	pub(crate) fn is_sanshoku_doukou(&self) -> bool {
		self.is_sanshoku(|m| {
			let (
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t)
			) = m else { return None; };
			let Ok(t) = NumberTile::try_from(t) else { return None; };
			Some(t)
		})
	}

	pub(crate) fn is_sankantsu(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(m, ScorableHandMeld::Ankan(_) | ScorableHandMeld::Minkan(_)))
			.count() == 3
	}

	pub(crate) fn is_shousangen(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(
				m,
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) if DragonTile::try_from(t).is_ok(),
			))
			.count() == 2 &&
			matches!(self.pair, ScorableHandPair(tile) if DragonTile::try_from(tile).is_ok())
	}

	pub(crate) fn is_daisangen(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(
				m,
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) if DragonTile::try_from(t).is_ok(),
			))
			.count() == 3
	}

	pub(crate) fn is_shousuushii(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(
				m,
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) if WindTile::try_from(t).is_ok(),
			))
			.count() == 3 &&
			matches!(self.pair, ScorableHandPair(tile) if WindTile::try_from(tile).is_ok())
	}

	pub(crate) fn is_daisuushii(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(
				m,
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) if WindTile::try_from(t).is_ok(),
			))
			.count() == 4
	}

	#[expect(clippy::unusual_byte_groupings)]
	pub(crate) fn is_ryuuiisou(&self) -> bool {
		// Note: Having G is not required.

		// Micro-optimization: Same trick as `Tile::is_simple`.
		let mut tiles = 0_u64;
		self.for_each_unique_tile(|t| tiles |= 1_u64 << (t as u8 >> 1));
		tiles & !0b010_0000_010101110_000000000_000000000 == 0
	}

	pub(crate) fn num_chuuren_poutou(&self) -> u8 {
		const JUNSEI_HANDS: [JunseiChuurenPoutoutScorableHandRegular; 15] = make_junsei_chuuren_poutou_hands();

		if !self.is_menzen() {
			return 0;
		}

		let mut ts = ArrayVec::<_, 18>::new();
		self.for_each_tile(|t| unsafe { ts.push_unchecked(t); });
		let mut ts = ts.into_iter();

		let mut counts = [3_u8, 1, 1, 1, 1, 1, 1, 1, 3];

		let suit = {
			let Some(t) = ts.next() else { return 0; };
			let Ok(t) = NumberTile::try_from(t) else { return 0; };
			let NumberTileClassified { suit, number } = t.into();
			let count = &mut counts[usize::from(number.value() - 1)];
			*count -= 1;
			suit
		};

		for t in ts {
			let Ok(t) = NumberTile::try_from(t) else { return 0; };
			let NumberTileClassified { suit: suit_, number } = t.into();
			if suit_ != suit { return 0; }
			let count = &mut counts[usize::from(number.value() - 1)];
			*count = count.saturating_sub(1);
		}

		// Micro-optimization: Would be nice to just write `if *counts != [0; 9]`, but rustc implements that for RV by loading and shifting the first eight bytes
		// into a u64, then ORing that with the ninth byte, then comparing that to 0. The shifting part of that is pointless, so we do the ORing manually.
		if counts.iter().fold(0, |prev, &curr| prev | curr) != 0 { 0 }
		else if let Ok(h) = self.try_into() && JUNSEI_HANDS.binary_search(&h).is_ok() { 2 }
		else { 1 }
	}

	pub(crate) fn is_suukantsu(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(m, ScorableHandMeld::Ankan(_) | ScorableHandMeld::Minkan(_)))
			.count() == 4
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl const Clone for ScorableHandRegular {
	fn clone(&self) -> Self {
		*self
	}
}

impl core::fmt::Debug for ScorableHandRegular {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandRegular {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let Self { melds: ([m1, m2, m3], m4), pair } = self;
		write!(f, "{m1} {m2} {m3} {m4} {pair}")
	}
}

impl ScorableHandChiitoi {
	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		for p in self.0 {
			p.for_each_tile(&mut f);
		}
	}

	fn for_each_unique_tile(self, mut f: impl FnMut(Tile)) {
		for p in self.0 {
			p.for_each_tile(&mut f);
		}
	}

	fn chanta_routou(self) -> ChantaRoutou {
		self.0.into_iter().fold(ChantaRoutou(0), |prev, curr| prev | curr.chanta_routou())
	}

	fn is_tanyao(self) -> bool {
		// Micro-optimization: Using `.all(is_tanyao)` and using `&&` to combine the bools generates branches due to the short-circuiting.
		self.0.into_iter().fold(true, |prev, curr| prev & curr.is_tanyao())
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl const Clone for ScorableHandChiitoi {
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
		let Self([p1, ps @ ..])= self;
		p1.fmt(f)?;
		for p in ps {
			write!(f, " {p}")?;
		}
		Ok(())
	}
}

impl ScorableHandMeld {
	/// Construct a `ScorableHandMeld` of kind [`Ankan`] using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid ankan.
	pub const fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		debug_assert!((t1, t2, t3).eq_ignore_red(&(t2, t3, t4)));

		let tile = t1 as u8 | t2 as u8 | t3 as u8 | t4 as u8;
		let tile = unsafe { core::mem::transmute::<u8, Tile>(tile) };
		Self::Ankan(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkan`] using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid minkan.
	pub const fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		debug_assert!((t1, t2, t3).eq_ignore_red(&(t2, t3, t4)));

		let tile = t1 as u8 | t2 as u8 | t3 as u8 | t4 as u8;
		let tile = unsafe { core::mem::transmute::<u8, Tile>(tile) };
		Self::Minkan(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankou`] using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid ankou.
	pub const fn ankou(t1: Tile, t2: Tile, t3: Tile) -> Self {
		debug_assert!((t1, t2).eq_ignore_red(&(t2, t3)));

		let tile = t1 as u8 | t2 as u8 | t3 as u8;
		let tile = unsafe { core::mem::transmute::<u8, Tile>(tile) };
		Self::Ankou(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkou`] using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid minkou.
	pub const fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Self {
		debug_assert!((t1, t2).eq_ignore_red(&(t2, t3)));

		let tile = t1 as u8 | t2 as u8 | t3 as u8;
		let tile = unsafe { core::mem::transmute::<u8, Tile>(tile) };
		Self::Minkou(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Anjun`] using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid anjun.
	pub const fn anjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Self {
		debug_assert!(t1.shun_rest().eq_ignore_red(&(t2, t3)));

		let has_five_red = t1.is_red() || t2.is_red() || t3.is_red();
		let tile = t1.remove_red();
		Self::Anjun { tile, has_five_red }
	}

	/// Construct a `ScorableHandMeld` of kind [`Minjun`] using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid minjun.
	pub const fn minjun(t1: ShunLowTile, t2: NumberTile, t3: NumberTile) -> Self {
		debug_assert!(t1.shun_rest().eq_ignore_red(&(t2, t3)));

		let has_five_red = t1.is_red() || t2.is_red() || t3.is_red();
		let tile = t1.remove_red();
		Self::Minjun { tile, has_five_red }
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

			Self::Anjun { mut tile, has_five_red } |
			Self::Minjun { mut tile, has_five_red } => {
				let (mut t2, mut t3) = tile.shun_rest();
				if has_five_red {
					tile = tile.make_red();
					t2 = t2.make_red();
					t3 = t3.make_red();
				}
				f(tile.into());
				f(t2.into());
				f(t3.into());
			}
		}
	}

	fn for_each_unique_tile(self, mut f: impl FnMut(Tile)) {
		match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => f(t.remove_red()),
			Self::Anjun { tile, .. } |
			Self::Minjun { tile, .. } => {
				let (t2, t3) = tile.shun_rest();
				f(tile.into());
				f(t2.into());
				f(t3.into());
			},
		}
	}

	const fn is_menzen(self) -> bool {
		match self {
			Self::Ankan(_) |
			Self::Ankou(_) |
			Self::Anjun { .. }
				=> true,
			Self::Minkan(_) |
			Self::Minkou(_) |
			Self::Minjun { .. }
				=> false,
		}
	}

	const fn is_tanyao(self) -> bool {
		// Micro-optimization: Same trick as `Tile::is_simple`, except that we're only checking the first tile of the meld.
		// That means for `Anjun` and `Minjun` the first tile must be less than 7.
		let (c, t) = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => (0b0000000_011111110_011111110_011111110_u64, t),
			Self::Anjun { tile, .. } |
			Self::Minjun { tile, .. } => (0b0000000_000111110_000111110_000111110_u64, tile.into()),
		};
		c & (1_u64 << ((t as u8) >> 1)) != 0
	}

	const fn chanta_routou(self) -> ChantaRoutou {
		let (t, is_shun) = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => (t, false),
			Self::Anjun { tile, .. } |
			Self::Minjun { tile, .. } => (tile.into(), true),
		};

		// Micro-optimization: Same trick as `Tile::is_simple`.

		let offset = 1_u64 << (t as u8 >> 1);

		// Micro-optimization: `if is_shun { ... } else { ... } generates a branch on `discriminant(&self) & 0b100 == 0`.
		// Using `select_unpredictable` generate branchless selects (with that same condition) instead.
		core::hint::select_unpredictable(
			is_shun,
			if (0b0000000_001000001_001000001_001000001_u64 & offset) != 0 {
				ChantaRoutou::has_terminals()
			}
			else {
				ChantaRoutou::other()
			},
			if (0b0000000_100000001_100000001_100000001_u64 & offset) != 0 {
				ChantaRoutou::all_terminals()
			}
			else if t >= t!(E) {
				ChantaRoutou::all_honors()
			}
			else {
				ChantaRoutou::other()
			},
		)
	}

	const fn num_wind_yakuhai(self, wind: WindTile, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		let tile = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => t,
			// Micro-optimization: Doing an early `return 0` here generates a test on the discriminant and a branch.
			Self::Anjun { tile, .. } |
			Self::Minjun { tile, .. } => tile.into(),
		};
		let is_wind = tile == wind.into();
		u8::from(is_wind && wind == round_wind) + u8::from(is_wind && wind == seat_wind)
	}

	const fn is_dragon_yakuhai(self, dragon: DragonTile) -> bool {
		let t = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => t,
			// Micro-optimization: Doing a `return false` here generates a test on the discriminant.
			Self::Anjun { tile, .. } |
			Self::Minjun { tile, .. } => tile.into(),
		};
		t == dragon.into()
	}

	/// [9 8 7 6 5 4 3][2 1 0]
	//  [      t      ][  d  ]
	#[expect(clippy::trivially_copy_pass_by_ref)] // Taking `self` as clippy recommends ends up generating loads of all the other bytes and shifts and generally terrible code.
	pub(crate) const fn sort_criteria(&self) -> u16 {
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
		//
		// Lastly, using `(Tile, ScorableHandMeldDiscriminant)` as the comparison key generates individual branches for each byte comparison.
		// So we instead combine them into a `u16` and use that as the comparison key. Note that the tile value component is the raw tile value,
		// ie the final result will differentiate between `Five` and `FiveRed`. This generates simpler code, so most sorts in this library use
		// the result of this function as the sort key. However the `Ord` and `Eq` impls need to treat `Five` and `FiveRed` as equal,
		// so they mask out the LSB of the `Tile` component.

		let t = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => *t,
			Self::Anjun { tile, .. } |
			Self::Minjun { tile, .. } => (*tile).into(),
		};
		let d = ScorableHandMeldDiscriminant::from(self);
		((t as u16) << 3) | (d as u16)
	}
}

impl core::fmt::Debug for ScorableHandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self {
			Self::Ankan(_) => f.write_str("{ ankan ")?,
			Self::Minkan(_) => f.write_str("{ minkan ")?,
			Self::Ankou(_) => f.write_str("{ ankou ")?,
			Self::Minkou(_) => f.write_str("{ minkou ")?,
			Self::Anjun { .. } => f.write_str("{ anjun ")?,
			Self::Minjun { .. } => f.write_str("{ minjun ")?,
		}
		let mut is_ok = true;
		self.for_each_tile(|t| if is_ok && write!(f, "{t} ").is_err() { is_ok = false; });
		if is_ok { f.write_str("}") } else { Err(core::fmt::Error) }
	}
}

impl From<HandMeld> for ScorableHandMeld {
	fn from(meld: HandMeld) -> Self {
		match meld {
			HandMeld::Ankan([t1, t2, t3, t4]) => Self::ankan(t1, t2, t3, t4),
			HandMeld::Minkan([t1, t2, t3, t4]) => Self::minkan(t1, t2, t3, t4),
			HandMeld::Minkou([t1, t2, t3]) => Self::minkou(t1, t2, t3),
			HandMeld::Minjun(mut ts) => {
				SortingNetwork::sort_three(&mut ts);
				let t1 = ts[0].try_into();
				let t1 = unsafe { t1.unwrap_unchecked() };
				Self::minjun(t1, ts[1], ts[2])
			},
		}
	}
}

impl const From<ScorableHandFourthMeld> for ScorableHandMeld {
	fn from(meld: ScorableHandFourthMeld) -> Self {
		// Micro-optimization: Inlining the `tsumo_or_ron` matches into the outer `match` generates a jump table for each `ScorableHandFourthMeld` discriminant.
		// Doing it this way eliminates the jump table, and helps rustc notice the `Min*` discriminant can be formed by adding `tsumo_or_ron` to the `An*` discriminant.

		match meld {
			ScorableHandFourthMeld::Tanki(m) => m,
			ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron } => match tsumo_or_ron {
				TsumoOrRon::Tsumo => Self::Ankou(tile),
				TsumoOrRon::Ron => Self::Minkou(tile),
			},
			ScorableHandFourthMeld::Kanchan { tile, has_five_red, tsumo_or_ron } |
			ScorableHandFourthMeld::Penchan { tile, has_five_red, tsumo_or_ron } |
			ScorableHandFourthMeld::RyanmenLow { tile, has_five_red, tsumo_or_ron } |
			ScorableHandFourthMeld::RyanmenHigh { tile, has_five_red, tsumo_or_ron } => match tsumo_or_ron {
				TsumoOrRon::Tsumo => Self::Anjun { tile, has_five_red },
				TsumoOrRon::Ron => Self::Minjun { tile, has_five_red },
			},
		}
	}
}

impl const Eq for ScorableHandMeld {}

/// `ScorableHandMeld`s differing only in the presence of akadora are considered equal.
impl const Ord for ScorableHandMeld {
	#[expect(clippy::unusual_byte_groupings)]
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		// We want to treat `Five` and `FiveRed`s the same so we set the LSB of each `Tile` field.
		// Masking it out would be clearer, but ORing it is equivalent and generates simpler code.
		let sc = self.sort_criteria() | 0b0000001_000;
		let sc_other = other.sort_criteria() | 0b0000001_000;
		sc.cmp(&sc_other)
	}
}

/// `ScorableHandMeld`s differing only in the presence of akadora are considered equal.
impl const PartialEq for ScorableHandMeld {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

/// `ScorableHandMeld`s differing only in the presence of akadora are considered equal.
impl const PartialOrd for ScorableHandMeld {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[derive(Copy, Debug)]
#[repr(u8)]
enum ScorableHandMeldDiscriminant {
	Ankan = 0,
	Minkan = 1,
	Ankou = 2,
	Minkou = 3,
	Anjun = 4,
	Minjun = 5,
}

impl const From<&ScorableHandMeld> for ScorableHandMeldDiscriminant {
	fn from(m: &ScorableHandMeld) -> Self {
		match m {
			ScorableHandMeld::Ankan(_) => Self::Ankan,
			ScorableHandMeld::Minkan(_) => Self::Minkan,
			ScorableHandMeld::Ankou(_) => Self::Ankou,
			ScorableHandMeld::Minkou(_) => Self::Minkou,
			ScorableHandMeld::Anjun { .. } => Self::Anjun,
			ScorableHandMeld::Minjun { .. } => Self::Minjun,
		}
	}
}

impl ScorableHandFourthMeld {
	/// Construct a `ScorableHandFourthMeld::Shanpon` using the given tiles and `TsumoOrRon` flag.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid ankou.
	pub const fn shanpon(t1: Tile, t2: Tile, t3: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		debug_assert!((t1, t2).eq_ignore_red(&(t2, t3)));

		let tile = t1 as u8 | t2 as u8 | t3 as u8;
		let tile = unsafe { core::mem::transmute::<u8, Tile>(tile) };
		Self::Shanpon { tile, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::Kanchan` using the given tiles and `TsumoOrRon` flag.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid anjun.
	pub const fn kanchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		debug_assert!(t1.shun_rest().eq_ignore_red(&(t2, t3)));

		let has_five_red = t1.is_red() || t2.is_red() || t3.is_red();
		let tile = t1.remove_red();
		Self::Kanchan { tile, has_five_red, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::Penchan` using the given tiles and `TsumoOrRon` flag.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid anjun.
	pub const fn penchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		debug_assert!(t1.shun_rest().eq_ignore_red(&(t2, t3)));

		let has_five_red = t1.is_red() || t2.is_red() || t3.is_red();
		let tile = t1.remove_red();
		Self::Penchan { tile, has_five_red, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::RyanmenLow` using the given tiles and `TsumoOrRon` flag.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid anjun.
	pub const fn ryanmen_low(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		debug_assert!(t1.shun_rest().eq_ignore_red(&(t2, t3)));

		let has_five_red = t1.is_red() || t2.is_red() || t3.is_red();
		let tile = t1.remove_red();
		Self::RyanmenLow { tile, has_five_red, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::RyanmenHigh` using the given tiles and `TsumoOrRon` flag.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid anjun.
	pub const fn ryanmen_high(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		debug_assert!(t1.shun_rest().eq_ignore_red(&(t2, t3)));

		let has_five_red = t1.is_red() || t2.is_red() || t3.is_red();
		let tile = t1.remove_red();
		Self::RyanmenHigh { tile, has_five_red, tsumo_or_ron }
	}

	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		match self {
			Self::Tanki(m) => m.for_each_tile(f),

			Self::Shanpon { tile, .. } => {
				let t_rest = tile.remove_red();
				f(t_rest);
				f(t_rest);
				f(tile);
			},

			Self::Kanchan { mut tile, has_five_red, .. } |
			Self::Penchan { mut tile, has_five_red, .. } |
			Self::RyanmenLow { mut tile, has_five_red, .. } |
			Self::RyanmenHigh { mut tile, has_five_red, .. } => {
				let (mut t2, mut t3) = tile.shun_rest();
				if has_five_red {
					tile = tile.make_red();
					t2 = t2.make_red();
					t3 = t3.make_red();
				}
				f(tile.into());
				f(t2.into());
				f(t3.into());
			},
		}
	}

	fn for_each_unique_tile(self, mut f: impl FnMut(Tile)) {
		match self {
			Self::Tanki(m) => m.for_each_unique_tile(f),

			Self::Shanpon { tile, .. } => f(tile.remove_red()),

			Self::Kanchan { tile, .. } |
			Self::Penchan { tile, .. } |
			Self::RyanmenLow { tile, .. } |
			Self::RyanmenHigh { tile, .. } => {
				let (t2, t3) = tile.shun_rest();
				f(tile.into());
				f(t2.into());
				f(t3.into());
			},
		}
	}

	const fn is_menzen(self) -> bool {
		match self {
			Self::Tanki(m) => m.is_menzen(),
			Self::Shanpon { .. } |
			Self::Kanchan { .. } |
			Self::Penchan { .. } |
			Self::RyanmenLow { .. } |
			Self::RyanmenHigh { .. } => true,
		}
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl const Clone for ScorableHandFourthMeld {
	fn clone(&self) -> Self {
		*self
	}
}

impl core::fmt::Debug for ScorableHandFourthMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		core::fmt::Display::fmt(self, f)
	}
}

impl core::fmt::Display for ScorableHandFourthMeld {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let suffix = match self {
			Self::Tanki(m4) => return write!(f, "{m4}"),
			Self::Shanpon { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => { f.write_str("{ ankou ")?; "shanpon" },
			Self::Shanpon { tsumo_or_ron: TsumoOrRon::Ron, .. } => { f.write_str("{ minkou ")?; "shanpon" },
			Self::Kanchan { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => { f.write_str("{ anjun ")?; "kanchan" },
			Self::Kanchan { tsumo_or_ron: TsumoOrRon::Ron, .. } => { f.write_str("{ minjun ")?; "kanchan" },
			Self::Penchan { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => { f.write_str("{ anjun ")?; "penchan" },
			Self::Penchan { tsumo_or_ron: TsumoOrRon::Ron, .. } => { f.write_str("{ minjun ")?; "penchan" },
			Self::RyanmenLow { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => { f.write_str("{ anjun ")?; "ryanmen_low" },
			Self::RyanmenLow { tsumo_or_ron: TsumoOrRon::Ron, .. } => { f.write_str("{ minjun ")?; "ryanmen_low" },
			Self::RyanmenHigh { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => { f.write_str("{ anjun ")?; "ryanmen_high" },
			Self::RyanmenHigh { tsumo_or_ron: TsumoOrRon::Ron, .. } => { f.write_str("{ minjun ")?; "ryanmen_high" },
		};
		let mut is_ok = true;
		ScorableHandMeld::from(*self).for_each_tile(|t| if is_ok && write!(f, "{t} ").is_err() { is_ok = false; });
		if is_ok { write!(f, "{suffix} }}") } else { Err(core::fmt::Error) }
	}
}

impl const Ord for ScorableHandFourthMeld {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		// Just like `ScorableHandMeld::cmp`, this sorts by the first tile and then by the type of wait. See the comment in that function for details.
		// However one difference to that function is that `Tanki` is sorted before the other waits.

		// Doesn't get inlined by default and generates panicking code for the `Tanki` arm. Inlining allows rustc to notice the `Tanki` arm is unreachable and elide it.
		#[inline]
		#[expect(clippy::trivially_copy_pass_by_ref)]
		const fn discriminant(m: &ScorableHandFourthMeld) -> u8 {
			// Values are based on the ones that rustc infers for `ScorableHandFourthMeld`. Specifically `Tanki`'s field discriminants are inlined into `ScorableHandFourthMeld`,
			// so `Shanpon` starts from 0x6. This allows the value of `ScorableHandFourthMeldDiscriminant` to be calculated by shifting the `ScorableHandFourthMeld` discriminant
			// and ORing the `TsumoOrRon` field.
			#[expect(clippy::identity_op)]
			match *m {
				ScorableHandFourthMeld::Tanki(_) => unreachable!(),
				ScorableHandFourthMeld::Shanpon { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => (0x06 << 1) | 0b0,
				ScorableHandFourthMeld::Shanpon { tsumo_or_ron: TsumoOrRon::Ron, .. } => (0x06 << 1) | 0b1,
				ScorableHandFourthMeld::Kanchan { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => (0x07 << 1) | 0b0,
				ScorableHandFourthMeld::Kanchan { tsumo_or_ron: TsumoOrRon::Ron, .. } => (0x07 << 1) | 0b1,
				ScorableHandFourthMeld::Penchan { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => (0x08 << 1) | 0b0,
				ScorableHandFourthMeld::Penchan { tsumo_or_ron: TsumoOrRon::Ron, .. } => (0x08 << 1) | 0b1,
				ScorableHandFourthMeld::RyanmenLow { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => (0x09 << 1) | 0b0,
				ScorableHandFourthMeld::RyanmenLow { tsumo_or_ron: TsumoOrRon::Ron, .. } => (0x09 << 1) | 0b1,
				ScorableHandFourthMeld::RyanmenHigh { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => (0x0A << 1) | 0b0,
				ScorableHandFourthMeld::RyanmenHigh { tsumo_or_ron: TsumoOrRon::Ron, .. } => (0x0A << 1) | 0b1,
			}
		}

		let (d, d_other) = match (self, other) {
			(Self::Tanki(m1), Self::Tanki(m2)) => return m1.cmp(m2),
			(Self::Tanki(_), _) => return core::cmp::Ordering::Less,
			(_, Self::Tanki(_)) => return core::cmp::Ordering::Greater,
			(this, other) => (discriminant(this), discriminant(other)),
		};
		let t = match *self {
			Self::Tanki(_) => unreachable!(),
			Self::Shanpon { tile, .. } => tile,
			Self::Kanchan { tile, .. } |
			Self::Penchan { tile, .. } |
			Self::RyanmenLow { tile, .. } |
			Self::RyanmenHigh { tile, .. } => tile.into(),
		};
		let t_other = match *other {
			Self::Tanki(_) => unreachable!(),
			Self::Shanpon { tile, .. } => tile,
			Self::Kanchan { tile, .. } |
			Self::Penchan { tile, .. } |
			Self::RyanmenLow { tile, .. } |
			Self::RyanmenHigh { tile, .. } => tile.into(),
		};
		let sc = (((t as u16) & !0b1) << 4) | u16::from(d);
		let sc_other = (((t_other as u16) & !0b1) << 4) | u16::from(d_other);
		sc.cmp(&sc_other)
	}
}

impl const PartialEq for ScorableHandFourthMeld {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

impl const PartialOrd for ScorableHandFourthMeld {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl ScorableHandPair {
	/// Construct a `ScorableHandPair` using the given tiles.
	///
	/// For the sake of efficiency, this function does not check that the given tiles form a valid pair.
	pub fn new(t1: Tile, t2: Tile) -> Self {
		let tile = if t1.is_red() { t1 } else { t2 };
		Self(tile)
	}

	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		f(self.0.remove_red());
		f(self.0);
	}

	fn for_each_unique_tile(self, mut f: impl FnMut(Tile)) {
		f(self.0.remove_red());
	}

	const fn is_tanyao(self) -> bool {
		self.0.is_simple()
	}

	const fn chanta_routou(self) -> ChantaRoutou {
		// Micro-optimization: Same trick as `Tile::is_simple`.

		let offset = 1_u64 << (self.0 as u8 >> 1);

		if 0b0000000_100000001_100000001_100000001_u64 & offset != 0 {
			ChantaRoutou::all_terminals()
		}
		else if self.0 >= t!(E) {
			ChantaRoutou::all_honors()
		}
		else {
			ChantaRoutou::other()
		}
	}

	pub(crate) const fn num_yakuhai(self, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		(u8::from(self.0 == round_wind.into()) + u8::from(self.0 == seat_wind.into())) | u8::from(self.0 >= t!(Wh))
	}
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
impl const Clone for ScorableHandPair {
	fn clone(&self) -> Self {
		*self
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
		self.for_each_tile(|t| if is_ok && write!(f, "{t} ").is_err() { is_ok = false; });
		if is_ok { f.write_str("}") } else { Err(core::fmt::Error) }
	}
}

impl const Ord for ScorableHandPair {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		self.0.cmp_ignore_red(&other.0)
	}
}

impl const PartialEq for ScorableHandPair {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), core::cmp::Ordering::Equal)
	}
}

impl const PartialOrd for ScorableHandPair {
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
#[derive_const(Clone)]
#[derive(Copy)]
pub(crate) struct ChantaRoutou(u8);

#[expect(clippy::unusual_byte_groupings)]
impl ChantaRoutou {
	const fn has_terminals() -> Self { Self(0b0_0_11) }
	const fn all_terminals() -> Self { Self(0b0_0_01) }
	const fn all_honors() -> Self { Self(0b0_1_00) }
	const fn other() -> Self { Self(0b1_0_00) }

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
	const fn is_other(self) -> bool { self.0 >= 0b1_0_00 }
}

impl const core::ops::BitOr for ChantaRoutou {
	type Output = ChantaRoutou;

	fn bitor(self, rhs: Self) -> Self::Output {
		Self(self.0 | rhs.0)
	}
}

#[expect(clippy::unusual_byte_groupings)]
impl core::fmt::Debug for ChantaRoutou {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str(match self.0 {
			0b0_1_11 => "Chanta",
			0b0_1_01 => "Honroutou",
			0b0_0_11 => "Junchan",
			0b0_1_00 => "Tsuuiisou",
			0b0_0_01 => "Chinroutou",
			0b1_0_00.. => "Other",
			_ => unsafe { core::hint::unreachable_unchecked(); },
		})
	}
}

#[derive_const(Clone)]
#[derive(Copy)]
pub(crate) enum NumAnkou {
	Neither,
	Sanankou,
	Suuankou { is_tanki_wait: bool },
}

impl NumAnkou {
	pub(crate) const fn is_sanankou(self) -> bool {
		matches!(self, Self::Sanankou)
	}

	pub(crate) const fn num_suuankou(self) -> u8 {
		if let Self::Suuankou { is_tanki_wait } = self {
			1 + u8::from(is_tanki_wait)
		}
		else {
			0
		}
	}
}

#[derive_const(Clone)]
#[derive(Copy)]
pub(crate) enum Honchinitsu {
	Chinitsu = 0,
	Honitsu = 1,
	Neither = 2,
}

impl Honchinitsu {
	pub(crate) const fn is_honitsu(self) -> bool {
		matches!(self, Self::Honitsu)
	}

	pub(crate) const fn is_chinitsu(self) -> bool {
		matches!(self, Self::Chinitsu)
	}
}

#[derive_const(Clone, Eq, Ord, PartialEq, PartialOrd)]
#[derive(Copy, Debug)]
#[repr(transparent)]
struct JunseiChuurenPoutoutScorableHandRegular(u32);

#[repr(u8)]
enum JunseiChuurenPoutoutScorableHandMeld {
	Ankou = 0,
	Anjun = 1,
}

#[repr(u8)]
enum JunseiChuurenPoutoutScorableHandFourthMeld {
	TankiAnkou = 0,
	Shanpon = 1,
	Penchan = 2,
	RyanmenLow = 3,
	RyanmenHigh = 4,
}

impl JunseiChuurenPoutoutScorableHandRegular {
	const fn new([n1, n2, n3, n4, n5]: [Number; 5], [m1, m2, m3]: [JunseiChuurenPoutoutScorableHandMeld; 3], m4: JunseiChuurenPoutoutScorableHandFourthMeld) -> Self {
		let inner =
			(u32::from(n1.value() - 1) << 22) |
			(u32::from(n2.value() - 1) << 18) |
			(u32::from(n3.value() - 1) << 14) |
			(u32::from(n4.value() - 1) << 10) |
			(u32::from(n5.value() - 1) << 6) |
			((m1 as u32) << 5) |
			((m2 as u32) << 4) |
			((m3 as u32) << 3) |
			(m4 as u32);
		Self(inner)
	}

	fn new_from_tiles(ts: [NumberTile; 5], ms: [JunseiChuurenPoutoutScorableHandMeld; 3], m4: JunseiChuurenPoutoutScorableHandFourthMeld) -> Self {
		let ns = unsafe { NumberTile::unchecked_numbers_assume_suit(ts) };
		Self::new(ns, ms, m4)
	}
}

impl TryFrom<&'_ ScorableHandRegular> for JunseiChuurenPoutoutScorableHandRegular {
	type Error = ();

	fn try_from(h: &ScorableHandRegular) -> Result<Self, Self::Error> {
		fn convert_meld(m: ScorableHandMeld) -> Result<(NumberTile, JunseiChuurenPoutoutScorableHandMeld), ()> {
			// Micro-optimization: An early `return Err(())` for the `Ankan` and `Minkan` arms causes the whole `match` to generate multiple branches.
			// This formulation generates branchless code.
			let (t, m) = match m {
				ScorableHandMeld::Ankou(t) => (t, Some(JunseiChuurenPoutoutScorableHandMeld::Ankou)),

				ScorableHandMeld::Anjun { tile, .. } => (tile.into(), Some(JunseiChuurenPoutoutScorableHandMeld::Anjun)),

				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Minkou(t) => (t, None),

				ScorableHandMeld::Minjun { tile, .. } => (tile.into(), None),
			};
			let m = m.ok_or(())?;
			let t = NumberTile::try_from(t)?;
			Ok((t, m))
		}

		fn convert_fourth_meld(m: ScorableHandFourthMeld) -> Result<(NumberTile, JunseiChuurenPoutoutScorableHandFourthMeld), ()> {
			// Micro-optimization: Same trick as `convert_meld`.
			let (t, m) = match m {
				ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(t)) => (t, Some(JunseiChuurenPoutoutScorableHandFourthMeld::TankiAnkou)),

				ScorableHandFourthMeld::Shanpon { tile, .. } => (tile, Some(JunseiChuurenPoutoutScorableHandFourthMeld::Shanpon)),

				ScorableHandFourthMeld::Penchan { tile, .. } => (tile.into(), Some(JunseiChuurenPoutoutScorableHandFourthMeld::Penchan)),

				ScorableHandFourthMeld::RyanmenLow { tile, .. } => (tile.into(), Some(JunseiChuurenPoutoutScorableHandFourthMeld::RyanmenLow)),

				ScorableHandFourthMeld::RyanmenHigh { tile, .. } => (tile.into(), Some(JunseiChuurenPoutoutScorableHandFourthMeld::RyanmenHigh)),

				ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(tile) | ScorableHandMeld::Minkan(tile) | ScorableHandMeld::Minkou(tile)) => (tile, None),

				ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun { tile, .. } | ScorableHandMeld::Minjun { tile, .. }) |
				ScorableHandFourthMeld::Kanchan { tile, .. } => (tile.into(), None),
			};
			let m = m.ok_or(())?;
			let t = NumberTile::try_from(t)?;
			Ok((t, m))
		}

		let ScorableHandRegular { melds: ([m1, m2, m3], m4), pair } = h;
		let (t1, m1) = convert_meld(*m1)?;
		let (t2, m2) = convert_meld(*m2)?;
		let (t3, m3) = convert_meld(*m3)?;
		let (t4, m4) = convert_fourth_meld(*m4)?;
		let t5 = NumberTile::try_from(pair.0)?;
		Ok(Self::new_from_tiles([t1, t2, t3, t4, t5], [m1, m2, m3], m4))
	}
}

// It's easier to hard-code all the hands and check for equality rather than write code to inspect every meld and pair.
const fn make_junsei_chuuren_poutou_hands() -> [JunseiChuurenPoutoutScorableHandRegular; 15] {
	use {
		JunseiChuurenPoutoutScorableHandMeld::{Anjun, Ankou},
		JunseiChuurenPoutoutScorableHandFourthMeld::{Penchan, RyanmenHigh, RyanmenLow, Shanpon, TankiAnkou},
	};

	let n1 = Number::One;
	let n2 = Number::Two;
	let n3 = Number::Three;
	let n4 = Number::Four;
	let n5 = Number::Five;
	let n6 = Number::Six;
	let n7 = Number::Seven;
	let n8 = Number::Eight;
	let n9 = Number::Nine;
	// The array is manually sorted so that the caller can use `.binary_search()`. The sort order is tested in the `make_junsei_chuuren_poutou_hands_sorted` test.
	//
	// TODO(rustup): If `<[_]>::sort_unstable_by_key(): const fn`, etc happen, then this won't need to be manually sorted.
	[
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n2, n5, n7, n9], [Ankou, Anjun, Anjun], Penchan),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n2, n5, n9, n8], [Ankou, Anjun, Anjun], TankiAnkou),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n2, n6, n9, n5], [Ankou, Anjun, Anjun], TankiAnkou),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n2, n7, n4, n9], [Ankou, Anjun, Anjun], RyanmenLow),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n2, n7, n5, n9], [Ankou, Anjun, Anjun], RyanmenHigh),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n3, n6, n9, n2], [Ankou, Anjun, Anjun], TankiAnkou),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n4, n7, n1, n9], [Ankou, Anjun, Anjun], RyanmenLow),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n4, n7, n1, n9], [Anjun, Anjun, Anjun], Shanpon),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n4, n7, n2, n9], [Ankou, Anjun, Anjun], RyanmenHigh),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n4, n7, n9, n1], [Anjun, Anjun, Anjun], Shanpon),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n4, n9, n6, n1], [Anjun, Anjun, Ankou], RyanmenLow),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n4, n9, n7, n1], [Anjun, Anjun, Ankou], RyanmenHigh),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n6, n9, n3, n1], [Anjun, Anjun, Ankou], RyanmenLow),
		JunseiChuurenPoutoutScorableHandRegular::new([n1, n6, n9, n4, n1], [Anjun, Anjun, Ankou], RyanmenHigh),
		JunseiChuurenPoutoutScorableHandRegular::new([n3, n6, n9, n1, n1], [Anjun, Anjun, Ankou], Penchan),
	]
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use super::*;

	#[test]
	fn num_yakuhai() {
		for &t in Tile::each(crate::GameType::Yonma) {
			let p = ScorableHandPair::new(t, t);
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

	#[test]
	fn pinfu() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744

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

		// > Every tile group is a sequence, but this hand is open.
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

		// > The pair of east winds invalidates pinfu if won by the dealer or by any player in the east round.
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

		// > The pair wait invalidates pinfu.
		test!((1p 2p 3p 4p 5p 6p 7m 8m 9m 5s 6s 7s 3m)
			+ 3m => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { anjun 7m 8m 9m } { anjun 5s 6s 7s } { 3m 3m }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);

		// > The dragon pair invalidates pinfu.
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

		// > The kanchan wait invalidates pinfu.
		test!((1m 2m 3m 2s 3s 4s 7s 9s 2p 2p 5p 6p 7p)
			+ 8s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 7s 8s 9s kanchan } { 2p 2p }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);

		// > This hand does qualify for pinfu if won by 6-pin or 9-pin.
		// > However, if won by 3-pin, it is considered to have won with a 3-pin tanki (specifically, it has a nobetan wait on 3-6p).
		// > Note that 6-pin could be considered a tanki wait, but still qualifies for pinfu, because the han increase takes precedence over tanki's extra fu.
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

	#[test]
	fn iipeikou() {
		// Ref: https://mahjongsoul.game.yo-star.com/?paipu=260122-eb23da04-3945-40c2-b154-a6f55eb1ed1c_a909728900

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

	#[test]
	fn tanyao() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Tanyao&oldid=27461

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

	#[test]
	fn yakuhai() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Yakuhai&oldid=25808

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

	#[test]
	fn chanta() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Chanta&oldid=27929

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

	#[test]
	fn sanshoku_doujun() {
		// Ref: https://riichi.wiki/index.php?title=Sanshoku_doujun&oldid=27023

		test!((1m 2m 3m 1p 2p 3p 1s 2s 3s 6s 7s 8s E)
			+ E => [
				({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { anjun 6s 7s 8s } { E E }) => {
					is_sanshoku_doujun();
				}
			]
		);

		test!((1m 2m 3m 1p 2p 3p 1s 2s 3s E { minjun 6s 7s 8s })
			+ E => [
				({ anjun 1m 2m 3m } { anjun 1p 2p 3p } { anjun 1s 2s 3s } { minjun 6s 7s 8s } { E E }) => {
					is_sanshoku_doujun();
				}
			]
		);

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

	#[test]
	fn ittsuu() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

	#[test]
	fn toitoi() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Toitoihou&oldid=27883

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

	#[test]
	fn sanankou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Sanankou&oldid=27270

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

		// > Note: A tsumo results in the suuankou yakuman.

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

	#[test]
	fn sanshoku_doukou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((4m 5m 6m 7m 7m 7m 5s { minkou 7s 7s 7s } { minkou 7p 7p 7p })
			+ 5s => [
				({ anjun 4m 5m 6m } { ankou 7m 7m 7m } { minkou 7s 7s 7s } { minkou 7p 7p 7p } { 5s 5s }) => {
					is_sanshoku_doukou();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Sanshoku_doukou&oldid=27024

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

		test!((3m 3m 3m 3s 3s 4s 5s 6s 6s 6s { minkou 3p 3p 3p })
			+ 3s => [
				({ ankou 3m 3m 3m } { anjun 3s 4s 5s } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
				({ ankou 3m 3m 3m } { anjun 4s 5s 6s } { minkou 3p 3p 3p } { ankou 3s 3s 3s shanpon } { 6s 6s }) => {
					is_sanshoku_doukou();
				}
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 3s 4s 5s ryanmen_low } { 3s 3s }) => {
					!is_sanshoku_doukou();
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

	#[test]
	fn sankantsu() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((4m 5m 6m 2s { minkan 6p 6p 6p 6p } { minkan 9s 9s 9s 9s } { ankan 5s 5s 5s 5s })
			+ 2s => [
				({ anjun 4m 5m 6m } { minkan 6p 6p 6p 6p } { minkan 9s 9s 9s 9s } { ankan 5s 5s 5s 5s } { 2s 2s }) => {
					is_sankantsu();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Sankantsu&oldid=27944

		test!((3p 4p 5p E { minkan 4m 4m 4m 4m } { ankan 8s 8s 8s 8s } { minkan 2p 2p 2p 2p })
			+ E => [
				({ anjun 3p 4p 5p } { minkan 4m 4m 4m 4m } { ankan 8s 8s 8s 8s } { minkan 2p 2p 2p 2p } { E E }) => {
					is_sankantsu();
				}
			]
		);
	}

	#[test]
	fn chiitoi() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((1p 1p 7p 7p W W 5m 5m S 4s 4s Wh Wh)
			+ S => [
				({ 1p 1p } { 7p 7p } { W W } { 5m 5m } { S S } { 4s 4s } { Wh Wh }) => {
					is_chiitoi();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Chiitoitsu&oldid=27947

		test!((1m 1m 3m 3m 4m 5p 5p 2s 2s W W Wh Wh)
			+ 4m => [
				({ 1m 1m } { 3m 3m } { 4m 4m } { 5p 5p } { 2s 2s } { W W } { Wh Wh }) => {
					is_chiitoi();
				}
			]
		);
	}

	#[test]
	fn honroutou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727

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

	#[test]
	fn shousangen() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371

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

		test!((2p 3p 4p 3s 4s G G { minkou Wh Wh Wh } { minkou R R R })
			+ 5s ron => [
				({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_high } { G G }) => {
					is_shousangen();
				}
			]
		);

		test!((5m 6m 7m 1s 2s 3s G G R R { minkou Wh Wh Wh })
			+ G ron => [
				({ anjun 5m 6m 7m } { anjun 1s 2s 3s }  { minkou Wh Wh Wh }{ minkou G G G shanpon } { R R }) => {
					is_shousangen();
				}
			]
		);
	}

	#[test]
	fn honitsu() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Honiisou&oldid=28041

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

	#[test]
	fn junchan() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Junchantaiyaochuu&oldid=27930

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

	#[test]
	fn ryanpeikou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Ryanpeikou&oldid=27706

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

		test!((2m 2m 3m 3m 4m 4m 4m 4m 7p 8p 8p 9p 9p)
			+ 7p => [
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 7p 8p 9p penchan } { 4m 4m }) => {
					is_ryanpeikou();
					!is_chiitoi();
				}
			]
		);
	}

	#[test]
	fn chinitsu() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Chiniisou&oldid=27271

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

	#[test]
	fn kokushi_musou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((1m 9m 1s 9s 1p 9p E S W N Wh Wh R)
			+ G => [
				(1m 9m 1s 9s 1p 9p E S W N Wh Wh G R) => {
					is_kokushi_musou();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Kokushi_musou&oldid=28089

		test!((1m 1p 9p 1s 9s E S W N Wh G G R)
			+ 9m => [
				(1m 9m 1p 9p 1s 9s E S W N Wh G G R) => {
					is_kokushi_musou();
				}
			]
		);

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

	#[test]
	fn suuankou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Suuankou&oldid=25891

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

	#[test]
	fn daisangen() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((3m 4m 5m 2s Wh Wh Wh R R R { minkou G G G })
			+ 2s => [
				({ anjun 3m 4m 5m } { ankou Wh Wh Wh } { ankou R R R } { minkou G G G } { 2s 2s }) => {
					is_daisangen();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Daisangen&oldid=27370

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

	#[test]
	fn suushii() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((8m 8m 8m E S S S { minkou W W W } { minkou N N N })
			+ E => [
				({ ankou 8m 8m 8m } { ankou S S S } { minkou W W W } { minkou N N N } { E E }) => {
					is_shousuushii();
				}
			]
		);

		test!((5p E E E S S S N N N { minkou W W W })
			+ 5p => [
				({ ankou E E E } { ankou S S S } { ankou N N N } { minkou W W W } { 5p 5p }) => {
					is_daisuushii();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Suushiihou&oldid=25800

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

		test!((2m E E E W W W N N N { minkou S S S })
			+ 2m => [
				({ ankou E E E } { ankou W W W } { ankou N N N } { minkou S S S } { 2m 2m }) => {
					is_daisuushii();
				}
			]
		);

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

	#[test]
	fn tsuuiisou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Tsuuiisou&oldid=25888

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

	#[test]
	fn chinroutou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Chinroutou&oldid=27235

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

	#[test]
	fn ryuuiisou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Ryuuiisou&oldid=25760

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

	#[test]
	fn chuuren_poutou() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

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

		// Ref: https://riichi.wiki/index.php?title=Chuuren_poutou&oldid=27609

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

	#[test]
	fn suukantsu() {
		// Ref: https://riichi.wiki/index.php?title=List_of_yaku&oldid=27560

		test!((N { minkan 6p 6p 6p 6p } { minkan 2m 2m 2m 2m } { ankan R R R R } { minkan 4s 4s 4s 4s })
			+ N => [
				({ minkan 6p 6p 6p 6p } { minkan 2m 2m 2m 2m } { ankan R R R R } { minkan 4s 4s 4s 4s } { N N }) => {
					is_suukantsu();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Suukantsu&oldid=25770

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
		const EXPECTED_CHANTA: (bool, bool, bool, bool, bool, bool) = (true, false, false, false, false, false);
		const EXPECTED_HONROUTOU: (bool, bool, bool, bool, bool, bool) = (false, true, false, false, false, false);
		const EXPECTED_JUNCHAN: (bool, bool, bool, bool, bool, bool) = (false, false, true, false, false, false);
		const EXPECTED_TSUUIISOU: (bool, bool, bool, bool, bool, bool) = (false, false, false, true, false, false);
		const EXPECTED_CHINROUTOU: (bool, bool, bool, bool, bool, bool) = (false, false, false, false, true, false);
		const EXPECTED_OTHER: (bool, bool, bool, bool, bool, bool) = (false, false, false, false, false, true);

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
			(ChantaRoutou::other(), ChantaRoutou::other(), EXPECTED_OTHER),
		] {
			let actual = input_lhs | input_rhs;
			let actual = (actual.is_chanta(), actual.is_honroutou(), actual.is_junchan(), actual.is_tsuuiisou(), actual.is_chinroutou(), actual.is_other());
			assert_eq!(actual, expected, "{input_lhs:?} | {input_rhs:?} = {actual:?}, expected {expected:?}");
		}
	}

	#[test]
	fn make_junsei_chuuren_poutou_hands_sorted() {
		let expected = {
			let suit = crate::NumberSuit::Man;
			let n1 = NumberTile::from(NumberTileClassified { suit, number: Number::One });
			let s1 = n1.try_into().unwrap();
			let t1 = n1.into();
			let n2 = NumberTile::from(NumberTileClassified { suit, number: Number::Two });
			let s2 = n2.try_into().unwrap();
			let t2 = n2.into();
			let n3 = NumberTile::from(NumberTileClassified { suit, number: Number::Three });
			let s3 = n3.try_into().unwrap();
			let n4 = NumberTile::from(NumberTileClassified { suit, number: Number::Four });
			let s4 = n4.try_into().unwrap();
			let n5 = NumberTile::from(NumberTileClassified { suit, number: Number::Five });
			let s5 = n5.try_into().unwrap();
			let t5 = n5.into();
			let n6 = NumberTile::from(NumberTileClassified { suit, number: Number::Six });
			let s6 = n6.try_into().unwrap();
			let n7 = NumberTile::from(NumberTileClassified { suit, number: Number::Seven });
			let s7 = n7.try_into().unwrap();
			let n8 = NumberTile::from(NumberTileClassified { suit, number: Number::Eight });
			let t8 = n8.into();
			let n9 = NumberTile::from(NumberTileClassified { suit, number: Number::Nine });
			let t9 = n9.into();
			// 1 and 9 can be a ryanmen or shanpon hand, for two possible hands each.
			// 2, 5 and 8 can be a tanki hand, for one possible hand each.
			// 3 and 7 can be a ryanmen or penchan hand, for two possible hands each.
			// 4 and 6 can be one of two ryanmen hands, for two possible hands each.
			let expected = [
				// 1
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s4, n5, n6), ScorableHandMeld::anjun(s7, n8, n9)], ScorableHandFourthMeld::ryanmen_low(s1, n2, n3, TsumoOrRon::Tsumo), ScorableHandPair::new(t9, t9)),
				ScorableHandRegular::new([ScorableHandMeld::anjun(s1, n2, n3), ScorableHandMeld::anjun(s4, n5, n6), ScorableHandMeld::anjun(s7, n8, n9)], ScorableHandFourthMeld::shanpon(t1, t1, t1, TsumoOrRon::Tsumo), ScorableHandPair::new(t9, t9)),
				// 2
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s3, n4, n5), ScorableHandMeld::anjun(s6, n7, n8)], ScorableHandFourthMeld::Tanki(ScorableHandMeld::ankou(t9, t9, t9)), ScorableHandPair::new(t2, t2)),
				// 3
				ScorableHandRegular::new([ScorableHandMeld::anjun(s1, n2, n3), ScorableHandMeld::anjun(s6, n7, n8), ScorableHandMeld::ankou(t9, t9, t9)], ScorableHandFourthMeld::ryanmen_low(s3, n4, n5, TsumoOrRon::Tsumo), ScorableHandPair::new(t1, t1)),
				ScorableHandRegular::new([ScorableHandMeld::anjun(s3, n4, n5), ScorableHandMeld::anjun(s6, n7, n8), ScorableHandMeld::ankou(t9, t9, t9)], ScorableHandFourthMeld::penchan(s1, n2, n3, TsumoOrRon::Tsumo), ScorableHandPair::new(t1, t1)),
				// 4
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s2, n3, n4), ScorableHandMeld::anjun(s7, n8, n9)], ScorableHandFourthMeld::ryanmen_low(s4, n5, n6, TsumoOrRon::Tsumo), ScorableHandPair::new(t9, t9)),
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s4, n5, n6), ScorableHandMeld::anjun(s7, n8, n9)], ScorableHandFourthMeld::ryanmen_high(s2, n3, n4, TsumoOrRon::Tsumo), ScorableHandPair::new(t9, t9)),
				// 5
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s2, n3, n4), ScorableHandMeld::anjun(s6, n7, n8)], ScorableHandFourthMeld::Tanki(ScorableHandMeld::ankou(t9, t9, t9)), ScorableHandPair::new(t5, t5)),
				// 6
				ScorableHandRegular::new([ScorableHandMeld::anjun(s1, n2, n3), ScorableHandMeld::anjun(s4, n5, n6), ScorableHandMeld::ankou(t9, t9, t9)], ScorableHandFourthMeld::ryanmen_low(s6, n7, n8, TsumoOrRon::Tsumo), ScorableHandPair::new(t1, t1)),
				ScorableHandRegular::new([ScorableHandMeld::anjun(s1, n2, n3), ScorableHandMeld::anjun(s6, n7, n8), ScorableHandMeld::ankou(t9, t9, t9)], ScorableHandFourthMeld::ryanmen_high(s4, n5, n6, TsumoOrRon::Tsumo), ScorableHandPair::new(t1, t1)),
				// 7
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s2, n3, n4), ScorableHandMeld::anjun(s7, n8, n9)], ScorableHandFourthMeld::ryanmen_high(s5, n6, n7, TsumoOrRon::Tsumo), ScorableHandPair::new(t9, t9)),
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s2, n3, n4), ScorableHandMeld::anjun(s5, n6, n7)], ScorableHandFourthMeld::penchan(s7, n8, n9, TsumoOrRon::Tsumo), ScorableHandPair::new(t9, t9)),
				// 8
				ScorableHandRegular::new([ScorableHandMeld::ankou(t1, t1, t1), ScorableHandMeld::anjun(s2, n3, n4), ScorableHandMeld::anjun(s5, n6, n7)], ScorableHandFourthMeld::Tanki(ScorableHandMeld::ankou(t9, t9, t9)), ScorableHandPair::new(t8, t8)),
				// 9
				ScorableHandRegular::new([ScorableHandMeld::anjun(s1, n2, n3), ScorableHandMeld::anjun(s4, n5, n6), ScorableHandMeld::ankou(t9, t9, t9)], ScorableHandFourthMeld::ryanmen_high(s7, n8, n9, TsumoOrRon::Tsumo), ScorableHandPair::new(t1, t1)),
				ScorableHandRegular::new([ScorableHandMeld::anjun(s1, n2, n3), ScorableHandMeld::anjun(s4, n5, n6), ScorableHandMeld::anjun(s7, n8, n9)], ScorableHandFourthMeld::shanpon(t9, t9, t9, TsumoOrRon::Tsumo), ScorableHandPair::new(t1, t1)),
			];
			let mut expected = expected.map(|h| (&h).try_into().unwrap());
			expected.sort_unstable();
			expected
		};
		let actual = make_junsei_chuuren_poutou_hands();
		assert_eq!(actual, expected);
	}
}
