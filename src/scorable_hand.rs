use crate::{
	CmpIgnoreRed,
	DragonTile,
	HandMeld,
	Number, NumberSuit, NumberTileClassified, NumberTile,
	ShunLowNumber, ShunLowTile, ShunLowTileAndHasFiveRed, SortingNetwork,
	Tile, Tile27Set, Tile34Set, TsumoOrRon,
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
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ScorableHandChiitoi(pub [ScorableHandPair; 7]);

/// Kokushi musou hand shape containing one of each terminal and honor tile and one duplicate.
///
/// This type expects that its variant data is consistent. This means that the  `duplicate` tile is valid for a kokushi musou hand.
///
/// If this expectation is violated, the program may have undefined behavior.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct ScorableHandKokushiMusou {
	pub duplicate: Tile,
	pub was_juusanmen_wait: bool,
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
#[repr(align(2))] // See comment in `ScorableHandMeldSortCriteria::new`.
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
	Anjun(ShunLowTileAndHasFiveRed),

	/// Open sequence formed by chii.
	Minjun(ShunLowTileAndHasFiveRed),
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
#[derive(Clone, Copy, Eq)]
pub enum ScorableHandFourthMeld {
	/// This meld was already complete. One of the tiles of the [`ScorableHandRegular::pair`] was the wait.
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
		tile: ShunLowTileAndHasFiveRed,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a one-sided wait.
	///
	/// Eg 123m => 3m completed the hand, 789p => 7p completed the hand.
	Penchan {
		tile: ShunLowTileAndHasFiveRed,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a double-sided wait. The lowest number tile (the first tile) completed the hand.
	///
	/// Eg 123m => 1m completed the hand, 234m => 2m completed the hand, 678p => 6p completed the hand.
	RyanmenLow {
		tile: ShunLowTileAndHasFiveRed,
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a double-sided wait. The highest number tile (the last tile) completed the hand.
	///
	/// Eg 234m => 4m completed the hand, 678p => 8p completed the hand, 789p => 9p completed the hand.
	RyanmenHigh {
		tile: ShunLowTileAndHasFiveRed,
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

	pub(crate) fn is_menzen(&self) -> bool {
		match self {
			Self::Regular(h) => h.is_menzen(),
			Self::Chiitoi(_) |
			Self::KokushiMusou(_) => true,
		}
	}

	pub(crate) fn chanta_routou(&self) -> ChantaRoutou {
		match *self {
			Self::Regular(h) => h.chanta_routou(),
			Self::Chiitoi(h) => h.chanta_routou(),
			Self::KokushiMusou(_) => ChantaRoutou::other(),
		}
	}

	pub(crate) fn num_ankou(&self) -> NumAnkou {
		match self {
			Self::Regular(h) => h.num_ankou(),
			Self::Chiitoi(_) |
			Self::KokushiMusou(_) => NumAnkou::Neither,
		}
	}

	pub(crate) fn honchinitsu(&self) -> Honchinitsu {
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

		match self {
			Self::Regular(h @ ScorableHandRegular { pair, .. }) => {
				for m in h.melds() {
					let t = match m {
						ScorableHandMeld::Ankan(t) |
						ScorableHandMeld::Minkan(t) |
						ScorableHandMeld::Ankou(t) |
						ScorableHandMeld::Minkou(t) => t as u8,
						ScorableHandMeld::Anjun(t) |
						ScorableHandMeld::Minjun(t) => t as u8,
					};
					inner(&mut result, &mut suit, t);
				}
				inner(&mut result, &mut suit, pair.0 as u8);
			},

			Self::Chiitoi(ScorableHandChiitoi(ps)) =>
				for ScorableHandPair(t) in ps {
					inner(&mut result, &mut suit, *t as u8);
				},

			Self::KokushiMusou(_) => return Honchinitsu::neither(),
		}

		// suit.is_none() => Neither
		result += u8::from(suit.is_none()) << 1;

		Honchinitsu(result)
	}

	pub(crate) fn is_tanyao(&self) -> bool {
		match self {
			Self::Regular(h) => h.is_tanyao(),
			Self::Chiitoi(h) => h.is_tanyao(),
			Self::KokushiMusou(_) => false,
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
		let melds = match md {
			ScorableHandFourthMeld::Tanki(md) => {
				let mut ms = [ma, mb, mc, md];
				SortingNetwork::sort(&mut ms);
				let [m1, m2, m3, m4] = ms;
				([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
			},
			m4 => {
				let mut m123 = [ma, mb, mc];
				SortingNetwork::sort(&mut m123);
				(m123, m4)
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

	fn melds(&self) -> impl Iterator<Item = ScorableHandMeld> {
		let Self { melds: (m123, m4), .. } = self;
		m123.iter().copied().chain(core::iter::once((*m4).into()))
	}

	fn is_menzen(&self) -> bool {
		let Self { melds: (m123, m4), .. } = self;
		m123.iter().all(|m| m.is_menzen()) && m4.is_menzen()
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

			ScorableHandMeld::Anjun(t) => {
				let offset = t.remove_red() as u8;
				counts -= 0b1 << offset;
			},

			ScorableHandMeld::Minkan(_) |
			ScorableHandMeld::Minkou(_) |
			ScorableHandMeld::Minjun(_) => return 0,
		}

		for m in [m2, m3] {
			match m {
				ScorableHandMeld::Ankan(_) | ScorableHandMeld::Ankou(_) => (),
				ScorableHandMeld::Anjun(t) => {
					let offset = t.remove_red() as u8;
					let count = (counts >> offset) & 0b11;
					if count == 0 {
						// Sanankou or suuankou
						return 0;
					}
					// Micro-optimization: This is equivalent to `result += usize::from(count == 1);` but that generates
					// a comparison to `1` which is verbose (`addi -1; snez; add` on RV and similar on x86_64),
					// whereas this generates a simple AND and ADD.
					if count & 0b1 != 0 {
						result += 1;
					}

					// TODO(rustup): rustc on RV insists on compiling this to a longer-than-necessary sequence
					// `li temp, -1; sll temp, temp, offset; add counts, counts, temp` instead of the shorter
					// `bset temp, zero, offset; sub counts, counts, temp`.
					//
					// Ref: https://github.com/llvm/llvm-project/issues/178588
					#[cfg(all(target_arch = "riscv64", target_feature = "zbs"))]
					unsafe {
						core::arch::asm!(
							"bset {temp}, zero, {offset}",
							"sub {counts}, {counts}, {temp}",
							offset = in(reg) offset,
							counts = inout(reg) counts,
							temp = lateout(reg) _,
							options(nomem, nostack, pure),
						);
					}
					#[cfg(not(all(target_arch = "riscv64", target_feature = "zbs")))]
					{
						counts -= 0b1 << offset;
					}
				},
				ScorableHandMeld::Minkan(_) | ScorableHandMeld::Minkou(_) | ScorableHandMeld::Minjun(_) => return 0,
			}
		}

		let t = match m4 {
			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(_) | ScorableHandMeld::Ankou(_)) |
			ScorableHandFourthMeld::Shanpon { .. } => None,

			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun(tile)) |
			ScorableHandFourthMeld::Kanchan { tile, .. } |
			ScorableHandFourthMeld::Penchan { tile, .. } |
			ScorableHandFourthMeld::RyanmenLow { tile, .. } |
			ScorableHandFourthMeld::RyanmenHigh { tile, .. } => Some(tile),

			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Minkan(_) | ScorableHandMeld::Minkou(_) | ScorableHandMeld::Minjun(_)) => return 0,
		};
		if let Some(t) = t {
			let offset = t.remove_red() as u8;
			if counts & (0b11 << offset) == 0 {
				// Sanankou or suuankou
				return 0;
			}
			if counts & (0b1 << offset) != 0 {
				result += 1;
			}
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
		let Self { melds: (m123, m4), .. } = self;
		let mut num_ankan = 0_u8;
		let mut num_ankou = 0_u8;
		for m in m123 {
			match m {
				ScorableHandMeld::Ankan(_) => num_ankan += 1,
				ScorableHandMeld::Ankou(_) => num_ankou += 1,
				_ => (),
			}
		}
		match m4 {
			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(_)) => num_ankan += 1,
			ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(_)) |
			ScorableHandFourthMeld::Shanpon { tsumo_or_ron: TsumoOrRon::Tsumo, .. } => num_ankou += 1,
			_ => (),
		}
		match num_ankan + num_ankou {
			3 => NumAnkou::Sanankou,
			4 => NumAnkou::Suuankou { is_tanki_wait: matches!(m4, ScorableHandFourthMeld::Tanki(_)) },
			_ => NumAnkou::Neither,
		}
	}

	pub(crate) fn suushii_sangen(&self) -> SuushiiSangen {
		let mut num_wind_melds = 0;
		let mut num_dragon_melds = 0;
		for m in self.melds() {
			let t = match m {
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) => t as u8,
				ScorableHandMeld::Anjun(t) |
				ScorableHandMeld::Minjun(t) => t as u8,
			};
			// SAFETY: If `t` is in the range of wind or dragon tiles, it must have been from the `*kan` or `*kou` variants,
			// in which case it was a valid `Tile` and thus meets the safety requirement of `try_from_raw`.
			num_wind_melds += u8::from((unsafe { WindTile::try_from_raw(t) }).is_ok());
			num_dragon_melds += u8::from((unsafe { DragonTile::try_from_raw(t) }).is_ok());
		}

		let pair = {
			let t = self.pair.0 as u8;
			let pair = 2 - u8::from(t < t!(Wh) as u8) - u8::from(t < t!(E) as u8);
			unsafe { core::mem::transmute::<u8, WindOrDragon>(pair) }
		};

		SuushiiSangen { num_wind_melds, num_dragon_melds, pair }
	}

	pub(crate) fn is_pinfu(&self, round_wind: WindTile, seat_wind: WindTile) -> bool {
		if let Self { melds: (m123, ScorableHandFourthMeld::RyanmenLow { .. } | ScorableHandFourthMeld::RyanmenHigh { .. }), pair } = self {
			m123.iter().all(|m| matches!(m, ScorableHandMeld::Anjun(_))) && pair.num_yakuhai(round_wind, seat_wind) == 0
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
			let (ScorableHandMeld::Anjun(t) | ScorableHandMeld::Minjun(t)) = m else { return None; };
			Some(t.remove_red().into())
		})
	}

	pub(crate) fn is_ittsuu(&self) -> bool {
		const MASK: u32 = 0b001001001_u32;

		let mut counts = 0b000000000_000000000_000000000_u32;

		for m in self.melds() {
			let (ScorableHandMeld::Anjun(t) | ScorableHandMeld::Minjun(t)) = m else { continue; };
			let t = t.remove_red();

			counts |= 0b1 << (t as u8 >> 1);

			let group_offset = t.suit() as u8 * 9;
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
			let t = NumberTile::try_from(t).ok()?;
			Some(t)
		})
	}

	pub(crate) fn is_sankantsu(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(m, ScorableHandMeld::Ankan(_) | ScorableHandMeld::Minkan(_)))
			.count() == 3
	}

	#[inline(never)]
	pub(crate) fn is_ryuuiisou(&self) -> bool {
		// Note: Having G is not required.

		const KOU_KAN_PAIR_VALID: Tile34Set = t34set! { 2s, 3s, 4s, 6s, 8s, G };
		const SHUN_VALID: Tile34Set = t34set! { 2s };

		let mut is_valid = true;
		for m in self.melds() {
			let (set, t) = match m {
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) => (&KOU_KAN_PAIR_VALID, t),
				ScorableHandMeld::Anjun(t) |
				ScorableHandMeld::Minjun(t) => (&SHUN_VALID, Tile::from(t.remove_red())),
			};
			is_valid &= set.contains(t);
		}
		is_valid &= KOU_KAN_PAIR_VALID.contains(self.pair.0);
		is_valid
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

			match m4 {
				ScorableHandFourthMeld::Tanki(
					ScorableHandMeld::Ankan(_) |
					ScorableHandMeld::Minkan(_) |
					ScorableHandMeld::Minkou(_) |
					ScorableHandMeld::Minjun(_),
				) => return None,

				ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(t)) => {
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

				ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun(t)) => {
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

				ScorableHandFourthMeld::Shanpon { tile, .. } => {
					{
						let t = NumberTile::try_from(tile).ok()?;
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

				ScorableHandFourthMeld::Kanchan { tile, .. } => {
					{
						let t = tile.remove_red();
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

				ScorableHandFourthMeld::Penchan { tile, .. } => {
					{
						let t = tile.remove_red();
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

				ScorableHandFourthMeld::RyanmenLow { tile, .. } => {
					{
						let t = tile.remove_red();
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

				ScorableHandFourthMeld::RyanmenHigh { tile, .. } => {
					{
						let t = tile.remove_red();

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

		let Self { melds: ([m1, m2, m3], m4), pair } = self;

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

		let Some((old1, old2, old3, old4, new)) = fourth_meld_and_pair_old_and_new_tiles(*m4, *pair, suit_expected) else { return 0; };
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

	pub(crate) fn is_suukantsu(&self) -> bool {
		self.melds()
			.filter(|&m| matches!(m, ScorableHandMeld::Ankan(_) | ScorableHandMeld::Minkan(_)))
			.count() == 4
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

	fn chanta_routou(self) -> ChantaRoutou {
		self.0.into_iter().fold(ChantaRoutou(0), |prev, curr| prev | curr.chanta_routou())
	}

	fn is_tanyao(self) -> bool {
		// Micro-optimization: Using `.all(is_tanyao)` and using `&&` to combine the bools generates branches due to the short-circuiting.
		self.0.into_iter().fold(true, |prev, curr| prev & curr.is_tanyao())
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
		t!(1m).fmt(f)?;
		if self.duplicate == t!(1m) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(9m))?;
		if self.duplicate == t!(9m) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(1p))?;
		if self.duplicate == t!(1p) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(9p))?;
		if self.duplicate == t!(9p) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(1s))?;
		if self.duplicate == t!(1s) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(9s))?;
		if self.duplicate == t!(9s) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(E))?;
		if self.duplicate == t!(E) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(S))?;
		if self.duplicate == t!(S) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(W))?;
		if self.duplicate == t!(W) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(N))?;
		if self.duplicate == t!(N) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(Wh))?;
		if self.duplicate == t!(Wh) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(G))?;
		if self.duplicate == t!(G) { write!(f, " {}", self.duplicate)?; }
		write!(f, " {}", t!(R))?;
		if self.duplicate == t!(R) { write!(f, " {}", self.duplicate)?; }
		if self.was_juusanmen_wait { f.write_str(" juusanmen")?; }
		Ok(())
	}
}

impl ScorableHandMeld {
	/// Construct a `ScorableHandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub fn ankan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let tile = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Ankan(tile))
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankan`](Self::Ankan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub unsafe fn ankan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let tile = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Ankan(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`, `None` otherwise.
	pub fn minkan(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Option<Self> {
		let tile = Tile::kan_representative(t1, t2, t3, t4)?;
		Some(Self::Minkan(tile))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkan`](Self::Minkan) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2, t3].eq_ignore_red(&[t2, t3, t4])`.
	pub unsafe fn minkan_unchecked(t1: Tile, t2: Tile, t3: Tile, t4: Tile) -> Self {
		let tile = unsafe { Tile::kan_representative_unchecked(t1, t2, t3, t4) };
		Self::Minkan(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankou`](Self::Ankou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub fn ankou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let tile = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Ankou(tile))
	}

	/// Construct a `ScorableHandMeld` of kind [`Ankou`](Self::Ankou) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn ankou_unchecked(t1: Tile, t2: Tile, t3: Tile) -> Self {
		let tile = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Ankou(tile)
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub fn minkou(t1: Tile, t2: Tile, t3: Tile) -> Option<Self> {
		let tile = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Minkou(tile))
	}

	/// Construct a `ScorableHandMeld` of kind [`Minkou`](Self::Minkou) using the given tiles.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn minkou_unchecked(t1: Tile, t2: Tile, t3: Tile) -> Self {
		let tile = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Minkou(tile)
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

	const fn is_tanyao(self) -> bool {
		// First tile of a tanyao shun cannot be 7 since that shun would contain a 9.
		const SHUN_SIMPLES: Tile27Set = t27set! {
			2m, 3m, 4m, 5m, 6m,
			2p, 3p, 4p, 5p, 6p,
			2s, 3s, 4s, 5s, 6s,
		};

		match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => t.is_simple(),
			Self::Anjun(t) |
			Self::Minjun(t) => SHUN_SIMPLES.contains(NumberTile::const_from_slt(t.remove_red())),
		}
	}

	fn chanta_routou(self) -> ChantaRoutou {
		const SHUN_TERMINALS: Tile34Set = t34set! { 1m, 7m, 1p, 7p, 1s, 7s };
		const KOU_KAN_TERMINALS: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };
		const KOU_KAN_HONORS: Tile34Set = t34set! { E, S, W, G, N, Wh, G, R };

		let (t, is_shun) = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => (t, false),
			Self::Anjun(t) |
			Self::Minjun(t) => (t.remove_red().into(), true),
		};

		// Micro-optimization: `if is_shun { ... } else { ... } generates a branch on `discriminant(&self) & 0b100 == 0`.
		// Using `select_unpredictable` generate branchless selects (with that same condition) instead.
		core::hint::select_unpredictable(
			is_shun,
			if SHUN_TERMINALS.contains(t) {
				ChantaRoutou::has_terminals()
			}
			else {
				ChantaRoutou::other()
			},
			if KOU_KAN_TERMINALS.contains(t) {
				ChantaRoutou::all_terminals()
			}
			else if KOU_KAN_HONORS.contains(t) {
				ChantaRoutou::all_honors()
			}
			else {
				ChantaRoutou::other()
			},
		)
	}

	fn num_wind_yakuhai(self, wind: WindTile, round_wind: WindTile, seat_wind: WindTile) -> u8 {
		let tile = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => t,
			// Micro-optimization: Doing an early `return 0` here generates a test on the discriminant and a branch.
			Self::Anjun(t) |
			Self::Minjun(t) => t.remove_red().into(),
		};
		let is_wind = tile == wind.into();
		u8::from(is_wind && wind == round_wind) + u8::from(is_wind && wind == seat_wind)
	}

	fn is_dragon_yakuhai(self, dragon: DragonTile) -> bool {
		let t = match self {
			Self::Ankan(t) |
			Self::Minkan(t) |
			Self::Ankou(t) |
			Self::Minkou(t) => t,
			// Micro-optimization: Doing a `return false` here generates a test on the discriminant.
			Self::Anjun(t) |
			Self::Minjun(t) => t.remove_red().into(),
		};
		t == dragon.into()
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
			Self::Anjun(_) => f.write_str("{ anjun ")?,
			Self::Minjun(_) => f.write_str("{ minjun ")?,
		}
		let mut is_ok = true;
		self.for_each_tile(|t| if is_ok && write!(f, "{t} ").is_err() { is_ok = false; });
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

impl From<ScorableHandFourthMeld> for ScorableHandMeld {
	fn from(meld: ScorableHandFourthMeld) -> Self {
		// Micro-optimization: Inlining the `tsumo_or_ron` matches into the outer `match` generates a jump table for each `ScorableHandFourthMeld` discriminant.
		// Doing it this way eliminates the jump table, and helps rustc notice the `Min*` discriminant can be formed by adding `tsumo_or_ron` to the `An*` discriminant.

		match meld {
			ScorableHandFourthMeld::Tanki(m) => m,
			ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron } => match tsumo_or_ron {
				TsumoOrRon::Tsumo => Self::Ankou(tile),
				TsumoOrRon::Ron => Self::Minkou(tile),
			},
			ScorableHandFourthMeld::Kanchan { tile, tsumo_or_ron } |
			ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron } |
			ScorableHandFourthMeld::RyanmenLow { tile, tsumo_or_ron } |
			ScorableHandFourthMeld::RyanmenHigh { tile, tsumo_or_ron } => match tsumo_or_ron {
				TsumoOrRon::Tsumo => Self::Anjun(tile),
				TsumoOrRon::Ron => Self::Minjun(tile),
			},
		}
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
		//
		// Lastly, using `(Tile, u8)` as the comparison key generates individual branches for each byte comparison.
		// So we instead combine them into a `u16` and use that as the comparison key. Note that the tile value component is the raw tile value,
		// ie the final result will differentiate between `Five` and `FiveRed`. This generates simpler code, so most sorts in this library use
		// the result of this function as the sort key. However the `Ord` and `Eq` impls need to treat `Five` and `FiveRed` as equal,
		// so they mask out the LSB of the `Tile` component.

		let t = match m {
			ScorableHandMeld::Ankan(t) |
			ScorableHandMeld::Minkan(t) |
			ScorableHandMeld::Ankou(t) |
			ScorableHandMeld::Minkou(t) => *t as u16,
			ScorableHandMeld::Anjun(t) |
			ScorableHandMeld::Minjun(t) => *t as u16,
		};

		// Neither `core::intrinsics::discriminant_value` nor `core::mem::discrinimant` is easy to use for this use case, so we generate the discriminant manually.
		// The former produces an `isize` which works for us, but requires `feature(core_intrinsics)` which will never be stabilized,
		// especially since the latter is meant to be its stable equivalent. The latter returns an opaque value that effectively wraps the same `isize`,
		// but libcore considers it UB to `transmute` it into `isize`.
		//
		// Another way would be to mark `Self` as `#[repr(C, u8)]` and assign explicit discriminants, but this ends up disabling niches,
		// and it's nice to not have to give up on that.
		//
		// So this manual implementation is the best we can do. The values are chosen to match what rustc generates, which is sufficient for rustc to notice that
		// it can just load the byte at `m` instead of needing to calculate anything. It is possible rustc chooses different values for the discriminants one day
		// which would then require calculation to convert to the values of this `match`, but at least that will just be a deoptimization, not UB.
		let d = match m {
			ScorableHandMeld::Ankan(_) => 0,
			ScorableHandMeld::Minkan(_) => 1,
			ScorableHandMeld::Ankou(_) => 2,
			ScorableHandMeld::Minkou(_) => 3,
			ScorableHandMeld::Anjun(_) => 4,
			ScorableHandMeld::Minjun(_) => 5,
		};

		// `d` is only 3b long, so we could do `(t << 3) | d`. On RV this would compile to two `lbu`s and one `sh3add`.
		// On x86_64 this would compile to two `movzx byte ptr`s and one `lea [d + t * 8]`.
		//
		// But by doing `(t << 8) | d` and marking `ScorableHandMeld` as `#[repr(align(2))]`, this ends up compiling to a single `u16` load on LE architectures,
		// including both x86_64 and RV. It would do that on x86_64 even if `ScorableHandMeld` wasn't `repr(align(2))`, because LLVM assumes that
		// unaligned loads on x86_64 are fast, but on RV it would fall back to doing two `lbu`s, so the `repr(align(2))` is required.
		//
		// Sorting / deduping `ScorableHandMeld` is hot enough that it's worth optimizing like this.
		let inner = (t << 8) | d;
		Self(inner)
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
	/// Construct a `ScorableHandFourthMeld::Shanpon` using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if `[t1, t2].eq_ignore_red(&[t2, t3])`, `None` otherwise.
	pub fn shanpon(t1: Tile, t2: Tile, t3: Tile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let tile = Tile::kou_representative(t1, t2, t3)?;
		Some(Self::Shanpon { tile, tsumo_or_ron })
	}

	/// Construct a `ScorableHandFourthMeld::Shanpon` using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// Requires `[t1, t2].eq_ignore_red(&[t2, t3])`.
	pub unsafe fn shanpon_unchecked(t1: Tile, t2: Tile, t3: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		let tile = unsafe { Tile::kou_representative_unchecked(t1, t2, t3) };
		Self::Shanpon { tile, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::Kanchan` using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn kanchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let tile = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Kanchan { tile, tsumo_or_ron })
	}

	/// Construct a `ScorableHandFourthMeld::Kanchan` using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn kanchan_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let tile = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::Kanchan { tile, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::Penchan` using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn penchan(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let tile = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::Penchan { tile, tsumo_or_ron })
	}

	/// Construct a `ScorableHandFourthMeld::Penchan` using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn penchan_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let tile = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::Penchan { tile, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::RyanmenLow` using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn ryanmen_low(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let tile = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::RyanmenLow { tile, tsumo_or_ron })
	}

	/// Construct a `ScorableHandFourthMeld::RyanmenLow` using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn ryanmen_low_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let tile = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::RyanmenLow { tile, tsumo_or_ron }
	}

	/// Construct a `ScorableHandFourthMeld::RyanmenHigh` using the given tiles and `TsumoOrRon` flag.
	///
	/// Returns `Some` if [`ShunLowTileAndHasFiveRed::new`] returns `Some`, `None` otherwise.
	pub fn ryanmen_high(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Option<Self> {
		let tile = ShunLowTileAndHasFiveRed::new(t1, t2, t3)?;
		Some(Self::RyanmenHigh { tile, tsumo_or_ron })
	}

	/// Construct a `ScorableHandFourthMeld::RyanmenHigh` using the given tiles and `TsumoOrRon` flag.
	///
	/// # Safety
	///
	/// See [`ShunLowTileAndHasFiveRed::new_unchecked`].
	pub unsafe fn ryanmen_high_unchecked(t1: ShunLowTile, t2: NumberTile, t3: NumberTile, tsumo_or_ron: TsumoOrRon) -> Self {
		let tile = unsafe { ShunLowTileAndHasFiveRed::new_unchecked(t1, t2, t3) };
		Self::RyanmenHigh { tile, tsumo_or_ron }
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

			Self::Kanchan { tile, .. } |
			Self::Penchan { tile, .. } |
			Self::RyanmenLow { tile, .. } |
			Self::RyanmenHigh { tile, .. } => {
				let (t1, t2, t3) = tile.shun();
				f(t1.into());
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

impl Ord for ScorableHandFourthMeld {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		// Just like `ScorableHandMeld::cmp`, this sorts by the first tile and then by the type of wait. See the comment in that function for the rationale.
		// However one difference to that function is that `Tanki` is sorted before the other waits.

		fn sort_criteria(m: ScorableHandFourthMeld) -> u16 {
			let (d, t, tsumo_or_ron) = match m {
				ScorableHandFourthMeld::Tanki(_) => unsafe { core::hint::unreachable_unchecked(); },
				ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron, .. } => (0, tile.remove_red(), tsumo_or_ron),
				ScorableHandFourthMeld::Kanchan { tile, tsumo_or_ron, .. } => (1, tile.remove_red().into(), tsumo_or_ron),
				ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron, .. } => (2, tile.remove_red().into(), tsumo_or_ron),
				ScorableHandFourthMeld::RyanmenLow { tile, tsumo_or_ron, .. } => (3, tile.remove_red().into(), tsumo_or_ron),
				ScorableHandFourthMeld::RyanmenHigh { tile, tsumo_or_ron, .. } => (4, tile.remove_red().into(), tsumo_or_ron),
			};
			let t = t as u16;
			let dt = d | (t << 3);
			let tr = match tsumo_or_ron { TsumoOrRon::Tsumo => 0b0, TsumoOrRon::Ron => 0b1 };
			(dt << 1) | tr
		}

		let (sc, sc_other) = match (self, other) {
			(Self::Tanki(m1), Self::Tanki(m2)) => return m1.cmp(m2),
			(Self::Tanki(_), _) => return core::cmp::Ordering::Less,
			(_, Self::Tanki(_)) => return core::cmp::Ordering::Greater,
			(this, other) => (sort_criteria(*this), sort_criteria(*other)),
		};
		sc.cmp(&sc_other)
	}
}

impl PartialEq for ScorableHandFourthMeld {
	fn eq(&self, other: &Self) -> bool {
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
		let tile = Tile::pair_representative(t1, t2)?;
		Some(Self(tile))
	}

	/// Construct a `ScorableHandPair` using the given tiles.
	///
	/// # Safety
	///
	/// Requires `t1.eq_ignore_red(&t2)`.
	pub unsafe fn new_unchecked(t1: Tile, t2: Tile) -> Self {
		let tile = unsafe { Tile::pair_representative_unchecked(t1, t2) };
		Self(tile)
	}

	fn for_each_tile(self, mut f: impl FnMut(Tile)) {
		f(self.0.remove_red());
		f(self.0);
	}

	fn is_tanyao(self) -> bool {
		self.0.is_simple()
	}

	const fn chanta_routou(self) -> ChantaRoutou {
		const TERMINALS: Tile34Set = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };
		const HONORS: Tile34Set = t34set! { E, S, W, G, N, Wh, G, R };

		if TERMINALS.contains(self.0) {
			ChantaRoutou::all_terminals()
		}
		else if HONORS.contains(self.0) {
			ChantaRoutou::all_honors()
		}
		else {
			ChantaRoutou::other()
		}
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
		self.for_each_tile(|t| if is_ok && write!(f, "{t} ").is_err() { is_ok = false; });
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

#[derive(Clone, Copy)]
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
			1 + (is_tanki_wait as u8)
		}
		else {
			0
		}
	}
}

#[derive(Clone, Copy)]
pub(crate) struct Honchinitsu(u8);

impl Honchinitsu {
	pub(crate) const fn is_honitsu(self) -> bool {
		self.0 == 0b01
	}

	pub(crate) const fn is_chinitsu(self) -> bool {
		self.0 == 0b00
	}

	fn neither() -> Self {
		Self(0b11)
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
			self.chanta_routou().is_chanta()
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
			self.num_ankou().is_sanankou()
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
				Self::Regular(h) => h.is_sankantsu(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		const fn is_chiitoi(&self) -> bool {
			matches!(self, Self::Chiitoi(_))
		}

		fn is_honroutou(&self) -> bool {
			self.chanta_routou().is_honroutou()
		}

		fn is_shousangen(&self) -> bool {
			match *self {
				Self::Regular(h) => h.is_shousangen(),
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_honitsu(&self) -> bool {
			self.honchinitsu().is_honitsu()
		}

		fn is_junchan(&self) -> bool {
			self.chanta_routou().is_junchan()
		}

		fn is_ryanpeikou(&self) -> bool {
			match self {
				Self::Regular(h) => h.num_peikou() == 2,
				Self::Chiitoi(_) |
				Self::KokushiMusou(_) => false,
			}
		}

		fn is_chinitsu(&self) -> bool {
			self.honchinitsu().is_chinitsu()
		}

		const fn is_kokushi_musou(&self) -> bool {
			matches!(self, Self::KokushiMusou(_))
		}

		fn num_suuankou(&self) -> u8 {
			self.num_ankou().num_suuankou()
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
			self.chanta_routou().is_tsuuiisou()
		}

		fn is_chinroutou(&self) -> bool {
			self.chanta_routou().is_chinroutou()
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
				Self::Regular(h) => h.is_suukantsu(),
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
}
