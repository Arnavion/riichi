use crate::{
	DragonTile,
	HandMeld,
	Number, NumberTileClassified, NumberSuit, NumberTile,
	Tile, TileClassified, Tile27MultiSet, TsumoOrRon,
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
/// - Any arrays of [`ScorableHandMeld`]s are in sorted order.
///
/// - Any [`ScorableHandMeld`]s, [`ScorableHandFourthMeld`]s and [`ScorableHandPair`]s are themselves consistent.
///   See their docs for details.
///
/// - For `Chiitoi`, the pairs really do form a chiitoi, specifically that
///   no two pairs have the same tiles.
///
/// - For `KokushiMusou`, the array of [`Tile`]s really does form a kokushi musou.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program will still be safe, but `score()`, `PartialEq`, etc
/// will produce unspecified and meaningless results. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum ScorableHand {
	/// Regular hand shape containing four melds and one pair.
	///
	/// The fourth meld indicates what type of wait this hand had.
	Regular {
		melds: ([ScorableHandMeld; 3], ScorableHandFourthMeld),
		pair: ScorableHandPair,
	},

	/// Chiitoi hand shape containing seven pairs.
	Chiitoi([ScorableHandPair; 7]),

	/// Kokushi musou hand shape containing one of each terminal and honor tile and one duplicate.
	KokushiMusou {
		tiles: [Tile; 14],
		/// The winning tile was a duplicate of one of the other thirteen unique tiles.
		was_juusanmen_wait: bool,
	},
}

/// A single meld inside a [`ScorableHand`].
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means:
///
/// - `Anjun` and `Minjun` really contain three [`NumberTile`]s that would form a valid sequence,
///   and are in sorted order.
///
/// - `Ankou` and `Minkou` really contain three of the same [`Tile`],
///   except that if two of them are [`Number::Five`]s then the third may be a [`Number::FiveRed`].
///
/// - `Ankan` and `Minkan` really contain four of the same [`Tile`],
///   except that if three of them are [`Number::Five`]s then the fourth may be a [`Number::FiveRed`].
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program will still be safe, but `score()`, `PartialEq`, etc
/// will produce unspecified and meaningless results. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ScorableHandMeld {
	/// Closed sequence held in hand.
	Anjun([NumberTile; 3]),
	/// Open sequence formed by chii.
	Minjun([NumberTile; 3]),
	/// Closed triplet held in hand.
	Ankou([Tile; 3]),
	/// Open triplet formed by pon.
	Minkou([Tile; 3]),
	/// Closed quad formed by kan.
	Ankan([Tile; 4]),
	/// Open quad formed by kan.
	Minkan([Tile; 4]),
}

/// The fourth meld of a [`ScorableHand::Regular`]. In addition to the content of the meld, this indicates what wait the hand had.
///
/// # Safety
///
/// This type expects that its variant data is consistent. This means:
///
/// - `Kanchan`, `Penchan` and `Ryanmen` really contain three [`NumberTile`]s that would form a valid sequence,
///   and are in sorted order.
///
/// - `Shanpon` really contains three of the same [`Tile`],
///   except that if two of them are [`Number::Five`]s then the third may be a [`Number::FiveRed`].
///
/// - For `Tanki`, the [`ScorableHandMeld`] is itself consistent. See its docs for details.
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program will still be safe, but `score()`, `PartialEq`, etc
/// will produce unspecified and meaningless results. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ScorableHandFourthMeld {
	/// This meld is a shun and had a middle wait.
	///
	/// Eg 123m => 2m completed the hand.
	Kanchan {
		tiles: [NumberTile; 3],
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a one-sided wait.
	///
	/// Eg 123m => 3m completed the hand, 789p => 7p completed the hand.
	Penchan {
		tiles: [NumberTile; 3],
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a double-sided wait. The left tile (lowest number) completed the hand.
	///
	/// Eg 123m => 1m completed the hand, 234m => 2m completed the hand, 678p => 6p completed the hand.
	RyanmenLeft {
		tiles: [NumberTile; 3],
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a shun and had a double-sided wait. The right tile (highest number) completed the hand.
	///
	/// Eg 234m => 4m completed the hand, 678p => 8p completed the hand, 789p => 9p completed the hand.
	RyanmenRight {
		tiles: [NumberTile; 3],
		/// Whether this shun was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld is a kou and one of its tiles completed the hand.
	///
	/// Eg 111m => 1m completed the hand.
	Shanpon {
		tiles: [Tile; 3],
		/// Whether this kou was completed via tsumo or ron.
		tsumo_or_ron: TsumoOrRon,
	},

	/// This meld was already complete. One of the tiles of the [`ScorableHand::Regular::pair`] was the wait.
	Tanki(ScorableHandMeld),
}

/// A single pair inside a [`ScorableHand`].
///
/// # Safety
///
/// This type expects that its data is consistent. This means that it expects the inner array
/// to really contain two of the same [`Tile`],
/// except that if one of them is a [`Number::Five`] then the other may be a [`Number::FiveRed`].
///
/// If this expectation is violated, the program will still be safe, but `score()`, `PartialEq`, etc
/// will produce unspecified and meaningless results. Therefore it is recommended to always satisfy this expectation.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct ScorableHandPair(pub [Tile; 2]);

impl ScorableHand {
	pub fn regular(mut ms: [ScorableHandMeld; 3], m4: ScorableHandFourthMeld, pair: ScorableHandPair) -> Self {
		let melds = match m4 {
			ScorableHandFourthMeld::Tanki(m4) => {
				let [m1, m2, m3] = ms;
				let mut ms = [m1, m2, m3, m4];
				ms.sort_unstable();
				let [m1, m2, m3, m4] = ms;
				([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
			},
			m4 => {
				ms.sort_unstable();
				(ms, m4)
			},
		};
		Self::Regular { melds, pair }
	}

	pub(crate) fn is_menzen(&self) -> bool {
		match self {
			Self::Regular { melds: (ms, m4), .. } =>
				ms.iter().all(|m| m.is_menzen()) &&
				m4.is_menzen(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => true,
		}
	}

	pub(crate) fn is_pinfu(&self, prevailing_wind: WindTile, seat_wind: WindTile) -> bool {
		match self {
			Self::Regular { melds: (ms, ScorableHandFourthMeld::RyanmenLeft { .. } | ScorableHandFourthMeld::RyanmenRight { .. }), pair } =>
				ms.iter().all(|m| matches!(m, ScorableHandMeld::Anjun(_))) &&
				pair.num_yakuhai(prevailing_wind, seat_wind) == 0,
			Self::Regular { .. } |
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_iipeikou(&self) -> bool {
		self.is_menzen() && match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } => {
				let ts: Tile27MultiSet =
					[m1, m2, m3, m4.into()].into_iter()
					.filter_map(|m|
						// Minjun is allowed because m4 may be open because of a ron, which does not invalidate iipeikou.
						// The closed-ness of the hand is already checked via `self.is_menzen()`
						if let ScorableHandMeld::Anjun([t, ..]) | ScorableHandMeld::Minjun([t, ..]) = m {
							Some(t)
						}
						else {
							None
						},
					)
					.collect();
				ts.into_iter().filter(|(_, n)| n.get() >= 2).count() == 1
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_tanyao(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				[m1, m2, m3, m4.into()].into_iter().all(ScorableHandMeld::is_tanyao) && pair.is_tanyao(),
			Self::Chiitoi(ps) => ps.into_iter().all(ScorableHandPair::is_tanyao),
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn num_wind_yakuhai(&self, wind: WindTile, prevailing_wind: WindTile, seat_wind: WindTile) -> u32 {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter()
				.map(|m| m.num_wind_yakuhai(wind, prevailing_wind, seat_wind))
				.sum(),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => 0,
		}
	}

	pub(crate) fn is_dragon_yakuhai(&self, dragon: DragonTile) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter()
				.any(|m| m.is_dragon_yakuhai(dragon)),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_chanta(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				matches!(
					m1.chanta_routou() + m2.chanta_routou() + m3.chanta_routou() + ScorableHandMeld::from(m4).chanta_routou() + pair.chanta_routou(),
					HandChantaRoutou::HasTerminalsAndHonors,
				),
			// Would be honroutou / chinroutou / tsuuiisou instead
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_sanshoku_doujun(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } => {
				let mut counts = [0b111_u8; 7];
				for m in [m1, m2, m3, m4.into()] {
					let (ScorableHandMeld::Anjun([t, ..]) | ScorableHandMeld::Minjun([t, ..])) = m else { continue; };
					let Some(counts) = counts.get_mut(usize::from(t.number().value() - 1)) else { continue; };
					let i = match t.suit() {
						NumberSuit::Man => 0,
						NumberSuit::Pin => 1,
						NumberSuit::Sou => 2,
					};
					*counts &= !(0b1 << i);
					if *counts == 0 {
						return true;
					}
				}
				false
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_ittsuu(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } => {
				let mut counts = [0b111_u8; 3];
				for m in [m1, m2, m3, m4.into()] {
					let (ScorableHandMeld::Anjun([t, ..]) | ScorableHandMeld::Minjun([t, ..])) = m else { continue; };
					let counts = match t.suit() {
						NumberSuit::Man => &mut counts[0],
						NumberSuit::Pin => &mut counts[1],
						NumberSuit::Sou => &mut counts[2],
					};
					let i = match t.number() {
						Number::One => 0,
						Number::Four => 1,
						Number::Seven => 2,
						_ => continue,
					};
					*counts &= !(0b1 << i);
					if *counts == 0 {
						return true;
					}
				}
				false
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_toitoi(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter().all(|m| matches!(
					m,
					ScorableHandMeld::Ankou(_) |
					ScorableHandMeld::Minkou(_) |
					ScorableHandMeld::Ankan(_) |
					ScorableHandMeld::Minkan(_),
				)),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_sanankou(&self) -> bool {
		match self {
			Self::Regular { melds: (ms, m4), .. } => {
				let mut num_closed_triplets = 0_usize;
				let mut num_closed_quads = 0_usize;
				for m in ms {
					match m {
						ScorableHandMeld::Ankou(_) => num_closed_triplets += 1,
						ScorableHandMeld::Ankan(_) => num_closed_quads += 1,
						_ => (),
					}
				}
				match m4 {
					ScorableHandFourthMeld::Shanpon { tsumo_or_ron: TsumoOrRon::Tsumo, .. } |
					ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(_)) => num_closed_triplets += 1,
					ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(_)) => num_closed_quads += 1,
					_ => (),
				}
				(num_closed_triplets + num_closed_quads) == 3
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_sanshoku_doukou(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } => {
				let mut counts = [0b111_u8; 9];
				for m in [m1, m2, m3, m4.into()] {
					let (
						ScorableHandMeld::Ankou([t, ..]) |
						ScorableHandMeld::Minkou([t, ..]) |
						ScorableHandMeld::Ankan([t, ..]) |
						ScorableHandMeld::Minkan([t, ..])
					) = m else { continue; };
					let Ok(t) = NumberTile::try_from(t) else { continue; };
					let counts = &mut counts[usize::from(t.number().value() - 1)];
					let i = match t.suit() {
						NumberSuit::Man => 0,
						NumberSuit::Pin => 1,
						NumberSuit::Sou => 2,
					};
					*counts &= !(0b1 << i);
					if *counts == 0 {
						return true;
					}
				}
				false
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_sankantsu(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter()
				.filter(|m| matches!(m, ScorableHandMeld::Ankan(_) | ScorableHandMeld::Minkan(_)))
				.count() == 3,
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	#[cfg(test)]
	const fn is_chiitoi(&self) -> bool {
		matches!(self, Self::Chiitoi(_))
	}

	pub(crate) fn is_honroutou(&self) -> bool {
		let hand_chanta_routou = match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				m1.chanta_routou() + m2.chanta_routou() + m3.chanta_routou() + ScorableHandMeld::from(m4).chanta_routou() + pair.chanta_routou(),
			Self::Chiitoi([p1, p2, p3, p4, p5, p6, p7]) =>
				p1.chanta_routou() + p2.chanta_routou() + p3.chanta_routou() + p4.chanta_routou() + p5.chanta_routou() + p6.chanta_routou() + p7.chanta_routou(),
			Self::KokushiMusou { .. } => return false,
		};
		matches!(
			hand_chanta_routou,
			HandChantaRoutou::AllTerminalsAndHonors,
		)
	}

	pub(crate) fn is_shousangen(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				[m1, m2, m3, m4.into()].into_iter()
				.filter(|m| matches!(
					m,
					ScorableHandMeld::Ankou([t, ..]) |
					ScorableHandMeld::Minkou([t, ..]) |
					ScorableHandMeld::Ankan([t, ..]) |
					ScorableHandMeld::Minkan([t, ..]) if DragonTile::try_from(*t).is_ok(),
				))
				.count() == 2 &&
				matches!(pair, ScorableHandPair([t, ..]) if DragonTile::try_from(t).is_ok()),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_honitsu(&self) -> bool {
		let mut suit = None;
		let mut has_honors = false;
		for t in *self {
			match t.into() {
				TileClassified::Number(t) =>
					if let Some(suit) = suit {
						if suit != t.suit() {
							return false;
						}
					}
					else {
						suit = Some(t.suit());
					},

				TileClassified::Wind(_) | TileClassified::Dragon(_) => has_honors = true,
			}
		}

		suit.is_some() && has_honors
	}

	pub(crate) fn is_junchan(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				matches!(
					m1.chanta_routou() + m2.chanta_routou() + m3.chanta_routou() + ScorableHandMeld::from(m4).chanta_routou() + pair.chanta_routou(),
					HandChantaRoutou::HasTerminals,
				),
			// Would be chinroutou instead
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_ryanpeikou(&self) -> bool {
		self.is_menzen() && match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } => {
				let ts: Tile27MultiSet =
					[m1, m2, m3, m4.into()].into_iter()
					.filter_map(|m|
						// Minjun is allowed because m4 may be open because of a ron, which does not invalidate ryanpeikou.
						// The closed-ness of the hand is already checked via `self.is_menzen()`
						if let ScorableHandMeld::Anjun([t, ..]) | ScorableHandMeld::Minjun([t, ..]) = m {
							Some(t)
						}
						else {
							None
						},
					)
					.collect();
				ts.into_iter().filter(|(_, n)| n.get() >= 2).count() == 2
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_chinitsu(&self) -> bool {
		let mut suit = None;
		for t in *self {
			let Ok(t) = NumberTile::try_from(t) else { return false; };
			if let Some(suit) = suit {
				if suit != t.suit() {
					return false;
				}
			}
			else {
				suit = Some(t.suit());
			}
		}

		suit.is_some()
	}

	#[cfg(test)]
	const fn is_kokushi_musou(&self) -> bool {
		match self {
			Self::Regular { .. } |
			Self::Chiitoi(_) => false,
			Self::KokushiMusou { .. } => true,
		}
	}

	pub(crate) fn num_suuankou(&self) -> u32 {
		match self {
			Self::Regular { melds: (ms, m4), .. } => {
				let mut num_closed_triplets = 0_usize;
				let mut num_closed_quads = 0_usize;
				for m in ms {
					match m {
						ScorableHandMeld::Ankou(_) => num_closed_triplets += 1,
						ScorableHandMeld::Ankan(_) => num_closed_quads += 1,
						_ => (),
					}
				}
				match m4 {
					ScorableHandFourthMeld::Shanpon { tsumo_or_ron: TsumoOrRon::Tsumo, .. } |
					ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou(_)) => num_closed_triplets += 1,
					ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankan(_)) => num_closed_quads += 1,
					_ => (),
				}
				if (num_closed_triplets + num_closed_quads) == 4 {
					if matches!(m4, ScorableHandFourthMeld::Tanki(_)) { 2 } else { 1 }
				}
				else {
					0
				}
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => 0,
		}
	}

	pub(crate) fn is_daisangen(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter()
				.filter(|m| matches!(
					m,
					ScorableHandMeld::Ankou([t, ..]) |
					ScorableHandMeld::Minkou([t, ..]) |
					ScorableHandMeld::Ankan([t, ..]) |
					ScorableHandMeld::Minkan([t, ..]) if DragonTile::try_from(*t).is_ok(),
				))
				.count() == 3,
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_shousuushii(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				[m1, m2, m3, m4.into()].into_iter()
				.filter(|m| matches!(
					m,
					ScorableHandMeld::Ankou([t, ..]) |
					ScorableHandMeld::Minkou([t, ..]) |
					ScorableHandMeld::Ankan([t, ..]) |
					ScorableHandMeld::Minkan([t, ..]) if WindTile::try_from(*t).is_ok(),
				))
				.count() == 3 &&
				matches!(pair, ScorableHandPair([t, ..]) if WindTile::try_from(t).is_ok()),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_daisuushii(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter()
				.filter(|m| matches!(
					m,
					ScorableHandMeld::Ankou([t, ..]) |
					ScorableHandMeld::Minkou([t, ..]) |
					ScorableHandMeld::Ankan([t, ..]) |
					ScorableHandMeld::Minkan([t, ..]) if WindTile::try_from(*t).is_ok(),
				))
				.count() == 4,
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_tsuuiisou(&self) -> bool {
		let hand_chanta_routou = match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				m1.chanta_routou() + m2.chanta_routou() + m3.chanta_routou() + ScorableHandMeld::from(m4).chanta_routou() + pair.chanta_routou(),
			Self::Chiitoi([p1, p2, p3, p4, p5, p6, p7]) =>
				p1.chanta_routou() + p2.chanta_routou() + p3.chanta_routou() + p4.chanta_routou() + p5.chanta_routou() + p6.chanta_routou() + p7.chanta_routou(),
			Self::KokushiMusou { .. } => return false,
		};
		matches!(
			hand_chanta_routou,
			HandChantaRoutou::AllHonors,
		)
	}

	pub(crate) fn is_chinroutou(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				matches!(
					m1.chanta_routou() + m2.chanta_routou() + m3.chanta_routou() + ScorableHandMeld::from(m4).chanta_routou() + pair.chanta_routou(),
					HandChantaRoutou::AllTerminals,
				),
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn is_ryuuiisou(&self) -> bool {
		match self {
			Self::Regular { .. } => {
				// Note: Having G is not required.
				for t in *self {
					if !matches!(t, t!(2s | 3s | 4s | 6s | 8s | G)) {
						return false;
					}
				}
				true
			},
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}

	pub(crate) fn num_chuuren_poutou(&self) -> u32 {
		// It's easier to hard-code all the hands and check for equality rather than write code to inspect every meld and pair.
		// 1 and 9 can be a ryanmen or shanpon hand, and either can be completed via tsumo or ron, for four possible hands each.
		// 2, 5 and 8 can be a tanki hand, for one possible hand each.
		// 3 and 7 can be a ryanmen or penchan hand, and either can be completed via tsumo or ron, for four possible hands each.
		// 4 and 6 can be one of two ryanmen hands, and either can be completed via tsumo or ron, for four possible hands each.

		fn make_junsei_hands(suit: NumberSuit) -> std::collections::BTreeSet<ScorableHand> {
			let n1 = NumberTile::from(NumberTileClassified { suit, number: Number::One });
			let t1 = n1.into();
			let n2 = NumberTile::from(NumberTileClassified { suit, number: Number::Two });
			let t2 = n2.into();
			let n3 = NumberTile::from(NumberTileClassified { suit, number: Number::Three });
			let n4 = NumberTile::from(NumberTileClassified { suit, number: Number::Four });
			let n5 = NumberTile::from(NumberTileClassified { suit, number: Number::Five });
			let t5 = n5.into();
			let n6 = NumberTile::from(NumberTileClassified { suit, number: Number::Six });
			let n7 = NumberTile::from(NumberTileClassified { suit, number: Number::Seven });
			let n8 = NumberTile::from(NumberTileClassified { suit, number: Number::Eight });
			let t8 = n8.into();
			let n9 = NumberTile::from(NumberTileClassified { suit, number: Number::Nine });
			let t9 = n9.into();
			[
				// 1
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n1, n2, n3], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n1, n2, n3], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::Shanpon { tiles: [t1, t1, t1], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::Shanpon { tiles: [t1, t1, t1], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t9, t9])),
				// 2
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n3, n4, n5]), ScorableHandMeld::Anjun([n6, n7, n8])], ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou([t9, t9, t9])), ScorableHandPair([t2, t2])),
				// 3
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n6, n7, n8]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n3, n4, n5], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n6, n7, n8]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n3, n4, n5], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n3, n4, n5]), ScorableHandMeld::Anjun([n6, n7, n8]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::Penchan { tiles: [n1, n2, n3], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n3, n4, n5]), ScorableHandMeld::Anjun([n6, n7, n8]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::Penchan { tiles: [n1, n2, n3], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t1, t1])),
				// 4
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n4, n5, n6], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n4, n5, n6], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n2, n3, n4], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n2, n3, n4], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t9, t9])),
				// 5
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n6, n7, n8])], ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou([t9, t9, t9])), ScorableHandPair([t5, t5])),
				// 6
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n6, n7, n8], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenLeft { tiles: [n6, n7, n8], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n6, n7, n8]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n4, n5, n6], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n6, n7, n8]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n4, n5, n6], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t1, t1])),
				// 7
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n5, n6, n7], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n5, n6, n7], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n5, n6, n7])], ScorableHandFourthMeld::Penchan { tiles: [n7, n8, n9], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t9, t9])),
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n5, n6, n7])], ScorableHandFourthMeld::Penchan { tiles: [n7, n8, n9], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t9, t9])),
				// 8
				ScorableHand::regular([ScorableHandMeld::Ankou([t1, t1, t1]), ScorableHandMeld::Anjun([n2, n3, n4]), ScorableHandMeld::Anjun([n5, n6, n7])], ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou([t9, t9, t9])), ScorableHandPair([t8, t8])),
				// 9
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n7, n8, n9], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Ankou([t9, t9, t9])], ScorableHandFourthMeld::RyanmenRight { tiles: [n7, n8, n9], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::Shanpon { tiles: [t9, t9, t9], tsumo_or_ron: TsumoOrRon::Tsumo }, ScorableHandPair([t1, t1])),
				ScorableHand::regular([ScorableHandMeld::Anjun([n1, n2, n3]), ScorableHandMeld::Anjun([n4, n5, n6]), ScorableHandMeld::Anjun([n7, n8, n9])], ScorableHandFourthMeld::Shanpon { tiles: [t9, t9, t9], tsumo_or_ron: TsumoOrRon::Ron }, ScorableHandPair([t1, t1])),
			].into()
		}

		static JUNSEI_HANDS_MAN: std::sync::LazyLock<std::collections::BTreeSet<ScorableHand>> = std::sync::LazyLock::new(|| make_junsei_hands(NumberSuit::Man));
		static JUNSEI_HANDS_PIN: std::sync::LazyLock<std::collections::BTreeSet<ScorableHand>> = std::sync::LazyLock::new(|| make_junsei_hands(NumberSuit::Pin));
		static JUNSEI_HANDS_SOU: std::sync::LazyLock<std::collections::BTreeSet<ScorableHand>> = std::sync::LazyLock::new(|| make_junsei_hands(NumberSuit::Sou));

		if !self.is_menzen() {
			return 0;
		}

		match self {
			Self::Regular { .. } => {
				let mut counts = [[3_u8, 1, 1, 1, 1, 1, 1, 1, 3]; 3];
				for t in *self {
					let Ok(t) = NumberTile::try_from(t) else { return 0; };
					let counts = match t.suit() {
						NumberSuit::Man => &mut counts[0],
						NumberSuit::Pin => &mut counts[1],
						NumberSuit::Sou => &mut counts[2],
					};
					let count = &mut counts[usize::from(t.number().value() - 1)];
					*count = count.saturating_sub(1);
				}
				for (counts, junsei_hands) in [(counts[0], &JUNSEI_HANDS_MAN), (counts[1], &JUNSEI_HANDS_PIN), (counts[2], &JUNSEI_HANDS_SOU)] {
					if counts == [0; 9] {
						return if junsei_hands.contains(self) { 2 } else { 1 };
					}
				}

				0
			},

			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => 0,
		}
	}

	pub(crate) fn is_suukantsu(&self) -> bool {
		match *self {
			Self::Regular { melds: ([m1, m2, m3], m4), .. } =>
				[m1, m2, m3, m4.into()].into_iter()
				.filter(|m| matches!(m, ScorableHandMeld::Ankan(_) | ScorableHandMeld::Minkan(_)))
				.count() == 4,
			Self::Chiitoi(_) |
			Self::KokushiMusou { .. } => false,
		}
	}
}

impl std::fmt::Debug for ScorableHand {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for ScorableHand {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } =>
				write!(f, "{m1} {m2} {m3} {m4} {pair}"),
			Self::Chiitoi([p1, p2, p3, p4, p5, p6, p7]) =>
				write!(f, "{p1} {p2} {p3} {p4} {p5} {p6} {p7}"),
			Self::KokushiMusou { tiles: [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14], was_juusanmen_wait: false } =>
				write!(f, "{t1} {t2} {t3} {t4} {t5} {t6} {t7} {t8} {t9} {t10} {t11} {t12} {t13} {t14}"),
			Self::KokushiMusou { tiles: [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14], was_juusanmen_wait: true } =>
				write!(f, "{t1} {t2} {t3} {t4} {t5} {t6} {t7} {t8} {t9} {t10} {t11} {t12} {t13} {t14} juusanmen"),
		}
	}
}

impl IntoIterator for ScorableHand {
	type Item = Tile;
	type IntoIter = ScorableHandIntoIter;

	fn into_iter(self) -> Self::IntoIter {
		let mut inner = [const { std::mem::MaybeUninit::uninit() }; 18];
		let mut len = 0;
		match self {
			Self::Regular { melds: (ms, m4), pair } =>
				for t in ms.into_iter().flatten().chain(ScorableHandMeld::from(m4)).chain(pair) {
					inner[len].write(t);
					len += 1;
				},

			Self::Chiitoi(ps) =>
				for ScorableHandPair([t1, t2]) in ps {
					inner[len].write(t1);
					inner[len + 1].write(t2);
					len += 2;
				}

			Self::KokushiMusou { tiles, .. } =>
				for t in tiles {
					inner[len].write(t);
					len += 1;
				},
		}
		#[expect(clippy::cast_possible_truncation)]
		ScorableHandIntoIter { inner, range: 0..(len as u8) }
	}
}

#[derive(Clone)]
pub struct ScorableHandIntoIter {
	inner: [std::mem::MaybeUninit<Tile>; 18],
	range: std::ops::Range<u8>,
}

impl std::fmt::Debug for ScorableHandIntoIter {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("ScorableHandIntoIter").finish_non_exhaustive()
	}
}

impl Iterator for ScorableHandIntoIter {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		let i = usize::from(self.range.next()?);
		let t = unsafe { self.inner.get_unchecked(i).assume_init() };
		Some(t)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.range.size_hint()
	}
}

impl DoubleEndedIterator for ScorableHandIntoIter {
	fn next_back(&mut self) -> Option<Self::Item> {
		let i = usize::from(self.range.next_back()?);
		let t = unsafe { self.inner.get_unchecked(i).assume_init() };
		Some(t)
	}
}

impl ExactSizeIterator for ScorableHandIntoIter {}

impl std::iter::FusedIterator for ScorableHandIntoIter {}

impl ScorableHandMeld {
	const fn is_menzen(self) -> bool {
		match self {
			Self::Anjun(_) |
			Self::Ankou(_) |
			Self::Ankan(_)
				=> true,
			Self::Minjun(_) |
			Self::Minkou(_) |
			Self::Minkan(_)
				=> false,
		}
	}

	const fn is_tanyao(self) -> bool {
		match self {
			Self::Anjun([t, ..]) |
			Self::Minjun([t, ..]) =>
				matches!(
					t,
					tn!(
						2m | 2p | 2s |
						3m | 3p | 3s |
						4m | 4p | 4s |
						5m | 5p | 5s |
						0m | 0p | 0s |
						6m | 6p | 6s
					),
				),

			Self::Ankou([t, ..]) |
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) =>
				matches!(
					t,
					t!(
						2m | 2p | 2s |
						3m | 3p | 3s |
						4m | 4p | 4s |
						5m | 5p | 5s |
						0m | 0p | 0s |
						6m | 6p | 6s |
						7m | 7p | 7s |
						8m | 8p | 8s
					),
				),
		}
	}

	const fn chanta_routou(self) -> MeldChantaRoutou {
		match self {
			Self::Anjun([t, ..]) |
			Self::Minjun([t, ..]) => match t {
				tn!(1m | 1p | 1s | 7m | 7p | 7s) => MeldChantaRoutou::HasTerminal,
				_ => MeldChantaRoutou::Other,
			},

			Self::Ankou([t, ..]) |
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => match t {
				t!(1m | 1p | 1s | 9m | 9p | 9s) => MeldChantaRoutou::AllTerminals,
				t!(E | S | W | N | Wh | G | R) => MeldChantaRoutou::AllHonors,
				_ => MeldChantaRoutou::Other,
			},
		}
	}

	fn num_wind_yakuhai(self, wind: WindTile, prevailing_wind: WindTile, seat_wind: WindTile) -> u32 {
		let tile = match self {
			Self::Anjun(_) |
			Self::Minjun(_) => return 0,
			Self::Ankou([t, ..]) |
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => t,
		};
		if let Ok(tile) = WindTile::try_from(tile) && tile == wind {
			u32::from(tile == prevailing_wind) +
			u32::from(tile == seat_wind)
		}
		else {
			0
		}
	}

	fn is_dragon_yakuhai(self, dragon: DragonTile) -> bool {
		match self {
			Self::Anjun(_) |
			Self::Minjun(_) => false,
			Self::Ankou([t, ..]) |
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => t == dragon.into(),
		}
	}
}

impl std::fmt::Debug for ScorableHandMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for ScorableHandMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Anjun([t1, t2, t3]) =>
				write!(f, "{{ anjun {t1} {t2} {t3} }}"),
			Self::Minjun([t1, t2, t3]) =>
				write!(f, "{{ minjun {t1} {t2} {t3} }}"),
			Self::Ankou([t1, t2, t3]) =>
				write!(f, "{{ ankou {t1} {t2} {t3} }}"),
			Self::Minkou([t1, t2, t3]) =>
				write!(f, "{{ minkou {t1} {t2} {t3} }}"),
			Self::Ankan([t1, t2, t3, t4]) =>
				write!(f, "{{ ankan {t1} {t2} {t3} {t4} }}"),
			Self::Minkan([t1, t2, t3, t4]) =>
				write!(f, "{{ minkan {t1} {t2} {t3} {t4} }}"),
		}
	}
}

impl From<HandMeld> for ScorableHandMeld {
	fn from(meld: HandMeld) -> Self {
		match meld {
			HandMeld::Minjun(mut ts) => { ts.sort_unstable(); Self::Minjun(ts) },
			HandMeld::Minkou(mut ts) => { ts.sort_unstable(); Self::Minkou(ts) },
			HandMeld::Ankan(mut ts) => { ts.sort_unstable(); Self::Ankan(ts) },
			HandMeld::Minkan(mut ts) => { ts.sort_unstable(); Self::Minkan(ts) },
		}
	}
}

impl From<ScorableHandFourthMeld> for ScorableHandMeld {
	fn from(meld: ScorableHandFourthMeld) -> Self {
		match meld {
			ScorableHandFourthMeld::Kanchan { tiles, tsumo_or_ron: TsumoOrRon::Tsumo } |
			ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron: TsumoOrRon::Tsumo } |
			ScorableHandFourthMeld::RyanmenLeft { tiles, tsumo_or_ron: TsumoOrRon::Tsumo } |
			ScorableHandFourthMeld::RyanmenRight { tiles, tsumo_or_ron: TsumoOrRon::Tsumo } => Self::Anjun(tiles),
			ScorableHandFourthMeld::Kanchan { tiles, tsumo_or_ron: TsumoOrRon::Ron } |
			ScorableHandFourthMeld::Penchan { tiles, tsumo_or_ron: TsumoOrRon::Ron } |
			ScorableHandFourthMeld::RyanmenLeft { tiles, tsumo_or_ron: TsumoOrRon::Ron } |
			ScorableHandFourthMeld::RyanmenRight { tiles, tsumo_or_ron: TsumoOrRon::Ron } => Self::Minjun(tiles),
			ScorableHandFourthMeld::Shanpon { tiles, tsumo_or_ron: TsumoOrRon::Tsumo } => Self::Ankou(tiles),
			ScorableHandFourthMeld::Shanpon { tiles, tsumo_or_ron: TsumoOrRon::Ron } => Self::Minkou(tiles),
			ScorableHandFourthMeld::Tanki(m) => m,
		}
	}
}

impl IntoIterator for ScorableHandMeld {
	type Item = Tile;
	type IntoIter = ScorableHandMeldIntoIter;

	fn into_iter(self) -> Self::IntoIter {
		match self {
			Self::Anjun([t1, t2, t3]) |
			Self::Minjun([t1, t2, t3]) => ScorableHandMeldIntoIter { inner: [t1.into(), t2.into(), t3.into()].into_iter().chain(None) },
			Self::Ankou([t1, t2, t3]) |
			Self::Minkou([t1, t2, t3]) => ScorableHandMeldIntoIter { inner: [t1, t2, t3].into_iter().chain(None) },
			Self::Ankan([t1, t2, t3, t4]) |
			Self::Minkan([t1, t2, t3, t4]) => ScorableHandMeldIntoIter { inner: [t1, t2, t3].into_iter().chain(Some(t4)) },
		}
	}
}

impl Ord for ScorableHandMeld {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		let (t1, t2, t3, t4) = match *self {
			Self::Anjun([t1, t2, t3]) |
			Self::Minjun([t1, t2, t3]) => (t1.into(), t2.into(), t3.into(), t3.into()),
			Self::Ankou([t1, t2, t3]) |
			Self::Minkou([t1, t2, t3]) => (t1, t2, t3, t3),
			Self::Ankan([t1, t2, t3, t4]) |
			Self::Minkan([t1, t2, t3, t4]) => (t1, t2, t3, t4),
		};
		let (t_other1, t_other2, t_other3, t_other4) = match *other {
			Self::Anjun([t1, t2, t3]) |
			Self::Minjun([t1, t2, t3]) => (t1.into(), t2.into(), t3.into(), t3.into()),
			Self::Ankou([t1, t2, t3]) |
			Self::Minkou([t1, t2, t3]) => (t1, t2, t3, t3),
			Self::Ankan([t1, t2, t3, t4]) |
			Self::Minkan([t1, t2, t3, t4]) => (t1, t2, t3, t4),
		};
		#[expect(clippy::match_same_arms)]
		t1.cmp(&t_other1)
		.then_with(|| t2.cmp(&t_other2))
		.then_with(|| t3.cmp(&t_other3))
		.then_with(|| t4.cmp(&t_other4))
		.then_with(|| match (self, other) {
			(Self::Anjun(_), Self::Anjun(_)) => std::cmp::Ordering::Equal,
			(Self::Anjun(_), Self::Minjun(_) | Self::Ankou(_) | Self::Minkou(_) | Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minjun(_), Self::Anjun(_)) => std::cmp::Ordering::Greater,
			(Self::Minjun(_), Self::Minjun(_)) => std::cmp::Ordering::Equal,
			(Self::Minjun(_), Self::Ankou(_) | Self::Minkou(_) | Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Ankou(_), Self::Anjun(_) | Self::Minjun(_)) => std::cmp::Ordering::Greater,
			(Self::Ankou(_), Self::Ankou(_)) => std::cmp::Ordering::Equal,
			(Self::Ankou(_), Self::Minkou(_) | Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minkou(_), Self::Anjun(_) | Self::Minjun(_) | Self::Ankou(_)) => std::cmp::Ordering::Greater,
			(Self::Minkou(_), Self::Minkou(_)) => std::cmp::Ordering::Equal,
			(Self::Minkou(_), Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Ankan(_), Self::Anjun(_) | Self::Minjun(_) | Self::Ankou(_) | Self::Minkou(_)) => std::cmp::Ordering::Greater,
			(Self::Ankan(_), Self::Ankan(_)) => std::cmp::Ordering::Equal,
			(Self::Ankan(_), Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minkan(_), Self::Anjun(_) | Self::Minjun(_) | Self::Ankou(_) | Self::Minkou(_) | Self::Ankan(_)) => std::cmp::Ordering::Greater,
			(Self::Minkan(_), Self::Minkan(_)) => std::cmp::Ordering::Equal,
		})
	}
}

impl PartialOrd for ScorableHandMeld {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

#[derive(Clone)]
pub struct ScorableHandMeldIntoIter {
	inner: std::iter::Chain<std::array::IntoIter<Tile, 3>, std::option::IntoIter<Tile>>,
}

impl std::fmt::Debug for ScorableHandMeldIntoIter {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("ScorableHandMeldIntoIter").finish_non_exhaustive()
	}
}

impl Iterator for ScorableHandMeldIntoIter {
	type Item = Tile;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl DoubleEndedIterator for ScorableHandMeldIntoIter {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.next_back()
	}
}

impl ExactSizeIterator for ScorableHandMeldIntoIter {}

impl std::iter::FusedIterator for ScorableHandMeldIntoIter {}

impl ScorableHandFourthMeld {
	const fn is_menzen(self) -> bool {
		match self {
			Self::Kanchan { .. } |
			Self::Penchan { .. } |
			Self::RyanmenLeft { .. } |
			Self::RyanmenRight { .. } |
			Self::Shanpon { .. } => true,
			Self::Tanki(m) => m.is_menzen(),
		}
	}
}

impl std::fmt::Debug for ScorableHandFourthMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for ScorableHandFourthMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Kanchan { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Tsumo } => write!(f, "{{ anjun {t1} {t2} {t3} kanchan }}"),
			Self::Kanchan { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Ron } => write!(f, "{{ minjun {t1} {t2} {t3} kanchan }}"),
			Self::Penchan { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Tsumo } => write!(f, "{{ anjun {t1} {t2} {t3} penchan }}"),
			Self::Penchan { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Ron } => write!(f, "{{ minjun {t1} {t2} {t3} penchan }}"),
			Self::RyanmenLeft { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Tsumo } => write!(f, "{{ anjun {t1} {t2} {t3} ryanmen_left }}"),
			Self::RyanmenLeft { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Ron } => write!(f, "{{ minjun {t1} {t2} {t3} ryanmen_left }}"),
			Self::RyanmenRight { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Tsumo } => write!(f, "{{ anjun {t1} {t2} {t3} ryanmen_right }}"),
			Self::RyanmenRight { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Ron } => write!(f, "{{ minjun {t1} {t2} {t3} ryanmen_right }}"),
			Self::Shanpon { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Tsumo } => write!(f, "{{ ankou {t1} {t2} {t3} shanpon }}"),
			Self::Shanpon { tiles: [t1, t2, t3], tsumo_or_ron: TsumoOrRon::Ron } => write!(f, "{{ minkou {t1} {t2} {t3} shanpon }}"),
			Self::Tanki(m4) => write!(f, "{m4}"),
		}
	}
}

impl Ord for ScorableHandFourthMeld {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		match (self, other) {
			(Self::Tanki(m1), Self::Tanki(m2)) => return m1.cmp(m2),
			(Self::Tanki(_), _) => return std::cmp::Ordering::Greater,
			(_, Self::Tanki(_)) => return std::cmp::Ordering::Less,
			_ => (),
		}
		let (t1, t2, t3) = match *self {
			Self::Kanchan { tiles: [t1, t2, t3], .. } |
			Self::Penchan { tiles: [t1, t2, t3], .. } |
			Self::RyanmenLeft { tiles: [t1, t2, t3], .. } |
			Self::RyanmenRight { tiles: [t1, t2, t3], .. } => (t1.into(), t2.into(), t3.into()),
			Self::Shanpon { tiles: [t1, t2, t3], .. } => (t1, t2, t3),
			Self::Tanki(_) => unreachable!(),
		};
		let (t_other1, t_other2, t_other3) = match *other {
			Self::Kanchan { tiles: [t1, t2, t3], .. } |
			Self::Penchan { tiles: [t1, t2, t3], .. } |
			Self::RyanmenLeft { tiles: [t1, t2, t3], .. } |
			Self::RyanmenRight { tiles: [t1, t2, t3], .. } => (t1.into(), t2.into(), t3.into()),
			Self::Shanpon { tiles: [t1, t2, t3], .. } => (t1, t2, t3),
			Self::Tanki(_) => unreachable!(),
		};
		#[expect(clippy::match_same_arms)]
		t1.cmp(&t_other1)
		.then_with(|| t2.cmp(&t_other2))
		.then_with(|| t3.cmp(&t_other3))
		.then_with(|| match (self, other) {
			(Self::Kanchan { tsumo_or_ron: tor1, .. }, Self::Kanchan { tsumo_or_ron: tor2, .. }) => tor1.cmp(tor2),
			(Self::Kanchan { .. }, Self::Penchan { .. } | Self::RyanmenLeft { .. } | Self::RyanmenRight { .. } | Self::Shanpon { .. }) => std::cmp::Ordering::Less,

			(Self::Penchan { .. }, Self::Kanchan { .. }) => std::cmp::Ordering::Greater,
			(Self::Penchan { tsumo_or_ron: tor1, .. }, Self::Penchan { tsumo_or_ron: tor2, .. }) => tor1.cmp(tor2),
			(Self::Penchan { .. }, Self::RyanmenLeft { .. } | Self::RyanmenRight { .. } | Self::Shanpon { .. }) => std::cmp::Ordering::Less,

			(Self::RyanmenLeft { .. }, Self::Kanchan { .. } | Self::Penchan { .. }) => std::cmp::Ordering::Greater,
			(Self::RyanmenLeft { tsumo_or_ron: tor1, .. }, Self::RyanmenLeft { tsumo_or_ron: tor2, .. }) => tor1.cmp(tor2),
			(Self::RyanmenLeft { .. }, Self::RyanmenRight { .. } | Self::Shanpon { .. }) => std::cmp::Ordering::Less,

			(Self::RyanmenRight { .. }, Self::Kanchan { .. } | Self::Penchan { .. } | Self::RyanmenLeft { .. }) => std::cmp::Ordering::Greater,
			(Self::RyanmenRight { tsumo_or_ron: tor1, .. }, Self::RyanmenRight { tsumo_or_ron: tor2, .. }) => tor1.cmp(tor2),
			(Self::RyanmenRight { .. }, Self::Shanpon { .. }) => std::cmp::Ordering::Less,

			(Self::Shanpon { .. }, Self::Kanchan { .. } | Self::Penchan { .. } | Self::RyanmenLeft { .. } | Self::RyanmenRight { .. }) => std::cmp::Ordering::Greater,
			(Self::Shanpon { tsumo_or_ron: tor1, .. }, Self::Shanpon { tsumo_or_ron: tor2, .. }) => tor1.cmp(tor2),

			_ => unreachable!(),
		})
	}
}

impl PartialOrd for ScorableHandFourthMeld {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl ScorableHandPair {
	const fn is_tanyao(self) -> bool {
		matches!(
			self.0[0],
			t!(
				2m | 2p | 2s |
				3m | 3p | 3s |
				4m | 4p | 4s |
				5m | 5p | 5s |
				0m | 0p | 0s |
				6m | 6p | 6s |
				7m | 7p | 7s |
				8m | 8p | 8s
			),
		)
	}

	const fn chanta_routou(self) -> MeldChantaRoutou {
		match self.0[0] {
			t!(1m | 1p | 1s | 9m | 9p | 9s) => MeldChantaRoutou::AllTerminals,
			t!(E | S | W | N | Wh | G | R) => MeldChantaRoutou::AllHonors,
			_ => MeldChantaRoutou::Other,
		}
	}

	pub(crate) fn num_yakuhai(self, prevailing_wind: WindTile, seat_wind: WindTile) -> u32 {
		match self.0[0].into() {
			TileClassified::Number(_) => 0,
			TileClassified::Wind(t) => u32::from(t == prevailing_wind) + u32::from(t == seat_wind),
			TileClassified::Dragon(_) => 1,
		}
	}
}

impl std::fmt::Debug for ScorableHandPair {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for ScorableHandPair {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{{ {} {} }}", self.0[0], self.0[1])
	}
}

impl IntoIterator for ScorableHandPair {
	type Item = <[Tile; 2] as IntoIterator>::Item;
	type IntoIter = <[Tile; 2] as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

#[derive(Clone, Copy, Debug)]
enum MeldChantaRoutou {
	HasTerminal,
	AllTerminals,
	AllHonors,
	Other,
}

#[derive(Clone, Copy, Debug)]
enum HandChantaRoutou {
	/// Chanta
	HasTerminalsAndHonors,
	/// Junchan
	HasTerminals,
	/// Honroutou
	AllTerminalsAndHonors,
	/// Chinroutou
	AllTerminals,
	/// Tsuuiisou
	AllHonors,
	Other,
}

impl std::ops::Add for MeldChantaRoutou {
	type Output = HandChantaRoutou;

	fn add(self, rhs: Self) -> Self::Output {
		#[expect(clippy::match_same_arms)]
		match (self, rhs) {
			(Self::HasTerminal, Self::HasTerminal | Self::AllTerminals) => HandChantaRoutou::HasTerminals,
			(Self::HasTerminal, Self::AllHonors) => HandChantaRoutou::HasTerminalsAndHonors,

			(Self::AllTerminals, Self::HasTerminal) => HandChantaRoutou::HasTerminals,
			(Self::AllTerminals, Self::AllTerminals) => HandChantaRoutou::AllTerminals,
			(Self::AllTerminals, Self::AllHonors) => HandChantaRoutou::AllTerminalsAndHonors,

			(Self::AllHonors, Self::HasTerminal) => HandChantaRoutou::HasTerminalsAndHonors,
			(Self::AllHonors, Self::AllTerminals) => HandChantaRoutou::AllTerminalsAndHonors,
			(Self::AllHonors, Self::AllHonors) => HandChantaRoutou::AllHonors,

			(_, Self::Other) |
			(Self::Other, _) => HandChantaRoutou::Other,
		}
	}
}

impl std::ops::Add<MeldChantaRoutou> for HandChantaRoutou {
	type Output = Self;

	fn add(self, rhs: MeldChantaRoutou) -> Self::Output {
		#[expect(clippy::match_same_arms)]
		match (self, rhs) {
			(Self::HasTerminalsAndHonors, MeldChantaRoutou::HasTerminal | MeldChantaRoutou::AllTerminals | MeldChantaRoutou::AllHonors) => Self::HasTerminalsAndHonors,

			(Self::HasTerminals, MeldChantaRoutou::HasTerminal | MeldChantaRoutou::AllTerminals) => Self::HasTerminals,
			(Self::HasTerminals, MeldChantaRoutou::AllHonors) => Self::HasTerminalsAndHonors,

			(Self::AllTerminalsAndHonors, MeldChantaRoutou::HasTerminal) => Self::HasTerminalsAndHonors,
			(Self::AllTerminalsAndHonors, MeldChantaRoutou::AllTerminals | MeldChantaRoutou::AllHonors) => Self::AllTerminalsAndHonors,

			(Self::AllTerminals, MeldChantaRoutou::HasTerminal) => Self::HasTerminals,
			(Self::AllTerminals, MeldChantaRoutou::AllTerminals) => Self::AllTerminals,
			(Self::AllTerminals, MeldChantaRoutou::AllHonors) => Self::AllTerminalsAndHonors,

			(Self::AllHonors, MeldChantaRoutou::HasTerminal) => Self::HasTerminalsAndHonors,
			(Self::AllHonors, MeldChantaRoutou::AllTerminals) => Self::AllTerminalsAndHonors,
			(Self::AllHonors, MeldChantaRoutou::AllHonors) => Self::AllHonors,

			(_, MeldChantaRoutou::Other) |
			(Self::Other, _) => Self::Other,
		}
	}
}

#[cfg(test)]
mod tests {
	macro_rules! test {
		(@inner_new_tile $hand:ident) => {};

		(@inner_new_tile $hand:ident + $new_tile:tt => [ $( $scorable_hand:tt => { $($funcs:tt)* } )* ] $($rest:tt)*) => {{
			{
				let mut hands = $hand.to_scorable_hands(t!($new_tile), $crate::TsumoOrRon::Tsumo);
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
				let mut hands = $hand.to_scorable_hands(t!($new_tile), $crate::TsumoOrRon::Ron);
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
				({ anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 4s 5s 6s } { anjun 3p 4p 5p ryanmen_left } { 8s 8s }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 6p => [
				({ anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 4s 5s 6s } { anjun 4p 5p 6p ryanmen_right } { 8s 8s }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Pinfu&oldid=27744

		test!((1m 2m 3m 2s 3s 4s 7s 8s 5p 6p 7p 9p 9p)
			+ 6s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 6s 7s 8s ryanmen_left } { 9p 9p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 9s => [
				({ anjun 1m 2m 3m } { anjun 2s 3s 4s } { anjun 5p 6p 7p } { anjun 7s 8s 9s ryanmen_right } { 9p 9p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
		);

		// > Every tile group is a sequence, but this hand is open.
		test!((4m 5m 6m 3p 4p 5p 7p 8p 5s 5s { minjun 5s 6s 7s })
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 3p 4p 5p } { minjun 5s 6s 7s } { anjun 6p 7p 8p ryanmen_left } { 5s 5s }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 9p => [
				({ anjun 4m 5m 6m } { anjun 3p 4p 5p } { minjun 5s 6s 7s } { anjun 7p 8p 9p ryanmen_right } { 5s 5s }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
		);

		// > The pair of east winds invalidates pinfu if won by the dealer or by any player in the east round.
		test!((2m 3m 1p 2p 3p 6s 7s 8s 3m 4m 5m E E)
			+ 1m => [
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 1m 2m 3m ryanmen_left } { E E }) => {
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
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 2m 3m 4m ryanmen_right } { E E }) => {
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
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 1m 2m 3m ryanmen_left } { Wh Wh }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m kanchan } { Wh Wh }) => {
					!is_pinfu(tw!(E), tw!(E));
				}
				({ anjun 1p 2p 3p } { anjun 6s 7s 8s } { anjun 3m 4m 5m } { anjun 2m 3m 4m ryanmen_right } { Wh Wh }) => {
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
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 6p 7p 8p ryanmen_left } { 6p 6p }) => {
					is_pinfu(tw!(E), tw!(E));
				}
			]
			+ 9p => [
				({ anjun 4m 5m 6m } { anjun 1s 2s 3s } { anjun 3p 4p 5p } { anjun 7p 8p 9p ryanmen_right } { 6p 6p }) => {
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
				({ anjun 6m 7m 8m } { ankou 3p 3p 3p } { minkou 2m 2m 2m } { anjun 3s 4s 5s ryanmen_left } { 6p 6p }) => {
					is_tanyao();
				}
			]
			+ 6s => [
				({ anjun 6m 7m 8m } { ankou 3p 3p 3p } { minkou 2m 2m 2m } { anjun 4s 5s 6s ryanmen_right } { 6p 6p }) => {
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
				({ anjun 1p 2p 3p } { ankou 9s 9s 9s } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_left } { N N }) => {
					is_chanta();
					!is_honroutou();
					!is_junchan();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ 4m => [
				({ anjun 1p 2p 3p } { ankou 9s 9s 9s } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_right } { N N }) => {
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
				({ anjun 1p 2p 3p } { minjun 1m 2m 3m } { minjun 3s 1s 2s } { anjun 6s 7s 8s ryanmen_right } { E E }) => {
					is_sanshoku_doujun();
				}
			]
			+ 5s => [
				({ anjun 1p 2p 3p } { minjun 1m 2m 3m } { minjun 3s 1s 2s } { anjun 5s 6s 7s ryanmen_left } { E E }) => {
					is_sanshoku_doujun();
				}
			]
		);

		test!((4m 5m 6m 4s 5s 6s 4p 5p S S S G G)
			+ 3p => [
				({ anjun 4m 5m 6m } { anjun 4s 5s 6s } { ankou S S S } { anjun 3p 4p 5p ryanmen_left } { G G }) => {
					!is_sanshoku_doujun();
				}
			]
			+ 6p => [
				({ anjun 4m 5m 6m } { anjun 4s 5s 6s } { ankou S S S } { anjun 4p 5p 6p ryanmen_right } { G G }) => {
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
				({ anjun 1m 2m 3m } { anjun 4m 0m 6m } { anjun 7m 8m 9m } { anjun 2p 3p 4p ryanmen_left } { 5s 5s }) => {
					is_ittsuu();
				}
			]
			+ 5p => [
				({ anjun 1m 2m 3m } { anjun 4m 0m 6m } { anjun 7m 8m 9m } { anjun 3p 4p 5p ryanmen_right } { 5s 5s }) => {
					is_ittsuu();
				}
			]
		);

		test!((1m 2m 3m 4m 4m 5p 6p { minjun 5m 6m 7m } { minjun 7m 8m 9m })
			+ 4p => [
				({ anjun 1m 2m 3m } { minjun 5m 6m 7m } { minjun 7m 8m 9m } { anjun 4p 5p 6p ryanmen_left } { 4m 4m }) => {
					!is_ittsuu();
				}
			]
			+ 7p => [
				({ anjun 1m 2m 3m } { minjun 5m 6m 7m } { minjun 7m 8m 9m } { anjun 5p 6p 7p ryanmen_right } { 4m 4m }) => {
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
				({ ankou 6m 6m 6m } { ankou 4s 4s 4s } { ankou N N N } { anjun 1p 2p 3p ryanmen_left } { 8p 8p }) => {
					is_sanankou();
				}
			]
			+ 4p => [
				({ ankou 6m 6m 6m } { ankou 4s 4s 4s } { ankou N N N } { anjun 2p 3p 4p ryanmen_right } { 8p 8p }) => {
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
				({ ankou 3m 3m 3m } { ankou 3s 3s 3s } { minkou 3p 3p 3p } { anjun 5s 6s 7s ryanmen_left } { W W }) => {
					is_sanshoku_doukou();
				}
			]
			+ 8s => [
				({ ankou 3m 3m 3m } { ankou 3s 3s 3s } { minkou 3p 3p 3p } { anjun 6s 7s 8s ryanmen_right } { W W }) => {
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
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 3s 4s 5s ryanmen_left } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
			]
			+ 6s => [
				({ ankou 3m 3m 3m } { anjun 4s 5s 6s } { minkou 3p 3p 3p } { ankou 6s 6s 6s shanpon } { 3s 3s }) => {
					!is_sanshoku_doukou();
				}
				({ ankou 3m 3m 3m } { ankou 6s 6s 6s } { minkou 3p 3p 3p } { anjun 4s 5s 6s ryanmen_right } { 3s 3s }) => {
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
				({ anjun 3p 4p 0p } { ankou G G G } { minkou Wh Wh Wh } { anjun 1m 2m 3m ryanmen_left } { R R }) => {
					is_shousangen();
				}
			]
			+ 4m => [
				({ anjun 3p 4p 0p } { ankou G G G } { minkou Wh Wh Wh } { anjun 2m 3m 4m ryanmen_right } { R R }) => {
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
				({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_right } { G G }) => {
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
				({ anjun 1m 2m 3m } { ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 7s 8s 9s ryanmen_right } { 1s 1s }) => {
					is_junchan();
					!is_chanta();
					!is_honroutou();
					!is_tsuuiisou();
					!is_chinroutou();
				}
			]
			+ 6s => [
				({ anjun 1m 2m 3m } { ankou 9m 9m 9m } { anjun 7p 8p 9p } { anjun 6s 7s 8s ryanmen_left } { 1s 1s }) => {
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
				}
				({ 4m 4m } { 5m 5m } { 6m 6m } { 6p 6p } { 7p 7p } { 8p 8p } { 2s 2s }) => {
					!is_ryanpeikou();
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Ryanpeikou&oldid=27706

		test!((2p 2p 3p 3p 4p 4p 6m 6m 7m 7m 8m 1s 1s)
			+ 8m => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6m 7m 8m } { anjun 6m 7m 8m ryanmen_right } { 1s 1s }) => {
					is_ryanpeikou();
				}
				({ 2p 2p } { 3p 3p } { 4p 4p } { 6m 6m } { 7m 7m } { 8m 8m } { 1s 1s }) => {
					!is_ryanpeikou();
				}
			]
			+ 5m => [
				({ anjun 2p 3p 4p } { anjun 2p 3p 4p } { anjun 6m 7m 8m } { anjun 5m 6m 7m ryanmen_left } { 1s 1s }) => {
					!is_ryanpeikou();
					is_iipeikou();
					is_pinfu(tw!(E), tw!(E));
				}
			]
		);

		test!((2m 2m 3m 3m 4m 4m 4m 4m 7p 8p 8p 9p 9p)
			+ 7p => [
				({ anjun 2m 3m 4m } { anjun 2m 3m 4m } { anjun 7p 8p 9p } { anjun 7p 8p 9p penchan } { 4m 4m }) => {
					is_ryanpeikou();
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
				({ anjun 4m 5m 6m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 1m 2m 3m ryanmen_left } { 9m 9m }) => {
					is_chinitsu();
				}
			]
			+ 4m => [
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 4m 5m 6m ryanmen_left } { 9m 9m }) => {
					is_chinitsu();
				}
				({ anjun 4m 5m 6m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 2m 3m 4m ryanmen_right } { 9m 9m }) => {
					is_chinitsu();
				}
			]
			+ 7m => [
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 5m 6m 7m } { anjun 6m 7m 8m kanchan } { 9m 9m }) => {
					is_chinitsu();
				}
				({ anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 6m 7m 8m } { anjun 5m 6m 7m ryanmen_right } { 9m 9m }) => {
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
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s ryanmen_left } { 6s 6s }) => {
					is_chinitsu();
				}
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s } { 6s 6s }) => {
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
				({ anjun 1s 2s 3s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 7s 8s 9s ryanmen_right } { 6s 6s }) => {
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
				({ ankou 3p 3p 3p } { ankou 7s 7s 7s } { ankan 1s 1s 1s 1s } { anjun 2s 3s 4s ryanmen_right } { 2s 2s }) => {
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
				({ ankou 4s 4s 4s } { ankou 6s 6s 6s } { ankou G G G } { anjun 1s 2s 3s ryanmen_left } { 8s 8s }) => {
					!is_ryuuiisou();
				}
			]
			+ 4s => [
				({ anjun 2s 3s 4s } { ankou 6s 6s 6s } { ankou G G G } { ankou 4s 4s 4s shanpon } { 8s 8s }) => {
					is_ryuuiisou();
				}
				({ ankou 4s 4s 4s } { ankou 6s 6s 6s } { ankou G G G } { anjun 2s 3s 4s ryanmen_right } { 8s 8s }) => {
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
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 1m 2m 3m ryanmen_left } { 9m 9m }) => {
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
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 3m 4m 5m ryanmen_left } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 3m 4m 5m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 1m 2m 3m penchan } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 4m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 4m 5m 6m ryanmen_left } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1m 1m 1m } { anjun 4m 5m 6m } { anjun 7m 8m 9m } { anjun 2m 3m 4m ryanmen_right } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 5m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { 5m 5m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 6m => [
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 6m 7m 8m ryanmen_left } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1m 2m 3m } { anjun 6m 7m 8m } { ankou 9m 9m 9m } { anjun 4m 5m 6m ryanmen_right } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 7m => [
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 5m 6m 7m } { anjun 7m 8m 9m penchan } { 9m 9m }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1m 1m 1m } { anjun 2m 3m 4m } { anjun 7m 8m 9m } { anjun 5m 6m 7m ryanmen_right } { 9m 9m }) => {
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
				({ anjun 1m 2m 3m } { anjun 4m 5m 6m } { ankou 9m 9m 9m } { anjun 7m 8m 9m ryanmen_right } { 1m 1m }) => {
					num_chuuren_poutou() == 2;
				}
			]
		);

		// Ref: https://riichi.wiki/index.php?title=Chuuren_poutou&oldid=27609

		test!((1p 1p 1p 2p 3p 4p 5p 5p 7p 8p 9p 9p 9p)
			+ 6p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { ankou 9p 9p 9p } { anjun 6p 7p 8p ryanmen_left } { 5p 5p }) => {
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
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { ankou 9p 9p 9p } { anjun 7p 8p 9p ryanmen_right } { 5p 5p }) => {
					num_chuuren_poutou() == 0;
				}
			]
		);

		test!((1p 1p 1p 2p 3p 4p 5p 6p 7p 8p 9p 9p 9p)
			+ 1p => [
				({ ankou 1p 1p 1p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { anjun 1p 2p 3p ryanmen_left } { 9p 9p }) => {
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
				({ anjun 1p 2p 3p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 3p 4p 5p ryanmen_left } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 3p 4p 5p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 1p 2p 3p penchan } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 4p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { anjun 4p 5p 6p ryanmen_left } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1p 1p 1p } { anjun 4p 5p 6p } { anjun 7p 8p 9p } { anjun 2p 3p 4p ryanmen_right } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 5p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { 5p 5p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 6p => [
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 6p 7p 8p ryanmen_left } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
				({ anjun 1p 2p 3p } { anjun 6p 7p 8p } { ankou 9p 9p 9p } { anjun 4p 5p 6p ryanmen_right } { 1p 1p }) => {
					num_chuuren_poutou() == 2;
				}
			]
			+ 7p => [
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 5p 6p 7p } { anjun 7p 8p 9p penchan } { 9p 9p }) => {
					num_chuuren_poutou() == 2;
				}
				({ ankou 1p 1p 1p } { anjun 2p 3p 4p } { anjun 7p 8p 9p } { anjun 5p 6p 7p ryanmen_right } { 9p 9p }) => {
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
				({ anjun 1p 2p 3p } { anjun 4p 5p 6p } { ankou 9p 9p 9p } { anjun 7p 8p 9p ryanmen_right } { 1p 1p }) => {
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
}
