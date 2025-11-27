use crate::{
	MultiSet,
	NumberTile,
	ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair,
	Tile, TsumoOrRon,
	concat,
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
/// If any of these expectations are violated, the program will still be safe, but `to_scorable_hands()`
/// will produce an unspecified and meaningless result. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy)]
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
/// - `Minjun` really contains three [`NumberTile`]s that would form a valid sequence.
///
/// - `Minkou` really contains three of the same [`Tile`], except that if two of them are [`Number::Five`][crate::Number::Five]s
///   then the third may be a [`Number::FiveRed`][crate::Number::FiveRed].
///
/// - `Minkan` really contains four of the same [`Tile`], except that if three of them are [`Number::Five`][crate::Number::Five]s
///   then the fourth may be a [`Number::FiveRed`][crate::Number::FiveRed].
///
/// - There are not more of any one [`Tile`] than are present in a game.
///
/// If any of these expectations are violated, the program will still be safe, but `to_scorable_hands()`
/// will produce an unspecified and meaningless result. Therefore it is recommended to always satisfy these expectations.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum HandMeld {
	/// Open sequence formed by chii.
	Minjun([NumberTile; 3]),
	/// Open triplet formed by pon.
	Minkou([Tile; 3]),
	/// Closed quad formed by kan.
	Ankan([Tile; 4]),
	/// Open quad formed by kan.
	Minkan([Tile; 4]),
}

/// A hand containing some number of tiles and melds when it's not the player's turn.
///
/// This enum is a way to hold all possible stable hand types during a game.
#[derive(Clone, Copy)]
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
#[derive(Clone, Copy)]
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

assert_size_of!(Hand<1, 4>, 38);
assert_size_of!(Hand<2, 4>, 40);
assert_size_of!(Hand<4, 3>, 35);
assert_size_of!(Hand<5, 3>, 37);
assert_size_of!(Hand<7, 2>, 32);
assert_size_of!(Hand<8, 2>, 34);
assert_size_of!(Hand<10, 1>, 29);
assert_size_of!(Hand<11, 1>, 31);
assert_size_of!(Hand<13, 0>, 26);
assert_size_of!(Hand<14, 0>, 28);
assert_size_of!(HandMeld, 9);

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandStable: From<Self>,
{
	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> std::pin::Pin<Box<Minjuns<NT, NM>>> {
		Minjuns::new(self, new_tile)
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> std::pin::Pin<Box<Minkous<NT, NM>>> {
		Minkous::new(self, new_tile)
	}

	/// Find a possible shouminkan (quad via kan call on a minkou formed previously) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_shouminkan(self, new_tile: Tile) -> Option<Self> {
		let Self(ts, ms) = self;
		Some(Self(ts, find_shouminkan(ms, new_tile)?))
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NT + 1 }>` that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Hand<{ NT - 3 }, { NM + 1 }>> {
		let Self(ts, ms) = self;
		find_kan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, concat(ms, [HandMeld::Minkan(m_new)])))
	}

	/// Find a possible ankan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the `Hand<{ NT - 3 }, NT + 1 }>` that would result from this call, if any.
	pub fn find_ankan(self, new_tile: Tile) -> Option<Hand<{ NT - 3 }, { NM + 1 }>> {
		let Self(ts, ms) = self;
		find_kan(ts, new_tile).map(move |(ts, m_new)| Hand(ts, concat(ms, [HandMeld::Ankan(m_new)])))
	}
}

impl<const NT: usize, const NM: usize> Hand<NT, NM>
where
	HandStable: From<Hand<{ NT - 1 }, NM>>,
{
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the `Hand<{ NT - 1 }, NM>` resulting from the discard of that tile, and the discarded tile.
	pub fn discard(self, i: usize) -> (Hand<{ NT - 1 }, NM>, Tile) {
		let Self(ts, ms) = self;
		let (ts, [t_discard]) = unsafe { except(ts, [i]) };
		(Hand(ts, ms), t_discard)
	}
}

impl<const NT: usize, const NM: usize> std::fmt::Debug for Hand<NT, NM>
where
	Hand<NT, NM>: std::fmt::Display,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl<const NT: usize, const NM: usize> std::fmt::Display for Hand<NT, NM> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
	pub fn to_scorable_hands(self, new_tile: Tile) -> Option<ScorableHand> {
		let Self([t1], ms) = self;

		if t1 == new_tile {
			let mut ms = ms.map(Into::into);
			ms.sort_unstable();
			let [m1, m2, m3, m4] = ms;
			Some(ScorableHand::Regular { melds: ([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4)), pair: ScorableHandPair([t1, new_tile]) })
		}
		else {
			None
		}
	}
}

impl Hand<4, 3> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let mut result: std::collections::BTreeSet<_> = Default::default();

		let mut ms = ms.map(Into::into);
		ms.sort_unstable();

		let mut ts = concat(ts.map(|t| (t, TileProps::NotNewTile)), [(new_tile, tsumo_or_ron.into())]);
		ts.sort_unstable();

		for (i, &[(pt1, _), (pt2, _)]) in ts.array_windows().enumerate() {
			if pt1 == pt2 {
				let rest = unsafe { skip_adjacent_2(ts, i) };
				let Some(m4) = to_meld(rest) else { continue; };
				let melds = match m4 {
					ScorableHandFourthMeld::Tanki(m4) => {
						let mut ms = concat(ms, [m4]);
						ms.sort_unstable();
						let [m1, m2, m3, m4] = ms;
						([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
					},
					m4 => (ms, m4),
				};
				result.insert(ScorableHand::Regular {
					melds,
					pair: ScorableHandPair([pt1, pt2]),
				});
			}
		}

		result
	}
}

impl Hand<7, 2> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let mut result: std::collections::BTreeSet<_> = Default::default();

		let mut ms = ms.map(Into::into);
		ms.sort_unstable();

		let mut ts = concat(ts.map(|t| (t, TileProps::NotNewTile)), [(new_tile, tsumo_or_ron.into())]);
		ts.sort_unstable();

		for (i, &[(pt1, _), (pt2, _)]) in ts.array_windows().enumerate() {
			if pt1 == pt2 {
				let rest = unsafe { skip_adjacent_2(ts, i) };
				for (m3, m4) in to_melds_2(rest) {
					let melds = match m4 {
						ScorableHandFourthMeld::Tanki(m4) => {
							let mut ms = concat(ms, [m3, m4]);
							ms.sort_unstable();
							let [m1, m2, m3, m4] = ms;
							([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
						},
						m4 => {
							let mut ms = concat(ms, [m3]);
							ms.sort_unstable();
							let [m1, m2, m3] = ms;
							([m1, m2, m3], m4)
						},
					};
					result.insert(ScorableHand::Regular {
						melds,
						pair: ScorableHandPair([pt1, pt2]),
					});
				}
			}
		}

		result
	}
}

impl Hand<10, 1> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, ms) = self;
		let mut result: std::collections::BTreeSet<_> = Default::default();

		let mut ms = ms.map(Into::into);
		ms.sort_unstable();

		let mut ts = concat(ts.map(|t| (t, TileProps::NotNewTile)), [(new_tile, tsumo_or_ron.into())]);
		ts.sort_unstable();

		for (i, &[(pt1, _), (pt2, _)]) in ts.array_windows().enumerate() {
			if pt1 == pt2 {
				let rest = unsafe { skip_adjacent_2(ts, i) };
				result.extend(
					to_melds_3(rest)
					.into_iter()
					.map(|([m2, m3], m4)| {
						let melds = match m4 {
							ScorableHandFourthMeld::Tanki(m4) => {
								let mut ms = concat(ms, [m2, m3, m4]);
								ms.sort_unstable();
								let [m1, m2, m3, m4] = ms;
								([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
							},
							m4 => {
								let mut ms = concat(ms, [m2, m3]);
								ms.sort_unstable();
								let [m1, m2, m3] = ms;
								([m1, m2, m3], m4)
							},
						};
						ScorableHand::Regular {
							melds,
							pair: ScorableHandPair([pt1, pt2]),
						}
					}),
				);
			}
		}

		result
	}
}

impl Hand<13, 0> {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		let Self(ts, []) = self;
		let mut result: std::collections::BTreeSet<_> = Default::default();

		let mut ts = concat(ts.map(|t| (t, TileProps::NotNewTile)), [(new_tile, tsumo_or_ron.into())]);
		ts.sort_unstable();

		for (i, &[(pt1, _), (pt2, _)]) in ts.array_windows().enumerate() {
			if pt1 == pt2 {
				let rest = unsafe { skip_adjacent_2(ts, i) };
				result.extend(
					to_melds_4(rest)
					.into_iter()
					.map(|([m1, m2, m3], m4)| {
						let melds = match m4 {
							ScorableHandFourthMeld::Tanki(m4) => {
								let mut ms = [m1, m2, m3, m4];
								ms.sort_unstable();
								let [m1, m2, m3, m4] = ms;
								([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
							},
							m4 => {
								let mut ms = [m1, m2, m3];
								ms.sort_unstable();
								let [m1, m2, m3] = ms;
								([m1, m2, m3], m4)
							},
						};
						ScorableHand::Regular {
							melds,
							pair: ScorableHandPair([pt1, pt2]),
						}
					}),
				);
			}
		}

		if let Some(h) = to_chiitoi(ts) {
			result.insert(h);
		}

		if let Some(h) = to_kokushi_musou(ts, new_tile) {
			result.insert(h);
		}

		result
	}
}

impl std::fmt::Debug for HandMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(self, f)
	}
}

impl std::fmt::Display for HandMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Minjun([t1, t2, t3]) =>
				write!(f, "{{ minjun {t1} {t2} {t3} }}"),
			Self::Minkou([t1, t2, t3]) =>
				write!(f, "{{ minkou {t1} {t2} {t3} }}"),
			Self::Ankan([t1, t2, t3, t4]) =>
				write!(f, "{{ ankan {t1} {t2} {t3} {t4} }}"),
			Self::Minkan([t1, t2, t3, t4]) =>
				write!(f, "{{ minkan {t1} {t2} {t3} {t4} }}"),
		}
	}
}

impl Ord for HandMeld {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		let t = match *self {
			Self::Minjun([t, ..]) => Tile::Number(t),
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => t,
		};
		let t_other = match *other {
			Self::Minjun([t, ..]) => Tile::Number(t),
			Self::Minkou([t, ..]) |
			Self::Ankan([t, ..]) |
			Self::Minkan([t, ..]) => t,
		};
		#[expect(clippy::match_same_arms)]
		t.cmp(&t_other).then_with(|| match (self, other) {
			(Self::Minjun(_), Self::Minjun(_)) => std::cmp::Ordering::Equal,
			(Self::Minjun(_), Self::Minkou(_) | Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minkou(_), Self::Minjun(_)) => std::cmp::Ordering::Greater,
			(Self::Minkou(_), Self::Minkou(_)) => std::cmp::Ordering::Equal,
			(Self::Minkou(_), Self::Ankan(_) | Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Ankan(_), Self::Minjun(_) | Self::Minkou(_)) => std::cmp::Ordering::Greater,
			(Self::Ankan(_), Self::Ankan(_)) => std::cmp::Ordering::Equal,
			(Self::Ankan(_), Self::Minkan(_)) => std::cmp::Ordering::Less,

			(Self::Minkan(_), Self::Minjun(_) | Self::Minkou(_) | Self::Ankan(_)) => std::cmp::Ordering::Greater,
			(Self::Minkan(_), Self::Minkan(_)) => std::cmp::Ordering::Equal,
		})
	}
}

impl PartialOrd for HandMeld {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl HandStable {
	/// Add the given drawn / called tile to this hand and convert it into a set of [`ScorableHand`]s.
	///
	/// Note that a `ScorableHand` is defined as a hand that has a winning shape,
	/// but does not necessarily have any yaku and so may not necessarily win the round.
	/// This is because the determination of whether a hand can win or not depends on external factors
	/// like winds, riichi, etc that is not tracked by `Hand` / `ScorableHand`.
	///
	/// Also note that the order of elements in the returned set does not correspond to the hands' scores.
	///
	/// Returns an empty set if a scorable hand cannot be formed with the new tile.
	pub fn to_scorable_hands(self, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> std::collections::BTreeSet<ScorableHand> {
		match self {
			Self::One(h) => h.to_scorable_hands(new_tile).into_iter().collect(),
			Self::Four(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
			Self::Seven(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
			Self::Ten(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
			Self::Thirteen(h) => h.to_scorable_hands(new_tile, tsumo_or_ron),
		}
	}

	/// Find all possible minjuns (sequence via chii call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minjuns(self, new_tile: NumberTile) -> Box<dyn Iterator<Item = HandTentative>> {
		match self {
			Self::One(_) => Box::new([].into_iter()),
			Self::Four(h) => Box::new(h.find_minjuns(new_tile).map(HandTentative::Two)),
			Self::Seven(h) => Box::new(h.find_minjuns(new_tile).map(HandTentative::Five)),
			Self::Ten(h) => Box::new(h.find_minjuns(new_tile).map(HandTentative::Eight)),
			Self::Thirteen(h) => Box::new(h.find_minjuns(new_tile).map(HandTentative::Eleven)),
		}
	}

	/// Find all possible minkous (triplet via pon call) using the given new tile.
	///
	/// Returns an `Iterator` of all possible hands that would result from this call.
	pub fn find_minkous(self, new_tile: Tile) -> Box<dyn Iterator<Item = HandTentative>> {
		match self {
			Self::One(_) => Box::new([].into_iter()),
			Self::Four(h) => Box::new(h.find_minkous(new_tile).map(HandTentative::Two)),
			Self::Seven(h) => Box::new(h.find_minkous(new_tile).map(HandTentative::Five)),
			Self::Ten(h) => Box::new(h.find_minkous(new_tile).map(HandTentative::Eight)),
			Self::Thirteen(h) => Box::new(h.find_minkous(new_tile).map(HandTentative::Eleven)),
		}
	}

	/// Find a possible shouminkan (quad via kan call on a minkou formed previously) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_shouminkan(self, new_tile: Tile) -> Option<Self> {
		Some(match self {
			Self::One(h) => Self::One(h.find_shouminkan(new_tile)?),
			Self::Four(h) => Self::Four(h.find_shouminkan(new_tile)?),
			Self::Seven(h) => Self::Seven(h.find_shouminkan(new_tile)?),
			Self::Ten(h) => Self::Ten(h.find_shouminkan(new_tile)?),
			Self::Thirteen(h) => Self::Thirteen(h.find_shouminkan(new_tile)?),
		})
	}

	/// Find a possible daiminkan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_daiminkan(self, new_tile: Tile) -> Option<Self> {
		Some(match self {
			Self::One(_) => return None,
			Self::Four(h) => Self::One(h.find_daiminkan(new_tile)?),
			Self::Seven(h) => Self::Four(h.find_daiminkan(new_tile)?),
			Self::Ten(h) => Self::Seven(h.find_daiminkan(new_tile)?),
			Self::Thirteen(h) => Self::Ten(h.find_daiminkan(new_tile)?),
		})
	}

	/// Find a possible ankan (quad via kan call on a triplet held in the hand) using the given new tile.
	///
	/// Returns the hand that would result from this call, if any.
	pub fn find_ankan(self, new_tile: Tile) -> Option<Self> {
		Some(match self {
			Self::One(_) => return None,
			Self::Four(h) => Self::One(h.find_ankan(new_tile)?),
			Self::Seven(h) => Self::Four(h.find_ankan(new_tile)?),
			Self::Ten(h) => Self::Seven(h.find_ankan(new_tile)?),
			Self::Thirteen(h) => Self::Ten(h.find_ankan(new_tile)?),
		})
	}
}

impl HandTentative {
	/// Discard the tile at the given index from this hand.
	///
	/// Returns the hand resulting from the discard of that tile, and the discarded tile.
	pub fn discard(self, i: usize) -> (HandStable, Tile) {
		match self {
			Self::Two(h) => { let (h, t) = h.discard(i); (HandStable::One(h), t) },
			Self::Five(h) => { let (h, t) = h.discard(i); (HandStable::Four(h), t) },
			Self::Eight(h) => { let (h, t) = h.discard(i); (HandStable::Seven(h), t) },
			Self::Eleven(h) => { let (h, t) = h.discard(i); (HandStable::Ten(h), t) },
			Self::Fourteen(h) => { let (h, t) = h.discard(i); (HandStable::Thirteen(h), t) },
		}
	}
}

macro_rules! hand_enum_from {
	($($nt:expr, $nm:expr => $ty:tt :: $variant:ident ,)*) => {
		$(
			impl From<Hand<$nt, $nm>> for $ty {
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

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minjun
/// in the given hand using the given new tile.
pub struct Minjuns<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	new_tile: NumberTile,
	ts_consider_raw: [std::mem::MaybeUninit<(usize, NumberTile)>; NT],
	combinations: const_combinations::SliceCombinations<'static, (usize, NumberTile), 2>,
	pinned: std::marker::PhantomPinned,
}

impl<const NT: usize, const NM: usize> Minjuns<NT, NM> {
	fn new(
		hand: Hand<NT, NM>,
		new_tile: NumberTile,
	) -> std::pin::Pin<Box<Self>> {
		let mut result: Box<std::mem::MaybeUninit<Self>> = Box::new(std::mem::MaybeUninit::uninit());
		let result_ptr = result.as_mut_ptr();

		unsafe { (&raw mut (*result_ptr).hand).write(hand); }

		unsafe { (&raw mut (*result_ptr).new_tile).write(new_tile); }

		let ts_consider_raw = [std::mem::MaybeUninit::uninit(); NT];
		unsafe { (&raw mut (*result_ptr).ts_consider_raw).write(ts_consider_raw); }
		let ts_consider_raw = unsafe { &mut (*result_ptr).ts_consider_raw };

		let ts_consider = {
			let mut j = 0;
			let ts_consider =
				hand.0.into_iter()
				.enumerate()
				.filter_map(|(i, t)|
					if let Tile::Number(t) = t && t.suit == new_tile.suit && t.number.value().abs_diff(new_tile.number.value()) <= 2 {
						Some((i, t))
					}
					else {
						None
					},
				);
			for (i, t) in ts_consider {
				ts_consider_raw[j].write((i, t));
				j += 1;
			}
			unsafe { ts_consider_raw[..j].assume_init_ref() }
		};

		let combinations = const_combinations::SliceExt::combinations(ts_consider);
		unsafe { (&raw mut (*result_ptr).combinations).write(combinations); }

		unsafe { (&raw mut (*result_ptr).pinned).write(Default::default()); }

		let result = unsafe { result.assume_init() };
		Box::into_pin(result)
	}
}

impl<const NT: usize, const NM: usize> std::fmt::Debug for Minjuns<NT, NM> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("Minjuns")
			.field("hand", &self.hand)
			.field("new_tile", &self.new_tile)
			.finish_non_exhaustive()
	}
}

impl<const NT: usize, const NM: usize> Iterator for std::pin::Pin<Box<Minjuns<NT, NM>>>
where
	[(); NT - 2]:,
	[(); NM + 1]:,
{
	type Item = Hand<{ NT - 2 }, { NM + 1 }>;

	fn next(&mut self) -> Option<Self::Item> {
		let this = unsafe { self.as_mut().get_unchecked_mut() };
		loop {
			let [&(i1, t1), &(i2, t2)] = this.combinations.next()?;
			let [t1, t2, t3] = {
				let mut ts = [t1, t2, this.new_tile];
				ts.sort_unstable();
				ts
			};
			if is_shun([t1, t2, t3]) {
				let m = HandMeld::Minjun([t1, t2, t3]);
				let (ts, _) = unsafe { except(this.hand.0, [i1, i2]) };
				return Some(Hand(ts, concat(this.hand.1, [m])));
			}
		}
	}
}

/// [`Iterator`] of [`Hand<{ NT - 2 }, { NM + 1 }>`](Hand) values formed by creating a minkou
/// in the given hand using the given new tile.
pub struct Minkous<const NT: usize, const NM: usize> {
	hand: Hand<NT, NM>,
	new_tile: Tile,
	ts_consider_raw: [std::mem::MaybeUninit<(usize, Tile)>; NT],
	combinations: const_combinations::SliceCombinations<'static, (usize, Tile), 2>,
	pinned: std::marker::PhantomPinned,
}

impl<const NT: usize, const NM: usize> Minkous<NT, NM> {
	fn new(
		hand: Hand<NT, NM>,
		new_tile: Tile,
	) -> std::pin::Pin<Box<Self>> {
		let mut result: Box<std::mem::MaybeUninit<Self>> = Box::new(std::mem::MaybeUninit::uninit());
		let result_ptr = result.as_mut_ptr();

		unsafe { (&raw mut (*result_ptr).hand).write(hand); }

		unsafe { (&raw mut (*result_ptr).new_tile).write(new_tile); }

		let ts_consider_raw = [std::mem::MaybeUninit::uninit(); NT];
		unsafe { (&raw mut (*result_ptr).ts_consider_raw).write(ts_consider_raw); }
		let ts_consider_raw = unsafe { &mut (*result_ptr).ts_consider_raw };

		let ts_consider = {
			let mut j = 0;
			for (i, t) in hand.0.into_iter().enumerate().filter(|&(_, t)| t == new_tile) {
				ts_consider_raw[j].write((i, t));
				j += 1;
			}
			unsafe { ts_consider_raw[..j].assume_init_ref() }
		};

		let combinations = const_combinations::SliceExt::combinations(ts_consider);
		unsafe { (&raw mut (*result_ptr).combinations).write(combinations); }

		unsafe { (&raw mut (*result_ptr).pinned).write(Default::default()); }

		let result = unsafe { result.assume_init() };
		Box::into_pin(result)
	}
}

impl<const NT: usize, const NM: usize> std::fmt::Debug for Minkous<NT, NM> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("Minkous")
			.field("hand", &self.hand)
			.field("new_tile", &self.new_tile)
			.finish_non_exhaustive()
	}
}

impl<const NT: usize, const NM: usize> Iterator for std::pin::Pin<Box<Minkous<NT, NM>>>
where
	[(); NT - 2]:,
	[(); NM + 1]:,
{
	type Item = Hand<{ NT - 2 }, { NM + 1 }>;

	fn next(&mut self) -> Option<Self::Item> {
		let this = unsafe { self.as_mut().get_unchecked_mut() };
		loop {
			let [&(i1, t1), &(i2, t2)] = this.combinations.next()?;
			let ts = [t1, t2, this.new_tile];
			if is_kou(ts) {
				let m = HandMeld::Minkou(ts);
				let (ts, _) = unsafe { except(this.hand.0, [i1, i2]) };
				return Some(Hand(ts, concat(this.hand.1, [m])));
			}
		}
	}
}

fn find_shouminkan<const N: usize>(mut ms: [HandMeld; N], new_tile: Tile) -> Option<[HandMeld; N]> {
	let mut found = false;
	for m in &mut ms {
		if let HandMeld::Minkou([t1, t2, t3]) = *m && t1 == new_tile {
			*m = HandMeld::Minkan([t1, t2, t3, new_tile]);
			found = true;
			break;
		}
	}
	found.then_some(ms)
}

fn find_kan<const N: usize>(
	ts: [Tile; N],
	new_tile: Tile,
) -> Option<([Tile; N - 3], [Tile; 4])> {
	let [(i1, t1), (i2, t2), (i3, t3)] = ts.into_iter().enumerate().filter(|&(_, t)| t == new_tile).next_chunk().ok()?;
	let m = [t1, t2, t3, new_tile];
	let (ts, _) = unsafe { except(ts, [i1, i2, i3]) };
	Some((ts, m))
}

/// # Safety
///
/// Every element of `i_discard` must be distinct and within the bounds of `ts`.
unsafe fn except<T, const N: usize, const DN: usize>(
	ts: [T; N],
	i_discard: [usize; DN],
) -> ([T; N - DN], [T; DN]) {
	let mut discards = [const { std::mem::MaybeUninit::uninit() }; DN];
	let mut discards_i = 0_usize;
	let mut ts_result = [const { std::mem::MaybeUninit::uninit() }; N - DN];
	let mut ts_result_i = 0_usize;
	'outer: for (i, t) in ts.into_iter().enumerate() {
		for i_discard in i_discard {
			if i == i_discard {
				discards[discards_i].write(t);
				discards_i += 1;
				continue 'outer;
			}
		}

		ts_result[ts_result_i].write(t);
		ts_result_i += 1;
	}
	let discards = unsafe { std::mem::MaybeUninit::array_assume_init(discards) };
	let ts_result = unsafe { std::mem::MaybeUninit::array_assume_init(ts_result) };
	(ts_result, discards)
}

/// # Safety
///
/// `pt1_i` must be within the bounds of `ts`.
unsafe fn skip_adjacent_2<T, const N: usize>(ts: [T; N], pt1_i: usize) -> [T; N - 2]
where
	T: Copy,
{
	let rest = ts.into_iter().take(pt1_i).chain(ts.into_iter().skip(pt1_i + 2)).next_chunk();
	unsafe { rest.unwrap_unchecked() }
}

fn is_shun([t1, t2, t3]: [NumberTile; 3]) -> bool {
	t2.is_next_in_sequence(t1) && t3.is_next_in_sequence(t2)
}

fn is_kou([t1, t2, t3]: [Tile; 3]) -> bool {
	t1 == t2 && t2 == t3
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum TileProps {
	NotNewTile,
	NewTileViaTsumo,
	NewTileViaRon,
}

impl TileProps {
	fn is_new_tile(self) -> bool {
		matches!(self, Self::NewTileViaTsumo | Self::NewTileViaRon)
	}
}

impl From<TsumoOrRon> for TileProps {
	fn from(tsumo_or_ron: TsumoOrRon) -> Self {
		match tsumo_or_ron {
			TsumoOrRon::Tsumo => Self::NewTileViaTsumo,
			TsumoOrRon::Ron => Self::NewTileViaRon,
		}
	}
}

fn to_meld([(t1, t1p), (t2, t2p), (t3, t3p)]: [(Tile, TileProps); 3]) -> Option<ScorableHandFourthMeld> {
	let was_completed_with_ron =
		matches!(t1p, TileProps::NewTileViaRon) ||
		matches!(t2p, TileProps::NewTileViaRon) ||
		matches!(t3p, TileProps::NewTileViaRon);
	let tsumo_or_ron = if was_completed_with_ron { TsumoOrRon::Ron } else { TsumoOrRon::Tsumo };

	if is_kou([t1, t2, t3]) {
		let is_fourth_meld = t1p.is_new_tile() || t2p.is_new_tile() || t3p.is_new_tile();
		if is_fourth_meld {
			Some(ScorableHandFourthMeld::Shanpon { tiles: [t1, t2, t3], tsumo_or_ron })
		}
		else {
			Some(ScorableHandFourthMeld::Tanki(ScorableHandMeld::Ankou([t1, t2, t3])))
		}
	}
	else if let Tile::Number(t1) = t1 && let Tile::Number(t2) = t2 && let Tile::Number(t3) = t3 && is_shun([t1, t2, t3]) {
		let is_fourth_meld = t1p.is_new_tile() || t2p.is_new_tile() || t3p.is_new_tile();
		if is_fourth_meld {
			if t2p.is_new_tile() {
				Some(ScorableHandFourthMeld::Kanchan { tiles: [t1, t2, t3], tsumo_or_ron })
			}
			else if (t1p.is_new_tile() && t3.number.value() == 9) || (t3p.is_new_tile() && t1.number.value() == 1) {
				Some(ScorableHandFourthMeld::Penchan { tiles: [t1, t2, t3], tsumo_or_ron })
			}
			else if t1p.is_new_tile() {
				Some(ScorableHandFourthMeld::RyanmenLeft { tiles: [t1, t2, t3], tsumo_or_ron })
			}
			else {
				Some(ScorableHandFourthMeld::RyanmenRight { tiles: [t1, t2, t3], tsumo_or_ron })
			}
		}
		else {
			Some(ScorableHandFourthMeld::Tanki(ScorableHandMeld::Anjun([t1, t2, t3])))
		}
	}
	else {
		None
	}
}

fn to_melds_2(ts: [(Tile, TileProps); 6]) -> std::collections::BTreeSet<(ScorableHandMeld, ScorableHandFourthMeld)> {
	let ts = indexify(ts);

	let mut result: std::collections::BTreeSet<_> = Default::default();

	// To reduce duplicate hands, put the first tile always in m1, then...
	let (_, t1) = ts[0];
	// ... for the second tile, there are two choices:

	// Either the second tile is in m1...
	{
		let (_, t2) = ts[1];
		for &(i3, t3) in &ts[2..] {
			let Some(m1) = to_meld([t1, t2, t3]) else { continue; };
			let ts = ts[2..].iter().filter(move |&&(i, _)| i != i3).copied().next_chunk();
			let [(_, t4), (_, t5), (_, t6)] = unsafe { ts.unwrap_unchecked() };
			let Some(m2) = to_meld([t4, t5, t6]) else { continue; };
			let ms = match (m1, m2) {
				(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2)) => {
					let mut ms = [m1, m2];
					ms.sort_unstable();
					let [m1, m2] = ms;
					(m1, ScorableHandFourthMeld::Tanki(m2))
				},

				(ScorableHandFourthMeld::Tanki(m1), m2) => (m1, m2),

				(m1, ScorableHandFourthMeld::Tanki(m2)) => (m2, m1),

				_ => unreachable!("at most one meld can be non-tanki"),
			};
			result.insert(ms);
		}
	}

	// ... or the second tile is in m2.
	{
		let (_, t4) = ts[1];
		for [&(i2, t2), &(i3, t3)] in const_combinations::SliceExt::combinations(&ts[2..]) {
			let Some(m1) = to_meld([t1, t2, t3]) else { continue; };
			let ts = ts[2..].iter().filter(move |&&(i, _)| i != i2 && i != i3).copied().next_chunk();
			let [(_, t5), (_, t6)] = unsafe { ts.unwrap_unchecked() };
			let Some(m2) = to_meld([t4, t5, t6]) else { continue; };
			let ms = match (m1, m2) {
				(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2)) => {
					let mut ms = [m1, m2];
					ms.sort_unstable();
					let [m1, m2] = ms;
					(m1, ScorableHandFourthMeld::Tanki(m2))
				},

				(ScorableHandFourthMeld::Tanki(m1), m2) => (m1, m2),

				(m1, ScorableHandFourthMeld::Tanki(m2)) => (m2, m1),

				_ => unreachable!("at most one meld can be non-tanki"),
			};
			result.insert(ms);
		}
	}

	result
}

fn to_melds_3(ts: [(Tile, TileProps); 9]) -> std::collections::BTreeSet<([ScorableHandMeld; 2], ScorableHandFourthMeld)> {
	let ts = indexify(ts);

	let mut result: std::collections::BTreeSet<_> = Default::default();

	// To reduce duplicate hands, put the first tile always in m1, then...
	let (_, t1) = ts[0];
	// ... for the second tile, there are two choices:

	// Either the second tile is in m1...
	{
		let (_, t2) = ts[1];
		for &(i3, t3) in &ts[2..] {
			let Some(m1) = to_meld([t1, t2, t3]) else { continue; };
			let ts = ts[2..].iter().filter(move |&&(i, _)| i != i3).copied().next_chunk();
			let [(_, t4), (_, t5), (_, t6), (_, t7), (_, t8), (_, t9)] = unsafe { ts.unwrap_unchecked() };
			for (m2, m3) in to_melds_2([t4, t5, t6, t7, t8, t9]) {
				let ms = match (m1, m3) {
					(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m3)) => {
						let mut ms = [m1, m2, m3];
						ms.sort_unstable();
						let [m1, m2, m3] = ms;
						([m1, m2], ScorableHandFourthMeld::Tanki(m3))
					},

					(ScorableHandFourthMeld::Tanki(m1), m3) => {
						let mut ms = [m1, m2];
						ms.sort_unstable();
						(ms, m3)
					},

					(m1, ScorableHandFourthMeld::Tanki(m3)) => {
						let mut ms = [m2, m3];
						ms.sort_unstable();
						(ms, m1)
					},

					_ => unreachable!("at most one meld can be non-tanki"),
				};
				result.insert(ms);
			}
		}
	}

	// ... or the second tile is in m2.
	{
		let (_, t4) = ts[1];
		for [&(i2, t2), &(i3, t3)] in const_combinations::SliceExt::combinations(&ts[2..]) {
			let Some(m1) = to_meld([t1, t2, t3]) else { continue; };
			let ts = ts[2..].iter().filter(move |&&(i, _)| i != i2 && i != i3).copied().next_chunk();
			let [(_, t5), (_, t6), (_, t7), (_, t8), (_, t9)] = unsafe { ts.unwrap_unchecked() };
			for (m2, m3) in to_melds_2([t4, t5, t6, t7, t8, t9]) {
				let ms = match (m1, m3) {
					(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m3)) => {
						let mut ms = [m1, m2, m3];
						ms.sort_unstable();
						let [m1, m2, m3] = ms;
						([m1, m2], ScorableHandFourthMeld::Tanki(m3))
					},

					(ScorableHandFourthMeld::Tanki(m1), m3) => {
						let mut ms = [m1, m2];
						ms.sort_unstable();
						(ms, m3)
					},

					(m1, ScorableHandFourthMeld::Tanki(m3)) => {
						let mut ms = [m2, m3];
						ms.sort_unstable();
						(ms, m1)
					},

					_ => unreachable!("at most one meld can be non-tanki"),
				};
				result.insert(ms);
			}
		}
	}

	result
}

fn to_melds_4(ts: [(Tile, TileProps); 12]) -> std::collections::BTreeSet<([ScorableHandMeld; 3], ScorableHandFourthMeld)> {
	let ts = indexify(ts);

	let mut result: std::collections::BTreeSet<_> = Default::default();

	// To reduce duplicate hands, put the first tile always in m1, then...
	let (_, t1) = ts[0];
	// ... for the second tile, there are two choices:

	// Either the second tile is in m1...
	{
		let (_, t2) = ts[1];
		for &(i3, t3) in &ts[2..] {
			let Some(m1) = to_meld([t1, t2, t3]) else { continue; };
			let ts = ts[2..].iter().filter(move |&&(i, _)| i != i3).copied().next_chunk();
			let [(_, t4), (_, t5), (_, t6), (_, t7), (_, t8), (_, t9), (_, t10), (_, t11), (_, t12)] = unsafe { ts.unwrap_unchecked() };
			for ([m2, m3], m4) in to_melds_3([t4, t5, t6, t7, t8, t9, t10, t11, t12]) {
				let ms = match (m1, m4) {
					(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m4)) => {
						let mut ms = [m1, m2, m3, m4];
						ms.sort_unstable();
						let [m1, m2, m3, m4] = ms;
						([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
					},

					(ScorableHandFourthMeld::Tanki(m1), m4) => {
						let mut ms = [m1, m2, m3];
						ms.sort_unstable();
						(ms, m4)
					},

					(m1, ScorableHandFourthMeld::Tanki(m4)) => {
						let mut ms = [m2, m3, m4];
						ms.sort_unstable();
						(ms, m1)
					},

					_ => unreachable!("at most one meld can be non-tanki"),
				};
				result.insert(ms);
			}
		}
	}

	// ... or the second tile is in m2.
	{
		let (_, t4) = ts[1];
		for [&(i2, t2), &(i3, t3)] in const_combinations::SliceExt::combinations(&ts[2..]) {
			let Some(m1) = to_meld([t1, t2, t3]) else { continue; };
			let ts = ts[2..].iter().filter(move |&&(i, _)| i != i2 && i != i3).copied().next_chunk::<8>();
			let ts = unsafe { ts.unwrap_unchecked() };
			for [&(i5, t5), &(i6, t6)] in const_combinations::SliceExt::combinations(&ts[..]) {
				let Some(m2) = to_meld([t4, t5, t6]) else { continue; };
				let ts = ts.iter().filter(move |&&(i, _)| i != i5 && i != i6).copied().next_chunk();
				let [(_, t7), (_, t8), (_, t9), (_, t10), (_, t11), (_, t12)] = unsafe { ts.unwrap_unchecked() };
				for (m3, m4) in to_melds_2([t7, t8, t9, t10, t11, t12]) {
					let ms = match (m1, m2, m4) {
						(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m4)) => {
							let mut ms = [m1, m2, m3, m4];
							ms.sort_unstable();
							let [m1, m2, m3, m4] = ms;
							([m1, m2, m3], ScorableHandFourthMeld::Tanki(m4))
						},

						(ScorableHandFourthMeld::Tanki(m1), ScorableHandFourthMeld::Tanki(m2), m4) => {
							let mut ms = [m1, m2, m3];
							ms.sort_unstable();
							let [m1, m2, m3] = ms;
							([m1, m2, m3], m4)
						},

						(ScorableHandFourthMeld::Tanki(m1), m2, ScorableHandFourthMeld::Tanki(m4)) => {
							let mut ms = [m1, m3, m4];
							ms.sort_unstable();
							let [m1, m3, m4] = ms;
							([m1, m3, m4], m2)
						},

						(m1, ScorableHandFourthMeld::Tanki(m2), ScorableHandFourthMeld::Tanki(m4)) => {
							let mut ms = [m2, m3, m4];
							ms.sort_unstable();
							let [m2, m3, m4] = ms;
							([m2, m3, m4], m1)
						},

						_ => unreachable!("at most one meld can be non-tanki"),
					};
					result.insert(ms);
				}
			}
		}
	}

	result
}

fn indexify<T, const N: usize>(ts: [T; N]) -> [(usize, T); N] {
	let mut i = 0_usize;
	ts.map(|t| {
		let result = (i, t);
		i += 1;
		result
	})
}

fn to_chiitoi(
	[(t1, _), (t2, _), (t3, _), (t4, _), (t5, _), (t6, _), (t7, _), (t8, _), (t9, _), (t10, _), (t11, _), (t12, _), (t13, _), (t14, _)]: [(Tile, TileProps); 14],
) -> Option<ScorableHand> {
	let is_chiitoi =
		t1 == t2 &&
		t2 != t3 &&
		t3 == t4 &&
		t4 != t5 &&
		t5 == t6 &&
		t6 != t7 &&
		t7 == t8 &&
		t8 != t9 &&
		t9 == t10 &&
		t10 != t11 &&
		t11 == t12 &&
		t12 != t13 &&
		t13 == t14;
	is_chiitoi.then_some(ScorableHand::Chiitoi([
		ScorableHandPair([t1, t2]),
		ScorableHandPair([t3, t4]),
		ScorableHandPair([t5, t6]),
		ScorableHandPair([t7, t8]),
		ScorableHandPair([t9, t10]),
		ScorableHandPair([t11, t12]),
		ScorableHandPair([t13, t14]),
	]))
}

fn to_kokushi_musou(ts: [(Tile, TileProps); 14], new_tile: Tile) -> Option<ScorableHand> {
	let ts = ts.map(|(t, _)| t);
	let tiles: MultiSet<_> = ts.into_iter().collect();
	let is_kokushi_musou =
		tiles.len() == 13 &&
		tiles.get(&t!(1m)) >= 1 &&
		tiles.get(&t!(9m)) >= 1 &&
		tiles.get(&t!(1p)) >= 1 &&
		tiles.get(&t!(9p)) >= 1 &&
		tiles.get(&t!(1s)) >= 1 &&
		tiles.get(&t!(9s)) >= 1 &&
		tiles.get(&t!(E)) >= 1 &&
		tiles.get(&t!(S)) >= 1 &&
		tiles.get(&t!(W)) >= 1 &&
		tiles.get(&t!(N)) >= 1 &&
		tiles.get(&t!(Wh)) >= 1 &&
		tiles.get(&t!(G)) >= 1 &&
		tiles.get(&t!(R)) >= 1;
	is_kokushi_musou.then(|| {
		let was_juusanmen_wait = tiles.get(&new_tile) == 2;
		ScorableHand::KokushiMusou { tiles: ts, was_juusanmen_wait }
	})
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn to_meld() {
		// 111 -> 111
		assert_eq!(
			super::to_meld([(t!(1s), TileProps::NotNewTile), (t!(1s), TileProps::NotNewTile), (t!(1s), TileProps::NotNewTile)]),
			Some(make_scorable_hand!(@meldr4 { ankou 1s 1s 1s })),
		);

		// 123 -> 123
		assert_eq!(
			super::to_meld([(t!(1s), TileProps::NotNewTile), (t!(2s), TileProps::NotNewTile), (t!(3s), TileProps::NotNewTile)]),
			Some(make_scorable_hand!(@meldr4 { anjun 1s 2s 3s })),
		);

		// 124 -> X
		assert_eq!(
			super::to_meld([(t!(1s), TileProps::NotNewTile), (t!(2s), TileProps::NotNewTile), (t!(4s), TileProps::NotNewTile)]),
			None,
		);
	}

	#[test]
	fn to_melds_2() {
		let melds_from_6 = [
			make_scorable_hand!(@meld { ankou 1s 1s 1s }),
			make_scorable_hand!(@meld { ankou 2s 2s 2s }),
			make_scorable_hand!(@meld { ankou 3s 3s 3s }),
			make_scorable_hand!(@meld { ankou 4s 4s 4s }),
			make_scorable_hand!(@meld { anjun 1s 2s 3s }),
			make_scorable_hand!(@meld { anjun 2s 3s 4s }),
			make_scorable_hand!(@meld { anjun 3s 4s 5s }),
			make_scorable_hand!(@meld { anjun 4s 5s 6s }),
		];
		for m1 in melds_from_6 {
			let [t1, t2, t3] = match m1 {
				ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
				ScorableHandMeld::Ankou(ts) => ts,
				_ => unreachable!(),
			};
			for m2 in melds_from_6 {
				let [t4, t5, t6] = match m2 {
					ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
					ScorableHandMeld::Ankou(ts) => ts,
					_ => unreachable!(),
				};

				let mut used: MultiSet<_> = Default::default();
				used.insert(t1);
				used.insert(t2);
				used.insert(t3);
				used.insert(t4);
				used.insert(t5);
				used.insert(t6);
				if used.counts().any(|n| n.get() > 4) {
					continue;
				}

				let mut expected = [m1, m2];
				expected.sort_unstable();
				let expected = (expected[0], ScorableHandFourthMeld::Tanki(expected[1]));

				let mut ts = [t1, t2, t3, t4, t5, t6];
				ts.sort_unstable();
				let actual = super::to_melds_2(ts.map(|t| (t, TileProps::NotNewTile)));
				assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
			}
		}
	}

	#[test]
	fn to_melds_3() {
		let melds_from_9 = [
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
		];
		for m1 in melds_from_9 {
			let [t1, t2, t3] = match m1 {
				ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
				ScorableHandMeld::Ankou(ts) => ts,
				_ => unreachable!(),
			};
			let mut used: MultiSet<_> = Default::default();
			used.insert(t1);
			used.insert(t2);
			used.insert(t3);

			for m2 in melds_from_9 {
				let [t4, t5, t6] = match m2 {
					ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
					ScorableHandMeld::Ankou(ts) => ts,
					_ => unreachable!(),
				};
				let mut used = used.clone();
				used.insert(t4);
				used.insert(t5);
				used.insert(t6);
				if used.counts().any(|n| n.get() > 4) {
					continue;
				}

				for m3 in melds_from_9 {
					let [t7, t8, t9] = match m3 {
						ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
						ScorableHandMeld::Ankou(ts) => ts,
						_ => unreachable!(),
					};

					let mut used = used.clone();
					used.insert(t7);
					used.insert(t8);
					used.insert(t9);
					if used.counts().any(|n| n.get() > 4) {
						continue;
					}

					let mut expected = [m1, m2, m3];
					expected.sort_unstable();
					let expected = ([expected[0], expected[1]], ScorableHandFourthMeld::Tanki(expected[2]));

					let mut ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9];
					ts.sort_unstable();
					let actual = super::to_melds_3(ts.map(|t| (t, TileProps::NotNewTile)));
					assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
				}
			}
		}
	}

	#[test]
	fn to_melds_4() {
		let melds_from_12 = [
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
		];
		for m1 in melds_from_12 {
			let [t1, t2, t3] = match m1 {
				ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
				ScorableHandMeld::Ankou(ts) => ts,
				_ => unreachable!(),
			};
			let mut used: MultiSet<_> = Default::default();
			used.insert(t1);
			used.insert(t2);
			used.insert(t3);

			for m2 in melds_from_12 {
				let [t4, t5, t6] = match m2 {
					ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
					ScorableHandMeld::Ankou(ts) => ts,
					_ => unreachable!(),
				};
				let mut used = used.clone();
				used.insert(t4);
				used.insert(t5);
				used.insert(t6);
				if used.counts().any(|n| n.get() > 4) {
					continue;
				}

				for m3 in melds_from_12 {
					let [t7, t8, t9] = match m3 {
						ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
						ScorableHandMeld::Ankou(ts) => ts,
						_ => unreachable!(),
					};
					let mut used = used.clone();
					used.insert(t7);
					used.insert(t8);
					used.insert(t9);
					if used.counts().any(|n| n.get() > 4) {
						continue;
					}

					for m4 in melds_from_12 {
						let [t10, t11, t12] = match m4 {
							ScorableHandMeld::Anjun(ts) => ts.map(Tile::Number),
							ScorableHandMeld::Ankou(ts) => ts,
							_ => unreachable!(),
						};
						let mut used = used.clone();
						used.insert(t10);
						used.insert(t11);
						used.insert(t12);
						if used.counts().any(|n| n.get() > 4) {
							continue;
						}

						let mut expected = [m1, m2, m3, m4];
						expected.sort_unstable();
						let expected = ([expected[0], expected[1], expected[2]], ScorableHandFourthMeld::Tanki(expected[3]));

						let mut ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12];
						ts.sort_unstable();
						let actual = super::to_melds_4(ts.map(|t| (t, TileProps::NotNewTile)));
						assert!(actual.contains(&expected), "{ts:?} did not meld into {expected:?}, only into {actual:?}");
					}
				}
			}
		}
	}

	#[test]
	fn find_minjuns() {
		let h = make_hand!(1m 2m 3m 5m 0m 6m 7m 8m E E E G G);
		let hs: Vec<_> = h.find_minjuns(tn!(4m)).collect();
		assert!(matches!(hs[..], [
			Hand([t!(1m), t!(5m), t!(0m), t!(6m), t!(7m), t!(8m), t!(E), t!(E), t!(E), t!(G), t!(G)], [make_hand!(@meld { minjun 2m 3m 4m })]),
			Hand([t!(1m), t!(2m), t!(0m), t!(6m), t!(7m), t!(8m), t!(E), t!(E), t!(E), t!(G), t!(G)], [make_hand!(@meld { minjun 3m 4m 5m })]),
			Hand([t!(1m), t!(2m), t!(5m), t!(6m), t!(7m), t!(8m), t!(E), t!(E), t!(E), t!(G), t!(G)], [make_hand!(@meld { minjun 3m 4m 0m })]),
			Hand([t!(1m), t!(2m), t!(3m), t!(0m), t!(7m), t!(8m), t!(E), t!(E), t!(E), t!(G), t!(G)], [make_hand!(@meld { minjun 4m 5m 6m })]),
			Hand([t!(1m), t!(2m), t!(3m), t!(5m), t!(7m), t!(8m), t!(E), t!(E), t!(E), t!(G), t!(G)], [make_hand!(@meld { minjun 4m 0m 6m })]),
		]));
	}

	#[test]
	fn find_minkous() {
		let h = make_hand!(1m 1m 1m 2m 2m 3m 3m 3m 4m 4m 4m 5m 5m);
		let hs: Vec<_> = h.find_minkous(t!(2m)).collect();
		assert!(matches!(hs[..], [
			Hand([t!(1m), t!(1m), t!(1m), t!(3m), t!(3m), t!(3m), t!(4m), t!(4m), t!(4m), t!(5m), t!(5m)], [make_hand!(@meld { minkou 2m 2m 2m })]),
		]));
	}

	#[test]
	fn find_shouminkan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkou E E E });
		let h = h.find_shouminkan(t!(E)).unwrap();
		assert!(matches!(h, Hand([t!(1m), t!(2m), t!(3m), t!(4m), t!(5m), t!(6m), t!(7m), t!(8m), t!(9m), t!(G)], [make_hand!(@meld { minkan E E E E })])));
	}

	#[test]
	fn find_kan() {
		let h = make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m E E E G);
		{
			let h = h.find_daiminkan(t!(E)).unwrap();
			assert!(matches!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { minkan E E E E })));
		}
		{
			let h = h.find_ankan(t!(E)).unwrap();
			assert!(matches!(h, make_hand!(1m 2m 3m 4m 5m 6m 7m 8m 9m G { ankan E E E E })));
		}
	}
}
