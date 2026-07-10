use crate::{
	GameType,
	ScorableHand, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair,
	Tile, Tile34MultiSet, TsumoOrRon,
	WindTile,
	scorable_hand::Dairin,
};

#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
pub enum Riichi {
	NotRiichi,
	Riichi { ippatsu: bool, double: bool },
}

/// Seat relative to this player's seat.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
pub enum SeatRelative {
	/// Player to the right.
	Shimocha,
	/// Player opposite.
	Toimen,
	/// Player to the left.
	Kamicha,
}

/// Indicates where the winning tile was drawn from.
#[derive(Copy, Debug)]
#[derive_const(Clone, Eq, PartialEq)]
pub enum WinningTileFrom {
	/// The tile was drawn from the wall and was the last tile of the wall.
	Haitei,
	/// The tile was drawn from the dead wall because the player called a kan or played a nukidora.
	Rinshan,
	/// The tile was the first tile drawn on the player's turn, when the player is a dealer.
	Tenhou,
	/// The tile was the first tile drawn on the player's turn from the wall, when the player is not a dealer,
	/// and no previous player had called a tile until this player's turn.
	Chiihou,
	/// The tile was drawn from the wall and wasn't any of the above possibilities.
	Tsumo,

	/// The tile was taken from another player's discard which was the last discard of the round.
	Houtei(SeatRelative),
	/// The tile was taken from another player's ankan.
	ChankanAnkan(SeatRelative),
	/// The tile was taken from another player's shouminkan.
	ChankanShouminkan(SeatRelative),
	/// The tile was taken from another player's discard when that player called riichi.
	TsubameGaeshi(SeatRelative),
	/// The tile was taken from another player's discard when that player called kan.
	Kanburi(SeatRelative),
	/// The tile was taken from another player's discard, before the player has taken their first turn.
	Renhou(SeatRelative),
	/// The tile was taken from another player's discard and wasn't any of the above possibilities.
	Ron(SeatRelative),
}

/// Broken down score for a [`ScorableHand`].
///
/// `Default` impl sets all fields to 0.
#[derive(Copy)]
#[derive_const(Clone, Default, Eq, PartialEq)]
#[repr(C)]
pub struct Score {
	/// 20 for regular, 25 for chiitoi, 0 for kokushi musou.
	pub base: Fu,

	/// 10 for menzen ron, 2 for tsumo except if pinfu.
	pub win_condition: Fu,

	/// 2/4/8/16/32 fu for triplets and kans.
	pub meld1: Fu,

	/// 2/4/8/16/32 fu for triplets and kans.
	pub meld2: Fu,

	/// 2/4/8/16/32 fu for triplets and kans.
	pub meld3: Fu,

	/// 2/4/8/16/32 fu for triplets and kans.
	pub meld4: Fu,

	/// 2 fu for yakuhai pair.
	pub pair: Fu,

	/// 2 fu for kanchan / penchan / tanki.
	pub wait: Fu,

	/// 2 fu for a non-menzen hand with no fu other than 20 base fu.
	pub open_pinfu: Fu,

	pub rounding: Fu,

	pub mentsumo: Han,

	/// 1 han for riichi, 2 han for double riichi.
	pub riichi: Han,

	pub ippatsu: Han,

	pub pinfu: Han,

	pub iipeikou: Han,

	pub haitei: Han,

	pub houtei: Han,

	pub rinshan: Han,

	pub chankan: Han,

	pub tanyao: Han,

	pub yakuhai_ton: Han,
	pub yakuhai_nan: Han,
	pub yakuhai_shaa: Han,
	pub yakuhai_pei: Han,
	pub yakuhai_haku: Han,
	pub yakuhai_hatsu: Han,
	pub yakuhai_chun: Han,

	pub tsubame_gaeshi: Han,

	pub kanburi: Han,

	pub shiiaru_raotai: Han,

	pub chanta: Han,

	pub sanshoku_doujun: Han,

	pub ittsuu: Han,

	pub toitoi: Han,

	pub sanankou: Han,

	pub sanshoku_doukou: Han,

	pub sankantsu: Han,

	pub chiitoi: Han,

	pub honroutou: Han,

	pub shousangen: Han,

	pub uumensai: Han,

	pub sanrenkou: Han,

	pub honitsu: Han,

	pub junchan: Han,

	pub ryanpeikou: Han,

	pub isshoku_sanjun: Han,

	pub iipin_mouyue: Han,
	pub chuupin_raoyui: Han,

	pub chinitsu: Han,

	pub dora: Han,

	pub nukidora: Han,

	pub kazoe_yakuman: Yakuman,

	pub kokushi_musou: Yakuman,

	pub suuankou: Yakuman,

	pub daisangen: Yakuman,

	pub shousuushii: Yakuman,

	pub daisuushii: Yakuman,

	pub tsuuiisou: Yakuman,

	pub chinroutou: Yakuman,

	pub ryuuiisou: Yakuman,

	pub chuuren_poutou: Yakuman,

	pub suukantsu: Yakuman,

	pub tenhou: Yakuman,

	pub chiihou: Yakuman,

	pub renhou: Yakuman,

	pub daisharin: Yakuman,
	pub daichikurin: Yakuman,
	pub daisuurin: Yakuman,

	pub ishi_no_ue_ni_mo_sannen: Yakuman,

	pub daichisei: Yakuman,
}

#[derive(Copy, Debug)]
#[derive_const(Clone, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Fu(pub u8);

#[derive(Copy, Debug)]
#[derive_const(Clone, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Han(pub u8);

#[derive(Copy, Debug)]
#[derive_const(Clone, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Yakuman(pub u8);

#[derive(Copy, Debug)]
#[derive_const(Clone, Default, Eq, PartialEq)]
pub struct ScoreAggregate {
	pub fu: Fu,
	pub han: Han,
	pub yakuman: Yakuman,
}

/// The points to be taken from all players identified by their positions relative to the current player.
#[derive(Copy, Debug)]
#[derive_const(Clone, Default, Eq, PartialEq)]
#[repr(C)]
pub struct Points {
	/// Points from riichi sticks in play.
	pub riichi_bou: u32,
	/// Points to take from the right player.
	pub shimocha: u32,
	/// Points to take from the opposite player.
	pub toimen: u32,
	/// Points to take from the left player.
	pub kamicha: u32,
}

/// The points to be added or subtracted from all players identified by their seat winds.
#[derive(Copy, Debug)]
#[derive_const(Clone, Default, Eq, PartialEq)]
#[repr(C)]
pub struct PointsAbsolute {
	/// Points delta for the East seat player.
	pub ton: i32,
	/// Points delta for the South seat player.
	pub nan: i32,
	/// Points delta for the West seat player.
	pub shaa: i32,
	/// Points delta for the North seat player.
	pub pei: i32,
}

assert_size_of!(Score, 10 + 41 + 19);

impl WinningTileFrom {
	const fn ron_seat(self) -> Option<SeatRelative> {
		match self {
			Self::Haitei |
			Self::Rinshan |
			Self::Tenhou |
			Self::Chiihou |
			Self::Tsumo => None,

			Self::Houtei(seat) |
			Self::ChankanAnkan(seat) |
			Self::ChankanShouminkan(seat) |
			Self::TsubameGaeshi(seat) |
			Self::Kanburi(seat) |
			Self::Renhou(seat) |
			Self::Ron(seat) => Some(seat),
		}
	}
}

impl ScorableHand {
	/// Returns `None` if the hand has no yaku.
	#[expect(clippy::bool_to_int_with_if)]
	pub fn score(
		&self,
		local_yaku: bool,
		doras: &Tile34MultiSet,
		round_wind: WindTile,
		seat_wind: WindTile,
		nukidora: u8,
		riichi: Riichi,
		winning_tile: Tile,
		winning_tile_from: WinningTileFrom,
	) -> Option<Score> {
		let mut score = Score::default();

		let tsumo_or_ron = TsumoOrRon::from(winning_tile_from);

		match self {
			Self::Regular(h) => {
				let is_menzen = h.is_menzen();
				let is_pinfu = h.is_pinfu(round_wind, seat_wind);
				let (num_peikou, is_isshoku_sanjun) = h.num_peikou_isshoku_sanjun();
				let chanta_routou = h.chanta_routou();
				let num_ankou = h.num_ankou();
				let num_kantsu = h.num_kantsu();
				let suushii_sangen = h.suushii_sangen();
				let honchinitsu = h.honchinitsu();

				score.base = Fu(20);

				score.win_condition = Fu(match tsumo_or_ron {
					// TODO: > In a few scoring variations, a win by rinshan kaihou is also ineligible for the +2 fu from tsumo.
					TsumoOrRon::Tsumo if !is_pinfu => 2,
					TsumoOrRon::Ron if is_menzen => 10,
					_ => 0,
				});

				score.meld1 = h.m1.fu();
				score.meld2 = h.m2.fu();
				score.meld3 = h.m3.fu();
				(score.meld4, score.wait) = h.m4.fu();
				score.pair = h.pair.inner.fu(round_wind, seat_wind);

				score.open_pinfu = Fu(if !is_menzen && score.fu().0 == 20 { 2 } else { 0 });

				let fu = score.fu().0;
				score.rounding = Fu(fu.next_multiple_of(10) - fu);

				score.mentsumo = Han(if is_menzen && matches!(tsumo_or_ron, TsumoOrRon::Tsumo) { 1 } else { 0 });

				if let Riichi::Riichi { double, ippatsu } = riichi {
					score.riichi = Han(if double { 2 } else { 1 });
					score.ippatsu = Han(if ippatsu { 1 } else { 0 });
				}

				score.pinfu = Han(if is_pinfu { 1 } else { 0 });
				score.iipeikou = Han(if num_peikou == 1 { 1 } else { 0 });
				(score.haitei, score.iipin_mouyue) =
					if matches!(winning_tile_from, WinningTileFrom::Haitei) {
						if local_yaku && winning_tile == t!(1p) {
							(Han(0), Han(5))
						}
						else {
							(Han(1), Han(0))
						}
					}
					else {
						(Han(0), Han(0))
					};
				(score.houtei, score.chuupin_raoyui) =
					if matches!(winning_tile_from, WinningTileFrom::Houtei(_)) {
						if local_yaku && winning_tile == t!(9p) {
							(Han(0), Han(5))
						}
						else {
							(Han(1), Han(0))
						}
					}
					else {
						(Han(0), Han(0))
					};
				score.rinshan = Han(if matches!(winning_tile_from, WinningTileFrom::Rinshan) { 1 } else { 0 });
				score.chankan = Han(match winning_tile_from {
					// Only kokushi musou is allowed to chankan an ankan
					WinningTileFrom::ChankanAnkan(_) => return None,
					WinningTileFrom::ChankanShouminkan(_) => 1,
					_ => 0,
				});
				score.tanyao = Han(if chanta_routou.is_tanyao() { 1 } else { 0 });
				score.yakuhai_ton = Han(h.num_wind_yakuhai(tw!(E), round_wind, seat_wind));
				score.yakuhai_nan = Han(h.num_wind_yakuhai(tw!(S), round_wind, seat_wind));
				score.yakuhai_shaa = Han(h.num_wind_yakuhai(tw!(W), round_wind, seat_wind));
				score.yakuhai_pei = Han(h.num_wind_yakuhai(tw!(N), round_wind, seat_wind));
				score.yakuhai_haku = Han(if h.is_dragon_yakuhai(td!(Wh)) { 1 } else { 0 });
				score.yakuhai_hatsu = Han(if h.is_dragon_yakuhai(td!(G)) { 1 } else { 0 });
				score.yakuhai_chun = Han(if h.is_dragon_yakuhai(td!(R)) { 1 } else { 0 });

				score.tsubame_gaeshi = Han(if local_yaku && matches!(winning_tile_from, WinningTileFrom::TsubameGaeshi(_)) { 1 } else { 0 });
				score.kanburi = Han(if local_yaku && matches!(winning_tile_from, WinningTileFrom::Kanburi(_)) { 1 } else { 0 });
				score.shiiaru_raotai = Han(if local_yaku && h.is_shiiaru_raotai() { 1 } else { 0 });

				score.chanta = Han(if chanta_routou.is_chanta() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.sanshoku_doujun = Han(if h.is_sanshoku_doujun() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.ittsuu = Han(if h.is_ittsuu() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.toitoi = Han(if h.is_toitoi() { 2 } else { 0 });
				score.sanankou = Han(if num_ankou.is_sanankou() { 2 } else { 0 });
				score.sanshoku_doukou = Han(if h.is_sanshoku_doukou() { 2 } else { 0 });
				score.sankantsu = Han(if num_kantsu.is_sankantsu() { 2 } else { 0 });
				score.honroutou = Han(if chanta_routou.is_honroutou() { 2 } else { 0 });
				score.shousangen = Han(if suushii_sangen.is_shousangen() { 2 } else { 0 });

				score.uumensai = Han(if local_yaku && h.is_uumensai() { 2 } else { 0 });
				score.sanrenkou = Han(if local_yaku && h.is_sanrenkou() { 2 } else { 0 });

				score.honitsu = Han(if honchinitsu.is_honitsu() { if is_menzen { 3 } else { 2 } } else { 0 });
				score.junchan = Han(if chanta_routou.is_junchan() { if is_menzen { 3 } else { 2 } } else { 0 });
				score.ryanpeikou = Han(if num_peikou == 2 { 3 } else { 0 });

				score.isshoku_sanjun = Han(if local_yaku && is_isshoku_sanjun { if is_menzen { 3 } else { 2 } } else { 0 });

				score.chinitsu = Han(if honchinitsu.is_chinitsu() { if is_menzen { 6 } else { 5 } } else { 0 });

				score.suuankou = Yakuman(num_ankou.num_suuankou());
				score.daisangen = Yakuman(if suushii_sangen.is_daisangen() { 1 } else { 0 });
				score.shousuushii = Yakuman(if suushii_sangen.is_shousuushii() { 1 } else { 0 });
				score.daisuushii = Yakuman(if suushii_sangen.is_daisuushii() { 2 } else { 0 });
				score.tsuuiisou = Yakuman(if chanta_routou.is_tsuuiisou() { 1 } else { 0 });
				score.chinroutou = Yakuman(if chanta_routou.is_chinroutou() { 1 } else { 0 });
				score.ryuuiisou = Yakuman(if h.is_ryuuiisou() { 1 } else { 0 });
				score.chuuren_poutou = Yakuman(h.num_chuuren_poutou());
				score.suukantsu = Yakuman(if num_kantsu.is_suukantsu() { 1 } else { 0 });
			},

			Self::Chiitoi(h) => {
				if matches!(winning_tile_from, WinningTileFrom::ChankanAnkan(_)) {
					// Only kokushi musou is allowed to chankan an ankan
					return None;
				}

				let chanta_routou = h.chanta_routou();
				let honchinitsu = h.honchinitsu();
				let dairin = if local_yaku { h.dairin() } else { Dairin::None };

				score.base = Fu(25);

				score.mentsumo = Han(if matches!(tsumo_or_ron, TsumoOrRon::Tsumo) { 1 } else { 0 });

				score.tanyao = Han(if chanta_routou.is_tanyao() { 1 } else { 0 });

				if let Riichi::Riichi { double, ippatsu } = riichi {
					score.riichi = Han(if double { 2 } else { 1 });
					score.ippatsu = Han(if ippatsu { 1 } else { 0 });
				}

				(score.haitei, score.iipin_mouyue) =
					if matches!(winning_tile_from, WinningTileFrom::Haitei) {
						if local_yaku && winning_tile == t!(1p) {
							(Han(0), Han(5))
						}
						else {
							(Han(1), Han(0))
						}
					}
					else {
						(Han(0), Han(0))
					};
				(score.haitei, score.chuupin_raoyui) =
					if matches!(winning_tile_from, WinningTileFrom::Haitei) {
						if local_yaku && winning_tile == t!(9p) {
							(Han(0), Han(5))
						}
						else {
							(Han(1), Han(0))
						}
					}
					else {
						(Han(0), Han(0))
					};

				score.chiitoi = Han(2);

				score.honroutou = Han(if chanta_routou.is_honroutou() { 2 } else { 0 });

				score.honitsu = Han(if honchinitsu.is_honitsu() { 3} else { 0 });

				score.chinitsu = Han(if honchinitsu.is_chinitsu() { 6 } else { 0 });

				score.tsuuiisou = Yakuman(if chanta_routou.is_tsuuiisou() { 1 } else { 0 });

				score.daisharin = Yakuman(if matches!(dairin, Dairin::Pin) { 1 } else { 0 });
				score.daichikurin = Yakuman(if matches!(dairin, Dairin::Sou) { 1 } else { 0 });
				score.daisuurin = Yakuman(if matches!(dairin, Dairin::Man) { 1 } else { 0 });

				score.daichisei = Yakuman(if matches!(dairin, Dairin::Ji) { 2 } else { 0 });
			},

			Self::KokushiMusou(ScorableHandKokushiMusou { was_juusanmen_wait, .. }) => {
				score.kokushi_musou = Yakuman(if *was_juusanmen_wait { 2 } else { 1 });
			},
		}

		score.tenhou = Yakuman(if matches!(winning_tile_from, WinningTileFrom::Tenhou) { 1 } else { 0 });
		score.chiihou = Yakuman(if matches!(winning_tile_from, WinningTileFrom::Chiihou) { 1 } else { 0 });

		score.ishi_no_ue_ni_mo_sannen = Yakuman(
			if local_yaku && matches!(riichi, Riichi::Riichi { double: true, .. }) && matches!(winning_tile_from, WinningTileFrom::Haitei | WinningTileFrom::Houtei(_)) { 1 }
			else { 0 }
		);

		// No han and no yakuman => no yaku => cannot score.
		// Note that even 13+ dora cannot create kazoe yakuman by themselves, so we only want to consider non-dora han here.
		let han = score.han().0;
		if han == 0 && score.yakuman().0 == 0 {
			return None;
		}

		let dora = {
			let mut result = 0_u8;
			self.for_each_tile(|tile| result += dora_match(doras, tile));
			result + dora_match(doras, t!(N)) * nukidora
		};
		score.dora = Han(dora);
		score.nukidora = Han(nukidora);

		// Kazoe yakuman does not stack with other yakuman.
		if score.yakuman().0 == 0 && han + dora + nukidora >= 13 {
			score.kazoe_yakuman = Yakuman(1);
		}

		Some(score)
	}
}

impl ScorableHandMeld {
	const fn fu(self) -> Fu {
		// Micro-optimization: If `Anjun | Minjun` arm does `return Fu(0)`, the whole match compiles to a jump table
		// with a different target for every variant. Being consistent about returning a `(base, t)` pair makes it better;
		// it extracts the base by shifting a constant by the discriminant and `t` is at the same offset for every arm.
		let (base, t) = match self {
			Self::Ankan(t) => (16, t),
			Self::Minkan(t) => (8, t),
			Self::Ankou(t) => (4, t),
			Self::Minkou(t) => (2, t),
			Self::Anjun(t) |
			Self::Minjun(t) => (0, t.remove_red().into()),
		};
		Fu(base << u8::from(!t.is_simple()))
	}
}

impl ScorableHandFourthMeld {
	const fn fu(self) -> (Fu, Fu) {
		let m4_fu = ScorableHandMeld::from(self).fu();

		// This match is the proper impl, but it generates a jump table. We can do better with some comparisons on the waits.
		//
		//     let wait_fu = match self {
		//         Self::Ankan(..) |
		//         Self::Minkan(..) |
		//         Self::Ankou(_, KouWait::Tanki) |
		//         Self::Minkou(_, KouWait::Tanki) |
		//         Self::Anjun(_, ShunWait::Tanki | ShunWait::Kanchan | ShunWait::Penchan) |
		//         Self::Minjun(_, ShunWait::Tanki | ShunWait::Kanchan | ShunWait::Penchan) => Fu(2),
		//         Self::Ankou(_, KouWait::Shanpon) |
		//         Self::Minkou(_, KouWait::Shanpon) |
		//         Self::Anjun(_, ShunWait::RyanmenLow | ShunWait::RyanmenHigh) |
		//         Self::Minjun(_, ShunWait::RyanmenLow | ShunWait::RyanmenHigh) => Fu(0),
		//     };
		//
		// By reading the discriminant and wait as u8, we can compute tanki as `w == 0`
		// and kanchan / penchan as `d >= 4 && 1 <= w <= 2`.
		// We can also avoid the comparisons by using a bitmask shifted by `d` and `w`.
		#[expect(clippy::unusual_byte_groupings)]
		let wait_fu = (0b00_00_00_00_11_00_11_00_111111_0_u32 >> self.dw()) & 0b10;
		let wait_fu = Fu(wait_fu as u8);

		(m4_fu, wait_fu)
	}
}

impl ScorableHandPair {
	const fn fu(self, round_wind: WindTile, seat_wind: WindTile) -> Fu {
		Fu(self.num_yakuhai(round_wind, seat_wind) * 2)
	}
}

const impl From<WinningTileFrom> for TsumoOrRon {
	fn from(wtf: WinningTileFrom) -> Self {
		match wtf {
			WinningTileFrom::Haitei |
			WinningTileFrom::Rinshan |
			WinningTileFrom::Tenhou |
			WinningTileFrom::Chiihou |
			WinningTileFrom::Tsumo => Self::Tsumo,

			WinningTileFrom::Houtei(_) |
			WinningTileFrom::ChankanAnkan(_) |
			WinningTileFrom::ChankanShouminkan(_) |
			WinningTileFrom::TsubameGaeshi(_) |
			WinningTileFrom::Kanburi(_) |
			WinningTileFrom::Renhou(_) |
			WinningTileFrom::Ron(_) => Self::Ron,
		}
	}
}

impl core::fmt::Debug for Score {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		macro_rules! fmt_inner {
			($f:ident, $($field:ident ,)*) => {
				$(
					if self.$field.0 > 0 { $f.field(stringify!($field), &self.$field); }
				)*
			};
		}

		let mut f = f.debug_struct("Score");
		fmt_inner!(
			f,
			base, win_condition,
			meld1, meld2, meld3, meld4, pair,
			wait, open_pinfu,
			rounding,
			mentsumo, riichi, ippatsu, pinfu, iipeikou,
			haitei, houtei, rinshan, chankan, tanyao,
			yakuhai_ton, yakuhai_nan, yakuhai_shaa, yakuhai_pei, yakuhai_haku, yakuhai_hatsu, yakuhai_chun,
			tsubame_gaeshi, kanburi, shiiaru_raotai,
			chanta, sanshoku_doujun, ittsuu,
			toitoi, sanankou, sanshoku_doukou, sankantsu, chiitoi, honroutou, shousangen,
			uumensai, sanrenkou,
			honitsu, junchan, ryanpeikou,
			isshoku_sanjun,
			iipin_mouyue, chuupin_raoyui,
			chinitsu,
			dora, nukidora,
			kazoe_yakuman, kokushi_musou, suuankou, daisangen, shousuushii, daisuushii, tsuuiisou, chinroutou, ryuuiisou, chuuren_poutou, suukantsu, tenhou, chiihou,
			renhou, daisharin, daichikurin, daisuurin, ishi_no_ue_ni_mo_sannen, daichisei,
		);
		f.finish()
	}
}

impl core::fmt::Display for Score {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		macro_rules! fmt_inner {
			($f:ident, $($field:ident ,)*) => {
				$(
					if self.$field.0 > 0 { write!($f, concat!(", ", stringify!($field), ": {}"), self.$field)?; }
				)*
			};
		}

		write!(f, "base: {}", self.base)?;
		fmt_inner!(
			f,
			win_condition,
			meld1, meld2, meld3, meld4, pair,
			wait, open_pinfu,
			// rounding intentionally ignored
			mentsumo, riichi, ippatsu, pinfu, iipeikou,
			haitei, houtei, rinshan, chankan, tanyao,
			yakuhai_ton, yakuhai_nan, yakuhai_shaa, yakuhai_pei, yakuhai_haku, yakuhai_hatsu, yakuhai_chun,
			chanta, sanshoku_doujun, ittsuu,
			toitoi, sanankou, sanshoku_doukou, sankantsu, chiitoi, honroutou, shousangen,
			honitsu, junchan, ryanpeikou,
			chinitsu,
			dora, nukidora,
			kazoe_yakuman, kokushi_musou, suuankou, daisangen, shousuushii, daisuushii, tsuuiisou, chinroutou, ryuuiisou, chuuren_poutou, suukantsu, tenhou, chiihou,
		);
		Ok(())
	}
}

impl Score {
	/// - `riichi_bou`: Number of riichi sticks in play (1000 points each). Note that it is the caller's responsibility to consider atamahane in case of multiple rons.
	/// - `honba`: Number of round repeat sticks in play (300 points each in yonma, 200 points each in sanma).
	/// - `daisangen_sekinin_barai`: Set to `Some(seat)` if `seat` had dealt into this player's fully open daisangen,
	/// - `daisuushii_sekinin_barai`: Set to `Some(seat)` if `seat` had dealt into this player's fully open daisuushii,
	///
	/// # Panics
	///
	/// Panics if the given `Score` is not valid. Specifically an invalid score is one which has 0 han and 0 yakuman or 13+ han and 0 yakuman.
	pub fn score(
		self,
		game_type: GameType,
		riichi_bou: u8,
		honba: u8,
		seat_wind: WindTile,
		winning_tile_from: WinningTileFrom,
		daisangen_sekinin_barai: Option<SeatRelative>,
		daisuushii_sekinin_barai: Option<SeatRelative>,
	) -> Points {
		fn score_inner(points: &mut Points, seat_wind: WindTile, winning_tile_from: WinningTileFrom, basic_points: u32) {
			if let Some(seat) = winning_tile_from.ron_seat() {
				// If dealer, 6x from ron'd player.
				// If non-dealer, 4x from ron'd player.
				let ron = (basic_points * if matches!(seat_wind, tw!(E)) { 6 } else { 4 }).next_multiple_of(100);
				points[seat] += ron;
			}
			else {
				// If dealer, 2x from each non-dealer.
				// If non-dealer, 2x from dealer, 1x from each other non-dealer.
				let single = basic_points.next_multiple_of(100);
				let double = (basic_points * 2).next_multiple_of(100);
				points.shimocha += if matches!(seat_wind, tw!(E | N)) { double } else { single };
				points.toimen += if matches!(seat_wind, tw!(E | W)) { double } else { single };
				points.kamicha += if matches!(seat_wind, tw!(E | S)) { double } else { single };
			}
		}

		fn sekinin_barai_inner(points: &mut Points, seat_wind: WindTile, winning_tile_from: WinningTileFrom, sekinin_barai: SeatRelative, yakuman: u8) {
			let basic_points = u32::from(yakuman) * 8000;
			if let Some(seat) = winning_tile_from.ron_seat() {
				// (Treated as ron, then split equally between ron'd player and sekinin barai player.)
				// If dealer, 3x from ron'd player and 3x from sekinin barai player.
				// If non-dealer, 2x from ron'd player and 2x from sekinin barai player.
				let ron = (basic_points * if matches!(seat_wind, tw!(E)) { 3 } else { 2 }).next_multiple_of(100);
				points.shimocha += if matches!(seat, SeatRelative::Shimocha) { ron } else { 0 } + if matches!(sekinin_barai, SeatRelative::Shimocha) { ron } else { 0 };
				points.toimen += if matches!(seat, SeatRelative::Toimen) { ron } else { 0 } + if matches!(sekinin_barai, SeatRelative::Toimen) { ron } else { 0 };
				points.kamicha += if matches!(seat, SeatRelative::Kamicha) { ron } else { 0 } + if matches!(sekinin_barai, SeatRelative::Kamicha) { ron } else { 0 };
			}
			else {
				// (Treated as ron from the sekinin barai player.)
				// If dealer, 6x from sekinin barai player.
				// If non-dealer, 4x from sekinin barai player.
				let ron = (basic_points * if matches!(seat_wind, tw!(E)) { 6 } else { 4 }).next_multiple_of(100);
				points[sekinin_barai] += ron;
			}
		}

		let mut points = Points { riichi_bou: u32::from(riichi_bou) * 1000, ..Default::default() };

		if self.yakuman().0 == 0 {
			let basic_points = match self.han().0 {
				0 => 0,
				han @ 1..=5 => ((u32::from(self.fu().0) << 2) << han).min(2000),
				// haneman
				6..=7 => 3000,
				// baiman
				8..=10 => 4000,
				// sanbaiman
				11.. => 6000,
			};
			score_inner(&mut points, seat_wind, winning_tile_from, basic_points);

			if let Some(seat) = winning_tile_from.ron_seat() {
				// Honba penalty paid by ron'd player.
				let honba_points = u32::from(honba) * match game_type { GameType::Yonma => 300, GameType::Sanma => 200 };
				points[seat] += honba_points;
			}
			else {
				// Honba penalty shared equally by all other players.
				let honba_points = u32::from(honba) * 100;
				points.shimocha += honba_points;
				points.toimen += honba_points;
				points.kamicha += honba_points;
			}
		}
		else {
			// Composite yakuman are handled individually.
			let Self {
				kazoe_yakuman,
				kokushi_musou,
				suuankou,
				daisangen,
				shousuushii,
				daisuushii,
				tsuuiisou,
				chinroutou,
				ryuuiisou,
				chuuren_poutou,
				suukantsu,
				tenhou,
				chiihou,
				..
			} = self;

			// Daisangen and daisuushii handled separately to account for sekinin barai.
			for yakuman in [kazoe_yakuman, kokushi_musou, suuankou, shousuushii, tsuuiisou, chinroutou, ryuuiisou, chuuren_poutou, suukantsu, tenhou, chiihou] {
				score_inner(&mut points, seat_wind, winning_tile_from, u32::from(yakuman.0) * 8000);
			}
			if let Some(sekinin_barai) = daisangen_sekinin_barai {
				sekinin_barai_inner(&mut points, seat_wind, winning_tile_from, sekinin_barai, daisangen.0);
			}
			else {
				score_inner(&mut points, seat_wind, winning_tile_from, u32::from(daisangen.0) * 8000);
			}
			if let Some(sekinin_barai) = daisuushii_sekinin_barai {
				sekinin_barai_inner(&mut points, seat_wind, winning_tile_from, sekinin_barai, daisuushii.0);
			}
			else {
				score_inner(&mut points, seat_wind, winning_tile_from, u32::from(daisuushii.0) * 8000);
			}

			// Sekinin barai player pays full honba penalty regardless of tsumo or ron.
			let honba_seat = daisangen_sekinin_barai.or(daisuushii_sekinin_barai).or_else(|| winning_tile_from.ron_seat());
			if let Some(seat) = honba_seat {
				// Honba penalty paid by this player.
				let honba_points = u32::from(honba) * match game_type { GameType::Yonma => 300, GameType::Sanma => 200 };
				points[seat] += honba_points;
			}
			else {
				// Honba penalty shared equally by all other players.
				let honba_points = u32::from(honba) * 100;
				points.shimocha += honba_points;
				points.toimen += honba_points;
				points.kamicha += honba_points;
			}
		}

		if matches!(game_type, GameType::Sanma) {
			let points = (tw!(W) as u8).checked_sub(seat_wind as u8).map(|diff| unsafe { &mut *(&raw mut points.shimocha).add((diff >> 1).into()) });
			if let Some(points) = points {
				*points = 0;
			}
		}

		points
	}

	fn fu(&self) -> Fu {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10]>(self) };
		let fu = core::simd::Simd::from_array(*this);
		let fu = core::simd::num::SimdUint::reduce_sum(fu);
		Fu(fu)
	}

	fn han(&self) -> Han {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10 + 41]>(self) };
		let han = core::simd::Simd::<_, 41>::from_slice(&this[10..]);
		let han = core::simd::num::SimdUint::reduce_sum(han);
		Han(han)
	}

	fn yakuman(&self) -> Yakuman {
		let this = unsafe { &*<*const Self>::cast::<[u8; 10 + 41 + 19]>(self) };
		let yakuman = core::simd::Simd::<_, 19>::from_slice(&this[10 + 41..]);
		let yakuman = core::simd::num::SimdUint::reduce_sum(yakuman);
		Yakuman(yakuman)
	}
}

impl core::fmt::Display for Fu {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "{} fu", self.0)
	}
}

impl core::fmt::Display for Han {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "{} han", self.0)
	}
}

impl core::fmt::Display for Yakuman {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		// Micro-optimization: `f.write_str(match self.duplicate { ... })` causes each string to be stored as a separate constant
		// and generates a jump table to load the corresponding constant and length.
		// Making a single string and calculating the start and length using arithmetic avoids the LUT.
		const STRINGS: &str = "\
			?????????????????\
			Yakuman??????????\
			Double yakuman???\
			Triple yakuman???\
			Quadruple yakuman\
			Quintuple yakuman\
			Sextuple yakuman?\
			Too many yakuman?\
		";

		let n = self.0.min(7);
		let start = usize::from(n * 17);
		let len =
			usize::from(n >= 1) * 7
			+ usize::from(n >= 2) * 7
			+ usize::from(n >= 4) * 3
			- usize::from(n >= 6);
		let end = start + len;
		// Micro-optimization: rustc does not notice that all the ranges are valid and emits a str slice check, so assert that they are valid.
		unsafe { core::hint::assert_unchecked(start <= end); }
		unsafe { core::hint::assert_unchecked(end <= STRINGS.len()); }
		let s = &STRINGS[start..end];
		f.write_str(s)
	}
}

impl core::fmt::Display for ScoreAggregate {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		if self.yakuman.0 > 0 {
			self.yakuman.fmt(f)
		}
		else {
			write!(f, "{} {}", self.han, self.fu)?;
			match self.han.0 {
				han @ 1..=5 if ((u32::from(self.fu.0) << 2) << han) >= 2000 => f.write_str(" Mangan"),
				6..=7 => f.write_str(" Haneman"),
				8..=10 => f.write_str(" Baiman"),
				11.. => f.write_str(" Sanbaiman"),
				_ => Ok(()),
			}
		}
	}
}

impl From<Score> for ScoreAggregate {
	fn from(score: Score) -> Self {
		let fu = score.fu();
		let han = score.han();
		let yakuman = score.yakuman();
		Self { fu, han, yakuman }
	}
}

impl Points {
	/// Returns the sum of points gained by this player.
	pub const fn total(self) -> u32 {
		self.riichi_bou + self.shimocha + self.toimen + self.kamicha
	}

	/// Returns the points to be added or subtracted from all players, identified by their seat winds.
	///
	/// The given seat wind of the current player is used to derive the seat winds of the other players.
	pub const fn to_absolute(self, seat_wind: WindTile) -> PointsAbsolute {
		let mut result = core::mem::MaybeUninit::<PointsAbsolute>::uninit();
		{
			let result = result.as_mut_ptr();
			let me = (seat_wind as u8 - tw!(E) as u8) >> 1;
			let shimocha = (me + 1) % 4;
			let toimen = (me + 2) % 4;
			let kamicha = (me + 3) % 4;
			let me = unsafe { (&raw mut (*result).ton).add(me.into()) };
			let shimocha = unsafe { (&raw mut (*result).ton).add(shimocha.into()) };
			let toimen = unsafe { (&raw mut (*result).ton).add(toimen.into()) };
			let kamicha = unsafe { (&raw mut (*result).ton).add(kamicha.into()) };
			unsafe {
				me.write(self.total().cast_signed());
				shimocha.write(-(self.shimocha.cast_signed()));
				toimen.write(-(self.toimen.cast_signed()));
				kamicha.write(-(self.kamicha.cast_signed()));
			}
		}
		unsafe { result.assume_init() }
	}
}

impl core::fmt::Display for Points {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let mut wrote = false;
		if self.shimocha > 0 {
			write!(f, "shimocha: {}", self.shimocha)?;
			wrote = true;
		}
		if self.toimen > 0 {
			if wrote { f.write_str(", ")?; }
			write!(f, "toimen: {}", self.toimen)?;
			wrote = true;
		}
		if self.kamicha > 0 {
			if wrote { f.write_str(", ")?; }
			write!(f, "kamicha: {}", self.kamicha)?;
		}
		Ok(())
	}
}

const impl core::ops::Index<SeatRelative> for Points {
	type Output = u32;

	fn index(&self, seat: SeatRelative) -> &Self::Output {
		match seat {
			SeatRelative::Shimocha => &self.shimocha,
			SeatRelative::Toimen => &self.toimen,
			SeatRelative::Kamicha => &self.kamicha,
		}
	}
}

const impl core::ops::IndexMut<SeatRelative> for Points {
	fn index_mut(&mut self, seat: SeatRelative) -> &mut Self::Output {
		match seat {
			SeatRelative::Shimocha => &mut self.shimocha,
			SeatRelative::Toimen => &mut self.toimen,
			SeatRelative::Kamicha => &mut self.kamicha,
		}
	}
}

impl core::fmt::Display for PointsAbsolute {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		let mut wrote = false;
		if self.ton != 0 {
			write!(f, "ton: {:+}", self.ton)?;
			wrote = true;
		}
		if self.nan != 0 {
			if wrote { f.write_str(", ")?; }
			write!(f, "nan: {:+}", self.nan)?;
			wrote = true;
		}
		if self.shaa != 0 {
			if wrote { f.write_str(", ")?; }
			write!(f, "shaa: {:+}", self.shaa)?;
			wrote = true;
		}
		if self.pei != 0 {
			if wrote { f.write_str(", ")?; }
			write!(f, "pei: {:+}", self.pei)?;
		}
		Ok(())
	}
}

/// Convenience function to take the given sequence of [`ScorableHand`]s and return the one with the highest total points.
///
/// Returns `None` if none of the given hands have any yaku.
///
/// This is a wrapper around [`ScorableHand::score`], [`Score::score`] and [`Points::total`].
/// See their docs for more details about the parameters.
pub fn max_score(
	game_type: GameType,
	riichi_bou: u8,
	honba: u8,
	doras: &Tile34MultiSet,
	round_wind: WindTile,
	seat_wind: WindTile,
	nukidora: u8,
	riichi: Riichi,
	winning_tile: Tile,
	winning_tile_from: WinningTileFrom,
	daisangen_sekinin_barai: Option<SeatRelative>,
	daisuushii_sekinin_barai: Option<SeatRelative>,
	hands: impl IntoIterator<Item = ScorableHand>,
) -> Option<(ScorableHand, Score, Points, u32)> {
	hands.into_iter()
		.filter_map(|hand| {
			let score = hand.score(
				false,
				doras,
				round_wind,
				seat_wind,
				nukidora,
				riichi,
				winning_tile,
				winning_tile_from,
			)?;
			let points = score.score(game_type, riichi_bou, honba, seat_wind, winning_tile_from, daisangen_sekinin_barai, daisuushii_sekinin_barai);
			let total = points.total();
			Some((hand, score, points, total))
		})
		.max_by_key(|&(_, _, _, total)| total)
}

#[expect(clippy::cast_possible_truncation)]
const fn dora_match(doras: &Tile34MultiSet, tile: Tile) -> u8 {
	u8::from(tile.is_red()) + doras.get(tile) as u8
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use super::*;

	// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175
	//
	// > Each value to be paid is rounded up to the nearest 100. Because of how this rounding works,
	// > the totals for tsumo and ron do not always match.
	// > (For example, a 1 han 30 fu hand scores 240 basic points. Without rounding, a ron would score 960 points,
	// > and a tsumo would also score 240+240+480 = 960 points. As each individual player's payment is rounded,
	// > ron scores 1000, and tsumo scores 300+300+500 = 1100, or 100 more than ron.)
	#[test]
	fn score_rounding() {
		let score = Score { base: Fu(30), riichi: Han(1), ..Default::default() };
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(30), han: Han(1), yakuman: Yakuman(0) });

		let points = score.score(GameType::Yonma, 0, 0, tw!(S), WinningTileFrom::Ron(SeatRelative::Shimocha), None, None);
		assert_eq!(points, Points { shimocha: 960_u32.next_multiple_of(100), ..Default::default() });
		assert_eq!(points.total(), 960_u32.next_multiple_of(100));

		let points = score.score(GameType::Yonma, 0, 0, tw!(S), WinningTileFrom::Tsumo, None, None);
		assert_eq!(points, Points { shimocha: 240_u32.next_multiple_of(100), toimen: 240_u32.next_multiple_of(100), kamicha: 480_u32.next_multiple_of(100), ..Default::default() });
		assert_eq!(points.total(), 240_u32.next_multiple_of(100) + 240_u32.next_multiple_of(100) + 480_u32.next_multiple_of(100));
	}

	// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175
	//
	// > Example 1
	#[test]
	fn scoring_rules1() {
		let game_type = GameType::Yonma;
		let round_wind = tw!(E);
		let seat_wind = tw!(S);
		let hand = make_hand!(1s 2s 3s 5s 6s 9s 9s { minkou R R R } { minjun 1s 2s 3s });
		let winning_tile = t!(4s);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 1s 2s 3s } { minkou R R R } { minjun 1s 2s 3s } { minjun 4s 5s 6s ryanmen_low } { 9s 9s }));
		let score = hand.score(
			false,
			&Default::default(),
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			meld3: Fu(4), // { minkou R R R }
			rounding: Fu(6),
			yakuhai_chun: Han(1),
			honitsu: Han(2),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 4, 10)), han: Han(2 + 1), yakuman: Yakuman(0) });
		assert_eq!(score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, None).total(), 3900);
	}

	// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175
	//
	// > Example 2
	#[test]
	fn scoring_rules2() {
		let game_type = GameType::Yonma;
		let round_wind = tw!(E);
		let seat_wind = tw!(S);
		let hand = make_hand!(6p 6p 7p 7p 8p 9s 9s 9s G G { ankan 1m 1m 1m 1m });
		let winning_tile = t!(8p);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 6p 7p 8p } { ankou 9s 9s 9s } { ankan 1m 1m 1m 1m } { anjun 6p 7p 8p ryanmen_high } { G G }));
		let score = hand.score(
			false,
			&Default::default(),
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(2),
			meld1: Fu(32), // { ankan 1m 1m 1m 1m }
			meld3: Fu(8), // { ankou 9s 9s 9s }
			pair: Fu(2),
			rounding: Fu(6),
			mentsumo: Han(1),
			iipeikou: Han(1),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 32 + 8 + 2 + 2, 10)), han: Han(1 + 1), yakuman: Yakuman(0) });
		assert_eq!(score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, None).total(), 2240_u32.next_multiple_of(100) + 2 * 1120_u32.next_multiple_of(100));
	}

	// Ref: https://riichi.wiki/index.php?title=Sankantsu&oldid=27944
	#[test]
	fn sankantsu() {
		let game_type = GameType::Yonma;
		let round_wind = tw!(E);
		let seat_wind = tw!(S);
		let hand = make_hand!(2p 3p 9p 9p { minkan 2m 2m 2m 2m } { minkan 3m 3m 3m 3m } { minkan 4m 4m 4m 4m });
		let winning_tile = t!(4p);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkan 2m 2m 2m 2m } { minkan 3m 3m 3m 3m } { minkan 4m 4m 4m 4m } { minjun 2p 3p 4p ryanmen_high } { 9p 9p }));
		let score = hand.score(
			false,
			&Default::default(),
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			meld1: Fu(8), // { minkan 2m 2m 2m 2m }
			meld2: Fu(8), // { minkan 3m 3m 3m 3m }
			meld3: Fu(8), // { minkan 4m 4m 4m 4m }
			rounding: Fu(6),
			sankantsu: Han(2),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 8 + 8 + 8, 10)), han: Han(2), yakuman: Yakuman(0) });
		assert_eq!(score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, None).total(), 3200);
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727
	#[test]
	fn honroutou1() {
		let hand = make_hand!(1p 1p 9s 9s { minkou 9m 9m 9m } { minkou N N N } { minkou W W W });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let hands: std::vec::Vec<_> = t![1p, 9s].into_iter().flat_map(|winning_tile| {
			let hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
			assert_eq!(hands.len(), 1);
			hands.into_iter().map(move |hand| (winning_tile, hand))
		}).collect();
		assert_eq!(hands[0].1, make_scorable_hand!({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { minkou 1p 1p 1p shanpon } { 9s 9s }));
		assert_eq!(hands[1].1, make_scorable_hand!({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { minkou 9s 9s 9s shanpon } { 1p 1p }));
		for (winning_tile, hand) in hands {
			let score = hand.score(
				false,
				&Default::default(),
				tw!(E),
				tw!(E),
				0,
				Riichi::NotRiichi,
				winning_tile,
				winning_tile_from,
			).unwrap();
			assert_eq!(score, Score {
				base: Fu(20),
				meld1: Fu(4), // { minkou 9m 9m 9m }
				meld2: Fu(4), // { minkou W W W }
				meld3: Fu(4), // { minkou N N N }
				meld4: Fu(4), // { minkou 1p 1p 1p }
				rounding: Fu(4),
				toitoi: Han(2),
				honroutou: Han(2),
				..Default::default()
			});
			assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 4 + 4 + 4 + 4, 10)), han: Han(2 + 2), yakuman: Yakuman(0) });
		}
	}

	// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727
	#[test]
	fn honroutou2() {
		let hand = make_hand!(9m 9m 1p 1p 1s 1s 9s 9s S S W W N);
		let winning_tile = t!(N);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ 9m 9m } { 1p 1p } { 1s 1s } { 9s 9s } { S S } { W W } { N N }));
		let score = hand.score(
			false,
			&Default::default(),
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(25),
			chiitoi: Han(2),
			honroutou: Han(2),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(25), han: Han(2 + 2), yakuman: Yakuman(0) });
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371
	#[test]
	fn shousangen1() {
		let hand = make_hand!(2p 3p 4p 3s 4s G G { minkou Wh Wh Wh } { minkou R R R });
		let winning_tile = t!(5s);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_high } { G G }));

		let score = hand.score(
			false,
			&Default::default(),
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			meld2: Fu(4), // { minkou Wh Wh Wh }
			meld3: Fu(4), // { minkou R R R }
			pair: Fu(2),
			yakuhai_haku: Han(1),
			yakuhai_chun: Han(1),
			shousangen: Han(2),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 4 + 4 + 2, 10)), han: Han(1 + 1 + 2), yakuman: Yakuman(0) });
	}

	// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371
	#[test]
	fn shousangen2() {
		let hand = make_hand!(5m 6m 7m 1s 2s 3s G G R R { minkou Wh Wh Wh });
		let winning_tile = t!(G);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 5m 6m 7m } { anjun 1s 2s 3s } { minkou Wh Wh Wh } { minkou G G G shanpon } { R R }));
		let score = hand.score(
			false,
			&Default::default(),
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			meld3: Fu(4), // { minkou Wh Wh Wh }
			meld4: Fu(4), // { minkou G G G }
			pair: Fu(2),
			yakuhai_haku: Han(1),
			yakuhai_hatsu: Han(1),
			shousangen: Han(2),
			..Default::default()
		});

		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 4 + 4 + 2, 10)), han: Han(1 + 1 + 2), yakuman: Yakuman(0) });
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > Chinitsu with san ankou, riichi, tsumo, and some dora.
	#[test]
	fn kazoe_yakuman1() {
		let game_type = GameType::Yonma;
		let doras = t34multiset![9p,].indicates_dora(game_type);
		let hand = make_hand!(1p 1p 1p 2p 3p 5p 5p 0p 7p 7p 7p 9p 9p);
		let winning_tile = t!(1p);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 2);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankou 1p 1p 1p } { ankou 5p 5p 0p } { ankou 7p 7p 7p } { anjun 1p 2p 3p ryanmen_low } { 9p 9p }));
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 1p 2p 3p } { ankou 5p 5p 0p } { ankou 7p 7p 7p } { ankou 1p 1p 1p shanpon } { 9p 9p }));
		let score = hand.score(
			false,
			&doras,
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: false, ippatsu: false },
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(2),
			meld2: Fu(4), // { ankou 5p 5p 0p }
			meld3: Fu(4), // { ankou 7p 7p 7p }
			meld4: Fu(8), // { ankou 1p 1p 1p }
			rounding: Fu(2),
			mentsumo: Han(1),
			riichi: Han(1),
			sanankou: Han(2),
			chinitsu: Han(6),
			dora: Han(5),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > Riichi with 12+ dora
	#[test]
	fn kazoe_yakuman2() {
		let game_type = GameType::Yonma;
		let doras = t34multiset![4m, Wh, 2p, 2p, W, 4m].indicates_dora(game_type);
		let hand = make_hand!(3p 3p 3p 6p 7p 8p 1m 1m 6m 6m { ankan 5m 0m 5m 5m });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);

		{
			let winning_tile = t!(1m);
			let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
			assert_eq!(hands.len(), 1);
			let hand = hands.pop_first().unwrap();
			assert_eq!(hand, make_scorable_hand!({ ankan 5m 0m 5m 5m } { ankou 3p 3p 3p } { anjun 6p 7p 8p } { minkou 1m 1m 1m shanpon } { 6m 6m }));
			let score = hand.score(
				false,
				&doras,
				tw!(E),
				tw!(E),
				0,
				Riichi::Riichi { double: false, ippatsu: false },
				winning_tile,
				winning_tile_from,
			).unwrap();
			assert_eq!(score, Score {
				base: Fu(20),
				win_condition: Fu(10),
				meld1: Fu(16), // { ankan 5m 0m 5m 5m }
				meld2: Fu(4), // { ankou 3p 3p 3p }
				meld4: Fu(4), // { minkou 1m 1m 1m }
				rounding: Fu(6),
				riichi: Han(1),
				dora: Han(15),
				kazoe_yakuman: Yakuman(1),
				..Default::default()
			});
		}

		{
			let winning_tile = t!(6m);
			let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
			assert_eq!(hands.len(), 1);
			let hand = hands.pop_first().unwrap();
			assert_eq!(hand, make_scorable_hand!({ ankan 5m 0m 5m 5m } { ankou 3p 3p 3p } { anjun 6p 7p 8p } { minkou 6m 6m 6m shanpon } { 1m 1m }));
			let score = hand.score(
				false,
				&doras,
				tw!(E),
				tw!(E),
				0,
				Riichi::Riichi { double: false, ippatsu: false },
				winning_tile,
				winning_tile_from,
			).unwrap();
			assert_eq!(score, Score {
				base: Fu(20),
				win_condition: Fu(10),
				meld1: Fu(16), // { ankan 5m 0m 5m 5m }
				meld2: Fu(4), // { ankou 3p 3p 3p }
				meld4: Fu(2), // { minkou 6m 6m 6m }
				rounding: Fu(8),
				riichi: Han(1),
				dora: Han(15),
				kazoe_yakuman: Yakuman(1),
				..Default::default()
			});
		}
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > Chinitsu with ryanpeikou, tanyao, pinfu, riichi, and tsumo.
	#[test]
	fn kazoe_yakuman3() {
		let hand = make_hand!(2s 2s 3s 3s 4s 4s 5s 5s 6s 6s 7s 8s 8s);
		let winning_tile = t!(7s);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 4);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 3s 4s 5s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s kanchan } { 2s 2s }));
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s kanchan } { 5s 5s }));
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 5s 6s 7s ryanmen_high } { 8s 8s }));
		let score = hand.score(
			false,
			&Default::default(),
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: false, ippatsu: false },
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			mentsumo: Han(1),
			riichi: Han(1),
			pinfu: Han(1),
			tanyao: Han(1),
			ryanpeikou: Han(3),
			chinitsu: Han(6),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ 2s 2s } { 3s 3s } { 4s 4s } { 5s 5s } { 6s 6s } { 7s 7s } { 8s 8s }));
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > Shousangen with haku, hatsu, toitoi, sanankou, honroutou, honitsu, and sankantsu
	#[test]
	fn kazoe_yakuman4() {
		let hand = make_hand!(1p 1p 1p R { ankan 9p 9p 9p 9p } { minkan Wh Wh Wh Wh } { ankan G G G G });
		let winning_tile = t!(R);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankou 1p 1p 1p } { ankan 9p 9p 9p 9p } { minkan Wh Wh Wh Wh } { ankan G G G G } { R R }));
		let score = hand.score(
			false,
			&Default::default(),
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			meld1: Fu(8), // { ankou 1p 1p 1p }
			meld2: Fu(32), // { ankan 9p 9p 9p 9p }
			meld3: Fu(16), // { minkan Wh Wh Wh Wh }
			meld4: Fu(32), // { ankan G G G G }
			pair: Fu(2),
			wait: Fu(2),
			rounding: Fu(8),
			yakuhai_haku: Han(1),
			yakuhai_hatsu: Han(1),
			toitoi: Han(2),
			sanankou: Han(2),
			sankantsu: Han(2),
			honroutou: Han(2),
			shousangen: Han(2),
			honitsu: Han(2),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > Shousangen with haku, chun, double ton, toitoi, sankantsu, rinshan kaihou, honitsu
	#[test]
	fn kazoe_yakuman5() {
		let hand = make_hand!(G { ankan Wh Wh Wh Wh } { minkan R R R R } { minkan E E E E } { minkou 8s 8s 8s });
		let winning_tile = t!(G);
		let winning_tile_from = WinningTileFrom::Rinshan;
		let hand = hand.to_scorable_hand(winning_tile).unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkou 8s 8s 8s } { minkan E E E E } { ankan Wh Wh Wh Wh } { minkan R R R R } { G G }));
		let score = hand.score(
			false,
			&Default::default(),
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(2),
			meld1: Fu(2), // { minkou 8s 8s 8s }
			meld2: Fu(16), // { minkan E E E E }
			meld3: Fu(32), // { ankan Wh Wh Wh Wh }
			meld4: Fu(16), // { minkan R R R R }
			pair: Fu(2),
			wait: Fu(2),
			rounding: Fu(8),
			rinshan: Han(1),
			yakuhai_ton: Han(2),
			yakuhai_haku: Han(1),
			yakuhai_chun: Han(1),
			toitoi: Han(2),
			sankantsu: Han(2),
			shousangen: Han(2),
			honitsu: Han(2),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > The largest hand possible without regular yakuman
	// >
	// > Dealer in the east round
	// >
	// > 60 han with double riichi, houtei, haku, hatsu, double ton, sankantsu, toitoi, sanankou, shousangen, honroutou, honitsu, 20 dora, and 20 ura dora.
	#[test]
	fn kazoe_yakuman6() {
		let game_type = GameType::Yonma;
		let doras = t34multiset![9m, 9m, 9m, 9m, R, N, N, N, N, R].indicates_dora(game_type);
		let hand = make_hand!(G G R R { ankan 1m 1m 1m 1m } { ankan E E E E } { ankan Wh Wh Wh Wh });
		let winning_tile = t!(G);
		let winning_tile_from = WinningTileFrom::Houtei(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankan 1m 1m 1m 1m } { ankan E E E E } { ankan Wh Wh Wh Wh } { minkou G G G shanpon } { R R }));
		let score = hand.score(
			false,
			&doras,
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: true, ippatsu: false },
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(10),
			meld1: Fu(32), // { ankan 1m 1m 1m 1m }
			meld2: Fu(32), // { ankan E E E E }
			meld3: Fu(32), // { ankan Wh Wh Wh Wh }
			meld4: Fu(4), // { minkou G G G }
			pair: Fu(2),
			rounding: Fu(8),
			riichi: Han(2),
			houtei: Han(1),
			yakuhai_ton: Han(2),
			yakuhai_haku: Han(1),
			yakuhai_hatsu: Han(1),
			toitoi: Han(2),
			sanankou: Han(2),
			sankantsu: Han(2),
			honroutou: Han(2),
			shousangen: Han(2),
			honitsu: Han(3),
			dora: Han(40),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score).han, Han(60));
	}

	// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957
	//
	// > The largest hand possible without regular yakuman
	// >
	// > South seat in the south round (only possible in sanma)
	// >
	// > 64 han with double riichi, houtei, haku, hatsu, double ton, sankantsu, toitoi, sanankou, shousangen, honroutou, honitsu, 20 dora, 20 ura dora, and 4 nukidora.
	#[test]
	fn kazoe_yakuman7() {
		let game_type = GameType::Sanma;
		let doras = t34multiset![9m, 9m, 9m, 9m, R, E, E, E, E, R].indicates_dora(game_type);
		let hand = make_hand!(G G R R { ankan 1m 1m 1m 1m } { ankan S S S S } { ankan Wh Wh Wh Wh });
		let winning_tile = t!(G);
		let winning_tile_from = WinningTileFrom::Houtei(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankan 1m 1m 1m 1m } { ankan S S S S } { ankan Wh Wh Wh Wh } { minkou G G G shanpon } { R R }));
		let score = hand.score(
			false,
			&doras,
			tw!(S),
			tw!(S),
			4,
			Riichi::Riichi { double: true, ippatsu: false },
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(10),
			meld1: Fu(32), // { ankan 1m 1m 1m 1m }
			meld2: Fu(32), // { ankan S S S S }
			meld3: Fu(32), // { ankan Wh Wh Wh Wh }
			meld4: Fu(4), // { minkou G G G }
			pair: Fu(2),
			rounding: Fu(8),
			riichi: Han(2),
			houtei: Han(1),
			yakuhai_nan: Han(2),
			yakuhai_haku: Han(1),
			yakuhai_hatsu: Han(1),
			toitoi: Han(2),
			sanankou: Han(2),
			sankantsu: Han(2),
			honroutou: Han(2),
			shousangen: Han(2),
			honitsu: Han(3),
			dora: Han(40),
			nukidora: Han(4),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score).han, Han(64));
	}

	// Ref: https://old.reddit.com/r/Mahjong/comments/ceotnt/kazoe_yakuman_with_only_yakuhai_and_12_dora/
	#[test]
	fn kazoe_yakuman8() {
		let game_type = GameType::Sanma;
		let doras = t34multiset![W, 1s, 2s, S].indicates_dora(game_type);
		let round_wind = tw!(S);
		// Seat wind is not visible in the screenshot, but based on the score it's the dealer wind (E).
		let seat_wind = tw!(E);
		let hand = make_hand!(6p 7p 8p 9s 9s S S { minkou 4p 4p 4p } { minkan 3s 3s 3s 3s });
		let winning_tile = t!(S);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(winning_tile, winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 6p 7p 8p } { minkou 4p 4p 4p } { minkan 3s 3s 3s 3s } { ankou S S S shanpon } { 9s 9s }));
		let score = hand.score(
			false,
			&doras,
			round_wind,
			seat_wind,
			4,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(2),
			meld1: Fu(2), // { minkou 4p 4p 4p }
			meld3: Fu(8), // { minkan 3s 3s 3s 3s }
			meld4: Fu(8), // { ankou S S S }
			yakuhai_nan: Han(1),
			dora: Han(8),
			nukidora: Han(4),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(u8::next_multiple_of(20 + 2 + 2 + 8 + 8, 10)), han: Han(13), yakuman: Yakuman(1) });
		assert_eq!(score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, None).total(), 32000);
	}

	// Ref: https://web.archive.org/web/20221214050908/https://cdn.discordapp.com/attachments/150412836500275200/513656427890475008/TIM20181118175603RGBnoiseLevel2.png
	//      from https://riichi.wiki/index.php?title=Mahjong_Soul&oldid=28198#Rules
	#[test]
	fn composite_yakuman() {
		let game_type = GameType::Yonma;
		let doras = t34multiset![3s,].indicates_dora(game_type);
		let round_wind = tw!(S);
		let seat_wind = tw!(E);
		let hand = make_hand!(R { minkou S S S } { minkou E E E } { minkou N N N } { minkan W W W W });
		let winning_tile = t!(R);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let hand = hand.to_scorable_hand(winning_tile).unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkou E E E } { minkou S S S } { minkan W W W W } { minkou N N N } { R R }));
		let score = hand.score(
			false,
			&doras,
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
			winning_tile,
			winning_tile_from,
		).unwrap();
		assert_eq!(score, Score {
			base: Fu(20),
			win_condition: Fu(2),
			meld1: Fu(4), // { minkou E E E }
			meld2: Fu(4), // { minkou S S S }
			meld3: Fu(16), // { minkan W W W W }
			meld4: Fu(4), // { minkou N N N }
			pair: Fu(2),
			wait: Fu(2),
			rounding: Fu(6),
			yakuhai_ton: Han(1),
			yakuhai_nan: Han(1),
			toitoi: Han(2),
			daisuushii: Yakuman(2),
			tsuuiisou: Yakuman(1),
			..Default::default()
		});
		assert_eq!(score.score(game_type, 0, 0, seat_wind, winning_tile_from, None, Some(SeatRelative::Shimocha)), Points { shimocha: 112000, toimen: 16000, kamicha: 16000, ..Default::default() });
	}

	#[test]
	fn yakuman_display() {
		assert_eq!(std::string::ToString::to_string(&Yakuman(0)), "");
		assert_eq!(std::string::ToString::to_string(&Yakuman(1)), "Yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(2)), "Double yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(3)), "Triple yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(4)), "Quadruple yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(5)), "Quintuple yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(6)), "Sextuple yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(7)), "Too many yakuman");
		assert_eq!(std::string::ToString::to_string(&Yakuman(8)), "Too many yakuman");
	}
}
