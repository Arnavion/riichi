use crate::{
	CmpIgnoreRed,
	GameType,
	Number, NumberTile,
	ScorableHand, ScorableHandFourthMeld, ScorableHandKokushiMusou, ScorableHandMeld, ScorableHandPair,
	Tile, TsumoOrRon,
	WindTile,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Riichi {
	NotRiichi,
	Riichi { ippatsu: bool, double: bool },
}

/// Seat relative to this player's seat.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SeatRelative {
	/// Player to the right.
	Shimocha,
	/// Player opposite.
	Toimen,
	/// Player to the left.
	Kamicha,
}

/// Indicates where the winning tile was drawn from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WinningTileFrom {
	/// The tile was drawn from the wall and was the last tile of the wall.
	Haitei,
	/// The tile was taken from another player's discard which was the last discard of the round.
	Houtei(SeatRelative),
	/// The tile was drawn from the dead wall because the player called a kan or played a nukidora.
	Rinshan,
	/// The tile was taken from another player's ankan.
	ChankanAnkan(SeatRelative),
	/// The tile was taken from another player's shouminkan.
	ChankanShouminkan(SeatRelative),
	/// The tile was the first tile drawn on the player's turn, when the player is a dealer.
	Tenhou,
	/// The tile was the first tile drawn on the player's turn from the wall, when the player is not a dealer,
	/// and no previous player had called a tile until this player's turn.
	Chiihou,
	/// The tile was drawn from the wall and wasn't any of the above possibilities.
	Tsumo,
	/// The tile was taken from another player's discard and wasn't any of the above possibilities.
	Ron(SeatRelative),
}

/// Broken down score for a [`ScorableHand`].
///
/// `Default` impl sets all fields to 0.
#[derive(Clone, Copy, Default, Eq, PartialEq)]
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

	pub honitsu: Han,

	pub junchan: Han,

	pub ryanpeikou: Han,

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
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Fu(pub u8);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Han(pub u8);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Yakuman(pub u8);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ScoreAggregate {
	pub fu: Fu,
	pub han: Han,
	pub yakuman: Yakuman,
}

/// The points to be taken from all players identified by their positions relative to the current player.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
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
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
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
			Self::Ron(seat) => Some(seat),
		}
	}
}

impl ScorableHand {
	/// Returns `None` if the hand has no yaku.
	#[expect(clippy::bool_to_int_with_if)]
	pub fn score(
		&self,
		doras: &[Tile],
		round_wind: WindTile,
		seat_wind: WindTile,
		nukidora: u8,
		riichi: Riichi,
		winning_tile_from: WinningTileFrom,
	) -> Option<Score> {
		let mut score: Score = Default::default();

		let tsumo_or_ron: TsumoOrRon = winning_tile_from.into();
		let is_menzen = self.is_menzen();
		let is_tanyao = self.is_tanyao();
		let chanta_routou = self.chanta_routou();
		let num_ankou = self.num_ankou();
		let honchinitsu = self.honchinitsu();

		match self {
			Self::Regular(h) => {
				let num_peikou = h.num_peikou();
				let suushii_sangen = h.suushii_sangen();

				score.base = Fu(20);

				let is_pinfu = h.is_pinfu(round_wind, seat_wind);

				match tsumo_or_ron {
					// TODO: > In a few scoring variations, a win by rinshan kaihou is also ineligible for the +2 fu from tsumo.
					TsumoOrRon::Tsumo if !is_pinfu => score.win_condition = Fu(2),
					TsumoOrRon::Ron if is_menzen => score.win_condition = Fu(10),
					_ => (),
				}

				score.meld1 = h.melds.0[0].fu();
				score.meld2 = h.melds.0[1].fu();
				score.meld3 = h.melds.0[2].fu();
				(score.meld4, score.wait) = h.melds.1.fu();
				score.pair = h.pair.fu(round_wind, seat_wind);

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
				score.haitei = Han(if matches!(winning_tile_from, WinningTileFrom::Haitei) { 1 } else { 0 });
				score.houtei = Han(if matches!(winning_tile_from, WinningTileFrom::Houtei(_)) { 1 } else { 0 });
				score.rinshan = Han(if matches!(winning_tile_from, WinningTileFrom::Rinshan) { 1 } else { 0 });
				score.chankan = Han(match winning_tile_from {
					// Only kokushi musou is allowed to chankan an ankan
					WinningTileFrom::ChankanAnkan(_) => return None,
					WinningTileFrom::ChankanShouminkan(_) => 1,
					_ => 0,
				});
				score.tanyao = Han(if is_tanyao { 1 } else { 0 });
				score.yakuhai_ton = Han(h.num_wind_yakuhai(tw!(E), round_wind, seat_wind));
				score.yakuhai_nan = Han(h.num_wind_yakuhai(tw!(S), round_wind, seat_wind));
				score.yakuhai_shaa = Han(h.num_wind_yakuhai(tw!(W), round_wind, seat_wind));
				score.yakuhai_pei = Han(h.num_wind_yakuhai(tw!(N), round_wind, seat_wind));
				score.yakuhai_haku = Han(if h.is_dragon_yakuhai(td!(Wh)) { 1 } else { 0 });
				score.yakuhai_hatsu = Han(if h.is_dragon_yakuhai(td!(G)) { 1 } else { 0 });
				score.yakuhai_chun = Han(if h.is_dragon_yakuhai(td!(R)) { 1 } else { 0 });

				score.chanta = Han(if chanta_routou.is_chanta() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.sanshoku_doujun = Han(if h.is_sanshoku_doujun() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.ittsuu = Han(if h.is_ittsuu() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.toitoi = Han(if h.is_toitoi() { 2 } else { 0 });
				score.sanankou = Han(if num_ankou.is_sanankou() { 2 } else { 0 });
				score.sanshoku_doukou = Han(if h.is_sanshoku_doukou() { 2 } else { 0 });
				score.sankantsu = Han(if h.is_sankantsu() { 2 } else { 0 });
				score.honroutou = Han(if chanta_routou.is_honroutou() { 2 } else { 0 });
				score.shousangen = Han(if suushii_sangen.is_shousangen() { 2 } else { 0 });

				score.honitsu = Han(if honchinitsu.is_honitsu() { if is_menzen { 3 } else { 2 } } else { 0 });
				score.junchan = Han(if chanta_routou.is_junchan() { if is_menzen { 3 } else { 2 } } else { 0 });
				score.ryanpeikou = Han(if num_peikou == 2 { 3 } else { 0 });

				score.chinitsu = Han(if honchinitsu.is_chinitsu() { if is_menzen { 6 } else { 5 } } else { 0 });

				score.suuankou = Yakuman(num_ankou.num_suuankou());
				score.daisangen = Yakuman(if suushii_sangen.is_daisangen() { 1 } else { 0 });
				score.shousuushii = Yakuman(if suushii_sangen.is_shousuushii() { 1 } else { 0 });
				score.daisuushii = Yakuman(if suushii_sangen.is_daisuushii() { 2 } else { 0 });
				score.tsuuiisou = Yakuman(if chanta_routou.is_tsuuiisou() { 1 } else { 0 });
				score.chinroutou = Yakuman(if chanta_routou.is_chinroutou() { 1 } else { 0 });
				score.ryuuiisou = Yakuman(if h.is_ryuuiisou() { 1 } else { 0 });
				score.chuuren_poutou = Yakuman(h.num_chuuren_poutou());
				score.suukantsu = Yakuman(if h.is_suukantsu() { 1 } else { 0 });
			},

			Self::Chiitoi(_) => {
				score.base = Fu(25);

				score.mentsumo = Han(if is_menzen && matches!(tsumo_or_ron, TsumoOrRon::Tsumo) { 1 } else { 0 });

				score.tanyao = Han(if is_tanyao { 1 } else { 0 });

				if let Riichi::Riichi { double, ippatsu } = riichi {
					score.riichi = Han(if double { 2 } else { 1 });
					score.ippatsu = Han(if ippatsu { 1 } else { 0 });
				}

				score.haitei = Han(if matches!(winning_tile_from, WinningTileFrom::Haitei) { 1 } else { 0 });
				score.houtei = Han(if matches!(winning_tile_from, WinningTileFrom::Houtei(_)) { 1 } else { 0 });

				score.chiitoi = Han(2);

				score.honroutou = Han(if chanta_routou.is_honroutou() { 2 } else { 0 });

				score.honitsu = Han(if honchinitsu.is_honitsu() { if is_menzen { 3 } else { 2 } } else { 0 });

				score.chinitsu = Han(if honchinitsu.is_chinitsu() { if is_menzen { 6 } else { 5 } } else { 0 });

				score.tsuuiisou = Yakuman(if chanta_routou.is_tsuuiisou() { 1 } else { 0 });
			},

			Self::KokushiMusou(ScorableHandKokushiMusou { was_juusanmen_wait, .. }) => {
				score.kokushi_musou = Yakuman(if *was_juusanmen_wait { 2 } else { 1 });
			},
		}

		score.tenhou = Yakuman(if matches!(winning_tile_from, WinningTileFrom::Tenhou) { 1 } else { 0 });
		score.chiihou = Yakuman(if matches!(winning_tile_from, WinningTileFrom::Chiihou) { 1 } else { 0 });

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
	fn fu(self) -> Fu {
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
	fn fu(self) -> (Fu, Fu) {
		let meld4 = ScorableHandMeld::from(self).fu();
		let wait = match self {
			Self::Tanki(_) |
			Self::Kanchan { .. } |
			Self::Penchan { .. } => Fu(2),
			Self::Shanpon { .. } |
			Self::RyanmenLow { .. } |
			Self::RyanmenHigh { .. } => Fu(0),
		};
		(meld4, wait)
	}
}

impl ScorableHandPair {
	fn fu(self, round_wind: WindTile, seat_wind: WindTile) -> Fu {
		Fu(self.num_yakuhai(round_wind, seat_wind) * 2)
	}
}

impl From<WinningTileFrom> for TsumoOrRon {
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
			chanta, sanshoku_doujun, ittsuu,
			toitoi, sanankou, sanshoku_doukou, sankantsu, chiitoi, honroutou, shousangen,
			honitsu, junchan, ryanpeikou,
			chinitsu,
			dora, nukidora,
			kazoe_yakuman, kokushi_musou, suuankou, daisangen, shousuushii, daisuushii, tsuuiisou, chinroutou, ryuuiisou, chuuren_poutou, suukantsu, tenhou, chiihou,
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
				0 => unreachable!("cannot have 0 han and 0 yakuman in a valid Score"),
				han @ 1..=5 => ((u32::from(self.fu().0) << 2) << han).min(2000),
				// haneman
				6..=7 => 3000,
				// baiman
				8..=10 => 4000,
				// sanbaiman
				11..=12 => 6000,
				// kazoe yakuman
				13.. => unreachable!("cannot have >= 13 han without also having >= 1 yakuman due to kazoe yakuman"),
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
			match seat_wind {
				tw!(E) => points.kamicha = 0,
				tw!(S) => points.toimen = 0,
				tw!(W) => points.shimocha = 0,
				tw!(N) => unreachable!(),
			}
		}

		points
	}

	fn fu(&self) -> Fu {
		self.base +
			self.win_condition +
			self.meld1 + self.meld2 + self.meld3 + self.meld4 + self.pair +
			self.wait + self.open_pinfu +
			self.rounding
	}

	fn han(&self) -> Han {
		self.mentsumo + self.riichi + self.ippatsu + self.pinfu + self.iipeikou +
			self.haitei + self.houtei + self.rinshan + self.chankan + self.tanyao +
			self.yakuhai_ton + self.yakuhai_nan + self.yakuhai_shaa + self.yakuhai_pei + self.yakuhai_haku + self.yakuhai_hatsu + self.yakuhai_chun +
			self.chanta + self.sanshoku_doujun + self.ittsuu +
			self.toitoi + self.sanankou + self.sanshoku_doukou + self.sankantsu + self.chiitoi + self.honroutou + self.shousangen +
			self.honitsu + self.junchan + self.ryanpeikou +
			self.chinitsu +
			self.dora + self.nukidora
	}

	fn yakuman(&self) -> Yakuman {
		self.kazoe_yakuman + self.kokushi_musou + self.suuankou + self.daisangen + self.shousuushii + self.daisuushii + self.tsuuiisou + self.chinroutou + self.ryuuiisou + self.chuuren_poutou + self.suukantsu + self.tenhou + self.chiihou
	}
}

impl core::ops::Add for Fu {
	type Output = Self;

	fn add(self, other: Self) -> Self::Output {
		Self(self.0 + other.0)
	}
}

impl core::fmt::Display for Fu {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "{} fu", self.0)
	}
}

impl core::ops::Add for Han {
	type Output = Self;

	fn add(self, other: Self) -> Self::Output {
		Self(self.0 + other.0)
	}
}

impl core::fmt::Display for Han {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "{} han", self.0)
	}
}

impl core::ops::Add for Yakuman {
	type Output = Self;

	fn add(self, other: Self) -> Self::Output {
		Self(self.0 + other.0)
	}
}

impl core::fmt::Display for Yakuman {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str(match self.0 {
			0 => "",
			1 => "Yakuman",
			2 => "Double yakuman",
			3 => "Triple yakuman",
			4 => "Quadruple yakuman",
			5 => "Quintuple yakuman",
			6 => "Sextuple yakuman",
			7.. => "Too many yakuman",
		})
	}
}

impl core::fmt::Display for ScoreAggregate {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		match self.yakuman.0 {
			0 => {
				write!(f, "{} {}", self.han, self.fu)?;
				#[expect(clippy::match_same_arms)]
				match self.han.0 {
					// cannot have 0 han and 0 yakuman in a valid Score
					0 => Ok(()),
					han @ 1..=5 =>
						if ((u32::from(self.fu.0) << 2) << han) >= 2000 {
							f.write_str(" Mangan")
						}
						else {
							Ok(())
						},
					6..=7 => f.write_str(" Haneman"),
					8..=10 => f.write_str(" Baiman"),
					11..=12 => f.write_str(" Sanbaiman"),
					// cannot have >= 13 han without also having >= 1 yakuman due to kazoe yakuman
					13.. => Ok(()),
				}
			},
			yakuman => Yakuman(yakuman).fmt(f),
		}
	}
}

impl From<Score> for ScoreAggregate {
	fn from(score: Score) -> Self {
		let Score {
			base,
			win_condition,
			meld1,
			meld2,
			meld3,
			meld4,
			pair,
			wait,
			open_pinfu,
			rounding,

			mentsumo,
			riichi,
			ippatsu,
			pinfu,
			iipeikou,
			haitei,
			houtei,
			rinshan,
			chankan,
			tanyao,
			yakuhai_ton,
			yakuhai_nan,
			yakuhai_shaa,
			yakuhai_pei,
			yakuhai_haku,
			yakuhai_hatsu,
			yakuhai_chun,
			chanta,
			sanshoku_doujun,
			ittsuu,
			toitoi,
			sanankou,
			sanshoku_doukou,
			sankantsu,
			chiitoi,
			honroutou,
			shousangen,
			honitsu,
			junchan,
			ryanpeikou,
			chinitsu,
			dora,
			nukidora,

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
		} = score;

		let fu =
			base +
			win_condition +
			meld1 +
			meld2 +
			meld3 +
			meld4 +
			pair +
			wait +
			open_pinfu +
			rounding;

		let han =
			mentsumo +
			riichi +
			ippatsu +
			pinfu +
			iipeikou +
			haitei +
			houtei +
			rinshan +
			chankan +
			tanyao +
			yakuhai_ton +
			yakuhai_nan +
			yakuhai_shaa +
			yakuhai_pei +
			yakuhai_haku +
			yakuhai_hatsu +
			yakuhai_chun +
			chanta +
			sanshoku_doujun +
			ittsuu +
			toitoi +
			sanankou +
			sanshoku_doukou +
			sankantsu +
			chiitoi +
			honroutou +
			shousangen +
			honitsu +
			junchan +
			ryanpeikou +
			chinitsu +
			dora +
			nukidora;

		let yakuman =
			kazoe_yakuman +
			kokushi_musou +
			suuankou +
			daisangen +
			shousuushii +
			daisuushii +
			tsuuiisou +
			chinroutou +
			ryuuiisou +
			chuuren_poutou +
			suukantsu +
			tenhou +
			chiihou;

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
			let ton = unsafe { &raw mut (*result).ton };
			let nan = unsafe { &raw mut (*result).nan };
			let shaa = unsafe { &raw mut (*result).shaa };
			let pei = unsafe { &raw mut (*result).pei };
			let (me, shimocha, toimen, kamicha) = match seat_wind {
				tw!(E) => (ton, nan, shaa, pei),
				tw!(S) => (nan, shaa, pei, ton),
				tw!(W) => (shaa, pei, ton, nan),
				tw!(N) => (pei, ton, nan, shaa),
			};
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

impl core::ops::Index<SeatRelative> for Points {
	type Output = u32;

	fn index(&self, seat: SeatRelative) -> &Self::Output {
		match seat {
			SeatRelative::Shimocha => &self.shimocha,
			SeatRelative::Toimen => &self.toimen,
			SeatRelative::Kamicha => &self.kamicha,
		}
	}
}

impl core::ops::IndexMut<SeatRelative> for Points {
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
	doras: &[Tile],
	round_wind: WindTile,
	seat_wind: WindTile,
	nukidora: u8,
	riichi: Riichi,
	winning_tile_from: WinningTileFrom,
	daisangen_sekinin_barai: Option<SeatRelative>,
	daisuushii_sekinin_barai: Option<SeatRelative>,
	hands: impl IntoIterator<Item = ScorableHand>,
) -> Option<(ScorableHand, Score, Points, u32)> {
	hands.into_iter()
		.filter_map(|hand| {
			let score = hand.score(
				doras,
				round_wind,
				seat_wind,
				nukidora,
				riichi,
				winning_tile_from,
			)?;
			let points = score.score(game_type, riichi_bou, honba, seat_wind, winning_tile_from, daisangen_sekinin_barai, daisuushii_sekinin_barai);
			let total = points.total();
			Some((hand, score, points, total))
		})
		.max_by_key(|&(_, _, _, total)| total)
}

fn dora_match(doras: &[Tile], tile: Tile) -> u8 {
	let result =
		usize::from(matches!(NumberTile::try_from(tile), Ok(t) if t.number() == Number::FiveRed)) +
		doras.iter().filter(|&&d| tile.eq_ignore_red(&d)).count();
	unsafe { core::hint::assert_unchecked(result <= 14); }
	result.try_into().expect("cannot have more than 14 doras")
}

#[cfg(test)]
mod tests {
	extern crate std;

	use super::*;

	#[test]
	fn score_rounding() {
		// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175
		//
		// > Each value to be paid is rounded up to the nearest 100. Because of how this rounding works,
		// > the totals for tsumo and ron do not always match.
		// > (For example, a 1 han 30 fu hand scores 240 basic points. Without rounding, a ron would score 960 points,
		// > and a tsumo would also score 240+240+480 = 960 points. As each individual player's payment is rounded,
		// > ron scores 1000, and tsumo scores 300+300+500 = 1100, or 100 more than ron.)

		let score = Score { base: Fu(30), riichi: Han(1), ..Default::default() };
		assert_eq!(ScoreAggregate::from(score), ScoreAggregate { fu: Fu(30), han: Han(1), yakuman: Yakuman(0) });

		let points = score.score(GameType::Yonma, 0, 0, tw!(S), WinningTileFrom::Ron(SeatRelative::Shimocha), None, None);
		assert_eq!(points, Points { shimocha: 960_u32.next_multiple_of(100), ..Default::default() });
		assert_eq!(points.total(), 960_u32.next_multiple_of(100));

		let points = score.score(GameType::Yonma, 0, 0, tw!(S), WinningTileFrom::Tsumo, None, None);
		assert_eq!(points, Points { shimocha: 240_u32.next_multiple_of(100), toimen: 240_u32.next_multiple_of(100), kamicha: 480_u32.next_multiple_of(100), ..Default::default() });
		assert_eq!(points.total(), 240_u32.next_multiple_of(100) + 240_u32.next_multiple_of(100) + 480_u32.next_multiple_of(100));
	}

	#[test]
	fn score_example1() {
		// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175 "Example 1"

		let game_type = GameType::Yonma;
		let round_wind = tw!(E);
		let seat_wind = tw!(S);
		let hand = make_hand!(1s 2s 3s 5s 6s 9s 9s { minkou R R R } { minjun 1s 2s 3s });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(4s), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 1s 2s 3s } { minkou R R R } { minjun 1s 2s 3s } { minjun 4s 5s 6s ryanmen_low } { 9s 9s }));
		let score = hand.score(
			&[],
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
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

	#[test]
	fn score_example2() {
		// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175 "Example 2"

		let game_type = GameType::Yonma;
		let round_wind = tw!(E);
		let seat_wind = tw!(S);
		let hand = make_hand!(6p 6p 7p 7p 8p 9s 9s 9s G G { ankan 1m 1m 1m 1m });
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(8p), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 6p 7p 8p } { ankou 9s 9s 9s } { ankan 1m 1m 1m 1m } { anjun 6p 7p 8p ryanmen_high } { G G }));
		let score = hand.score(
			&[],
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
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

	#[test]
	fn sankantsu() {
		// Ref: https://riichi.wiki/index.php?title=Sankantsu&oldid=27944

		let game_type = GameType::Yonma;
		let round_wind = tw!(E);
		let seat_wind = tw!(S);
		let hand = make_hand!(2p 3p 9p 9p { minkan 2m 2m 2m 2m } { minkan 3m 3m 3m 3m } { minkan 4m 4m 4m 4m });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(4p), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkan 2m 2m 2m 2m } { minkan 3m 3m 3m 3m } { minkan 4m 4m 4m 4m } { minjun 2p 3p 4p ryanmen_high } { 9p 9p }));
		let score = hand.score(
			&[],
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
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

	#[test]
	fn honroutou() {
		// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727

		let hand = make_hand!(1p 1p 9s 9s { minkou 9m 9m 9m } { minkou N N N } { minkou W W W });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let hands: std::vec::Vec<_> = t![1p, 9s].into_iter().flat_map(|new_tile| {
			let hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(new_tile, winning_tile_from.into()).collect();
			assert_eq!(hands.len(), 1);
			hands
		}).collect();
		assert_eq!(hands[0], make_scorable_hand!({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { minkou 1p 1p 1p shanpon } { 9s 9s }));
		assert_eq!(hands[1], make_scorable_hand!({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { minkou 9s 9s 9s shanpon } { 1p 1p }));
		for hand in hands {
			let score = hand.score(
				&[],
				tw!(E),
				tw!(E),
				0,
				Riichi::NotRiichi,
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

		let hand = make_hand!(9m 9m 1p 1p 1s 1s 9s 9s S S W W N);
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(N), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ 9m 9m } { 1p 1p } { 1s 1s } { 9s 9s } { S S } { W W } { N N }));
		let score = hand.score(
			&[],
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
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

	#[test]
	fn shousangen() {
		// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371

		let hand = make_hand!(2p 3p 4p 3s 4s G G { minkou Wh Wh Wh } { minkou R R R });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(5s), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_high } { G G }));

		let score = hand.score(
			&[],
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
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

		let hand = make_hand!(5m 6m 7m 1s 2s 3s G G R R { minkou Wh Wh Wh });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(G), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 5m 6m 7m } { anjun 1s 2s 3s } { minkou Wh Wh Wh } { minkou G G G shanpon } { R R }));
		let score = hand.score(
			&[],
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
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

	#[test]
	fn kazoe_yakuman() {
		// Ref: https://riichi.wiki/index.php?title=Kazoe_yakuman&oldid=27957

		// > Chinitsu with san ankou, riichi, tsumo, and some dora.

		let game_type = GameType::Yonma;
		let doras = [t!(9p)].map(|t| t.indicates_dora(game_type));
		let hand = make_hand!(1p 1p 1p 2p 3p 5p 5p 0p 7p 7p 7p 9p 9p);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(1p), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 2);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankou 1p 1p 1p } { ankou 5p 5p 0p } { ankou 7p 7p 7p } { anjun 1p 2p 3p ryanmen_low } { 9p 9p }));
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 1p 2p 3p } { ankou 5p 5p 0p } { ankou 7p 7p 7p } { ankou 1p 1p 1p shanpon } { 9p 9p }));
		let score = hand.score(
			&doras,
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: false, ippatsu: false },
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

		// > Riichi with 12+ dora

		let game_type = GameType::Yonma;
		let doras = t![4m, Wh, 2p, 2p, W, 4m].map(|t| t.indicates_dora(game_type));
		let hand = make_hand!(3p 3p 3p 6p 7p 8p 1m 1m 6m 6m { ankan 5m 0m 5m 5m });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(1m), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankan 5m 0m 5m 5m } { ankou 3p 3p 3p } { anjun 6p 7p 8p } { minkou 1m 1m 1m shanpon } { 6m 6m }));
		let score = hand.score(
			&doras,
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: false, ippatsu: false },
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

		let hand = make_hand!(3p 3p 3p 6p 7p 8p 1m 1m 6m 6m { ankan 5m 0m 5m 5m });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(6m), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankan 5m 0m 5m 5m } { ankou 3p 3p 3p } { anjun 6p 7p 8p } { minkou 6m 6m 6m shanpon } { 1m 1m }));
		let score = hand.score(
			&doras,
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: false, ippatsu: false },
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

		// > Chinitsu with ryanpeikou, tanyao, pinfu, riichi, and tsumo.

		let hand = make_hand!(2s 2s 3s 3s 4s 4s 5s 5s 6s 6s 7s 8s 8s);
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(7s), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 4);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 5s 6s 7s } { anjun 5s 6s 7s ryanmen_high } { 8s 8s }));
		let score = hand.score(
			&[],
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: false, ippatsu: false },
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
		assert_eq!(hand, make_scorable_hand!({ anjun 2s 3s 4s } { anjun 2s 3s 4s } { anjun 6s 7s 8s } { anjun 6s 7s 8s kanchan } { 5s 5s }));
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 3s 4s 5s } { anjun 3s 4s 5s } { anjun 6s 7s 8s } { anjun 6s 7s 8s kanchan } { 2s 2s }));
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ 2s 2s } { 3s 3s } { 4s 4s } { 5s 5s } { 6s 6s } { 7s 7s } { 8s 8s }));

		// > Shousangen with haku, hatsu, toitoi, sanankou, honroutou, honitsu, and sankantsu

		let hand = make_hand!(1p 1p 1p R { ankan 9p 9p 9p 9p } { minkan Wh Wh Wh Wh } { ankan G G G G });
		let winning_tile_from = WinningTileFrom::Ron(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(R), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankou 1p 1p 1p } { ankan 9p 9p 9p 9p } { minkan Wh Wh Wh Wh } { ankan G G G G } { R R }));
		let score = hand.score(
			&[],
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
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

		// > Shousangen with haku, chun, double ton, toitoi, sankantsu, rinshan kaihou, honitsu

		let hand = make_hand!(G { ankan Wh Wh Wh Wh } { minkan R R R R } { minkan E E E E } { minkou 8s 8s 8s });
		let winning_tile_from = WinningTileFrom::Rinshan;
		let hand = hand.to_scorable_hand(t!(G)).unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkou 8s 8s 8s } { minkan E E E E } { ankan Wh Wh Wh Wh } { minkan R R R R } { G G }));
		let score = hand.score(
			&[],
			tw!(E),
			tw!(E),
			0,
			Riichi::NotRiichi,
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

		// > The largest hand possible without regular yakuman
		// >
		// > 60 han with double riichi, houtei, haku, hatsu, double ton, sankantsu, toitoi, sanankou, shousangen, honroutou, honitsu, 20 dora, and 20 ura dora.

		let game_type = GameType::Yonma;
		let doras = t![9m, 9m, 9m, 9m, R, N, N, N, N, R].map(|t| t.indicates_dora(game_type));
		let hand = make_hand!(G G R R { ankan 1m 1m 1m 1m } { ankan E E E E } { ankan Wh Wh Wh Wh });
		let winning_tile_from = WinningTileFrom::Houtei(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(G), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankan 1m 1m 1m 1m } { ankan E E E E } { ankan Wh Wh Wh Wh } { minkou G G G shanpon } { R R }));
		let score = hand.score(
			&doras,
			tw!(E),
			tw!(E),
			0,
			Riichi::Riichi { double: true, ippatsu: false },
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


		// > The largest hand possible without regular yakuman
		// >
		// > 64 han with double riichi, houtei, haku, hatsu, double ton, sankantsu, toitoi, sanankou, shousangen, honroutou, honitsu, 20 dora, 20 ura dora, and 4 nukidora.

		let game_type = GameType::Sanma;
		let doras = t![9m, 9m, 9m, 9m, R, E, E, E, E, R].map(|t| t.indicates_dora(game_type));
		let hand = make_hand!(G G R R { ankan 1m 1m 1m 1m } { ankan S S S S } { ankan Wh Wh Wh Wh });
		let winning_tile_from = WinningTileFrom::Houtei(SeatRelative::Shimocha);
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(G), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ ankan 1m 1m 1m 1m } { ankan S S S S } { ankan Wh Wh Wh Wh } { minkou G G G shanpon } { R R }));
		let score = hand.score(
			&doras,
			tw!(S),
			tw!(S),
			4,
			Riichi::Riichi { double: true, ippatsu: false },
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

		// Ref: https://old.reddit.com/r/Mahjong/comments/ceotnt/kazoe_yakuman_with_only_yakuhai_and_12_dora/

		let game_type = GameType::Sanma;
		let doras = t![W, 1s, 2s, S].map(|t| t.indicates_dora(game_type));
		let round_wind = tw!(S);
		// Seat wind is not visible in the screenshot, but based on the score it's the dealer wind (E).
		let seat_wind = tw!(E);
		let hand = make_hand!(6p 7p 8p 9s 9s S S { minkou 4p 4p 4p } { minkan 3s 3s 3s 3s });
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands: std::collections::BTreeSet<_> = hand.to_scorable_hands(t!(S), winning_tile_from.into()).collect();
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 6p 7p 8p } { minkou 4p 4p 4p } { minkan 3s 3s 3s 3s } { ankou S S S shanpon } { 9s 9s }));
		let score = hand.score(
			&doras,
			round_wind,
			seat_wind,
			4,
			Riichi::NotRiichi,
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

	#[test]
	fn composite_yakuman() {
		// Ref: https://web.archive.org/web/20221214050908/https://cdn.discordapp.com/attachments/150412836500275200/513656427890475008/TIM20181118175603RGBnoiseLevel2.png
		//      from https://riichi.wiki/index.php?title=Mahjong_Soul&oldid=28198#Rules
		let game_type = GameType::Yonma;
		let doras = t![3s,].map(|t| t.indicates_dora(game_type));
		let round_wind = tw!(S);
		let seat_wind = tw!(E);
		let hand = make_hand!(R { minkou S S S } { minkou E E E } { minkou N N N } { minkan W W W W });
		let winning_tile_from = WinningTileFrom::Tsumo;
		let hand = hand.to_scorable_hand(t!(R)).unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkou E E E } { minkou S S S } { minkan W W W W } { minkou N N N } { R R }));
		let score = hand.score(
			&doras,
			round_wind,
			seat_wind,
			0,
			Riichi::NotRiichi,
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
}
