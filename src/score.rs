use crate::{
	DragonTile,
	GameType,
	Number, NumberTile,
	ScorableHand, ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair,
	Tile, TsumoOrRon,
	WindTile,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Riichi {
	NotRiichi,
	Riichi { ippatsu: bool, double: bool },
}

/// Indicates where the winning tile was drawn from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WinningTileFrom {
	/// The tile was drawn from the wall and was the last tile of the wall.
	Haitei,
	/// The tile was taken from another player's discard which was the last discard of the round.
	Houtei,
	/// The tile was drawn from the dead wall because the player called a kan or played a nukidora.
	Rinshan,
	/// The tile was taken from another player's shouminkan.
	Chankan,
	/// The tile was the first tile drawn on the player's turn, when the player is a dealer.
	Tenhou,
	/// The tile was the first tile drawn on the player's turn from the wall, when the player is not a dealer,
	/// and no previous player had called a tile until this player's turn.
	Chiihou,
	/// The tile was drawn from the wall and wasn't any of the above possibilities.
	Tsumo,
	/// The tile was taken from another player's discard and wasn't any of the above possibilities.
	Ron,
}

/// Broken down score for a [`ScorableHand`].
///
/// `Default` impl sets all fields to 0.
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct ScoreRaw {
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
pub struct Fu(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Han(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Yakuman(pub u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Score {
	pub fu: u32,
	pub han: u32,
	pub yakuman: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Points {
	FromEveryone { dealer: u32, non_dealer: u32 },
	FromRon(u32),
}

impl ScorableHand {
	/// - `dead_wall` is a list of tiles revealed in the dead wall, that will be used to calculate dora tiles.
	///   Eg if 1m was revealed in the dead wall, it should be provided in this list, and 2m will be considered a dora tile.
	///
	/// Returns `None` if the hand has no yaku.
	#[expect(clippy::bool_to_int_with_if)]
	pub fn score(
		&self,
		riichi: Riichi,
		winning_tile_from: WinningTileFrom,
		nukidora: u32,
		game_type: GameType,
		dead_wall: impl IntoIterator<Item = Tile>,
		prevailing_wind: WindTile,
		seat_wind: WindTile,
	) -> Option<ScoreRaw> {
		let mut score: ScoreRaw = Default::default();

		let tsumo_or_ron: TsumoOrRon = winning_tile_from.into();
		let is_menzen = self.is_menzen();

		match self {
			Self::Regular { melds: ([m1, m2, m3], m4), pair } => {
				score.base = Fu(20);

				let is_pinfu = self.is_pinfu(prevailing_wind, seat_wind);

				match tsumo_or_ron {
					// TODO: > In a few scoring variations, a win by rinshan kaihou is also ineligible for the +2 fu from tsumo.
					TsumoOrRon::Tsumo if !is_pinfu => score.win_condition = Fu(2),
					TsumoOrRon::Ron if is_menzen => score.win_condition = Fu(10),
					_ => (),
				}

				score.meld1 = Fu(m1.fu());
				score.meld2 = Fu(m2.fu());
				score.meld3 = Fu(m3.fu());
				score.meld4 = Fu(ScorableHandMeld::from(*m4).fu());
				score.pair = Fu(pair.fu(prevailing_wind, seat_wind));

				score.wait = Fu(match m4 {
					ScorableHandFourthMeld::Kanchan { .. } |
					ScorableHandFourthMeld::Penchan { .. } |
					ScorableHandFourthMeld::Tanki { .. } => 2,
					ScorableHandFourthMeld::RyanmenLeft { .. } |
					ScorableHandFourthMeld::RyanmenRight { .. } |
					ScorableHandFourthMeld::Shanpon { .. } => 0,
				});

				score.open_pinfu = Fu(if !is_menzen && Score::from(score).fu == 20 { 2 } else { 0 });

				score.mentsumo = Han(if is_menzen && matches!(tsumo_or_ron, TsumoOrRon::Tsumo) { 1 } else { 0 });

				if let Riichi::Riichi { double, ippatsu } = riichi {
					score.riichi = Han(if double { 2 } else { 1 });
					score.ippatsu = Han(if ippatsu { 1 } else { 0 });
				}

				score.pinfu = Han(if is_pinfu { 1 } else { 0 });
				score.iipeikou = Han(if self.is_iipeikou() { 1 } else { 0 });
				score.haitei = Han(if matches!(winning_tile_from, WinningTileFrom::Haitei) { 1 } else { 0 });
				score.houtei = Han(if matches!(winning_tile_from, WinningTileFrom::Houtei) { 1 } else { 0 });
				score.rinshan = Han(if matches!(winning_tile_from, WinningTileFrom::Rinshan) { 1 } else { 0 });
				score.chankan = Han(if matches!(winning_tile_from, WinningTileFrom::Chankan) { 1 } else { 0 });
				score.tanyao = Han(if self.is_tanyao() { 1 } else { 0 });
				score.yakuhai_ton = Han(self.num_wind_yakuhai(WindTile::Ton, prevailing_wind, seat_wind));
				score.yakuhai_nan = Han(self.num_wind_yakuhai(WindTile::Nan, prevailing_wind, seat_wind));
				score.yakuhai_shaa = Han(self.num_wind_yakuhai(WindTile::Shaa, prevailing_wind, seat_wind));
				score.yakuhai_pei = Han(self.num_wind_yakuhai(WindTile::Pei, prevailing_wind, seat_wind));
				score.yakuhai_haku = Han(if self.is_dragon_yakuhai(DragonTile::Haku) { 1 } else { 0 });
				score.yakuhai_hatsu = Han(if self.is_dragon_yakuhai(DragonTile::Hatsu) { 1 } else { 0 });
				score.yakuhai_chun = Han(if self.is_dragon_yakuhai(DragonTile::Chun) { 1 } else { 0 });

				score.chanta = Han(if self.is_chanta() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.sanshoku_doujun = Han(if self.is_sanshoku_doujun() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.ittsuu = Han(if self.is_ittsuu() { if is_menzen { 2 } else { 1 } } else { 0 });
				score.toitoi = Han(if self.is_toitoi() { 2 } else { 0 });
				score.sanankou = Han(if self.is_sanankou() { 2 } else { 0 });
				score.sanshoku_doukou = Han(if self.is_sanshoku_doukou() { 2 } else { 0 });
				score.sankantsu = Han(if self.is_sankantsu() { 2 } else { 0 });
				score.honroutou = Han(if self.is_honroutou() { 2 } else { 0 });
				score.shousangen = Han(if self.is_shousangen() { 2 } else { 0 });

				score.honitsu = Han(if self.is_honitsu() { if is_menzen { 3 } else { 2 } } else { 0 });
				score.junchan = Han(if self.is_junchan() { if is_menzen { 3 } else { 2 } } else { 0 });
				score.ryanpeikou = Han(if self.is_ryanpeikou() { 3 } else { 0 });

				score.chinitsu = Han(if self.is_chinitsu() { if is_menzen { 6 } else { 5 } } else { 0 });
			},

			Self::Chiitoi(_) => {
				score.base = Fu(25);

				score.mentsumo = Han(if is_menzen && matches!(tsumo_or_ron, TsumoOrRon::Tsumo) { 1 } else { 0 });

				score.tanyao = Han(if self.is_tanyao() { 1 } else { 0 });

				if let Riichi::Riichi { double, ippatsu } = riichi {
					score.riichi = Han(if double { 2 } else { 1 });
					score.ippatsu = Han(if ippatsu { 1 } else { 0 });
				}

				score.haitei = Han(if matches!(winning_tile_from, WinningTileFrom::Haitei) { 1 } else { 0 });
				score.houtei = Han(if matches!(winning_tile_from, WinningTileFrom::Houtei) { 1 } else { 0 });

				score.chiitoi = Han(2);

				score.honroutou = Han(if self.is_honroutou() { 2 } else { 0 });

				score.honitsu = Han(if self.is_honitsu() { if is_menzen { 3 } else { 2 } } else { 0 });

				score.chinitsu = Han(if self.is_chinitsu() { if is_menzen { 6 } else { 5 } } else { 0 });
			},

			Self::KokushiMusou { was_juusanmen_wait, .. } => {
				score.kokushi_musou = Yakuman(if *was_juusanmen_wait { 2 } else { 1 });
			},
		}

		let han = Score::from(score).han;

		let dora = {
			let doras: Vec<_> = dead_wall.into_iter().map(|t| t.indicates_dora(game_type)).collect();
			self.into_iter().map(|tile| dora_match(&doras, tile)).sum::<u32>() +
			(0..nukidora).map(|_| dora_match(&doras, t!(N))).sum::<u32>()
		};
		score.dora = Han(dora);
		score.nukidora = Han(nukidora);

		score.suuankou = Yakuman(self.num_suuankou());
		score.daisangen = Yakuman(if self.is_daisangen() { 1 } else { 0 });
		score.shousuushii = Yakuman(if self.is_shousuushii() { 1 } else { 0 });
		score.daisuushii = Yakuman(if self.is_daisuushii() { 2 } else { 0 });
		score.tsuuiisou = Yakuman(if self.is_tsuuiisou() { 1 } else { 0 });
		score.chinroutou = Yakuman(if self.is_chinroutou() { 1 } else { 0 });
		score.ryuuiisou = Yakuman(if self.is_ryuuiisou() { 1 } else { 0 });
		score.chuuren_poutou = Yakuman(self.num_chuuren_poutou());
		score.suukantsu = Yakuman(if self.is_suukantsu() { 1 } else { 0 });
		score.tenhou = Yakuman(if matches!(winning_tile_from, WinningTileFrom::Tenhou) { 1 } else { 0 });
		score.chiihou = Yakuman(if matches!(winning_tile_from, WinningTileFrom::Chiihou) { 1 } else { 0 });

		if han == 0 && Score::from(score).yakuman == 0 {
			// No han and no yakuman => no yaku => cannot score.
			// Note that even 13+ dora cannot create kazoe yakuman by themselves, so we only want to consider non-dora han here.
			return None;
		}

		score.kazoe_yakuman = Yakuman(if han + dora + nukidora >= 13 { 1 } else { 0 });

		Some(score)
	}
}

impl ScorableHandMeld {
	const fn fu(self) -> u32 {
		match self {
			Self::Anjun(_) |
			Self::Minjun(_) => 0,
			Self::Ankou([t, ..]) => 4 << (!t.is_simple() as u8),
			Self::Minkou([t, ..]) => 2 << (!t.is_simple() as u8),
			Self::Ankan([t, ..]) => 16 << (!t.is_simple() as u8),
			Self::Minkan([t, ..]) => 8 << (!t.is_simple() as u8),
		}
	}
}

impl ScorableHandPair {
	fn fu(self, prevailing_wind: WindTile, seat_wind: WindTile) -> u32 {
		self.num_yakuhai(prevailing_wind, seat_wind) * 2
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
			WinningTileFrom::Houtei |
			WinningTileFrom::Chankan |
			WinningTileFrom::Ron => Self::Ron,
		}
	}
}

impl std::fmt::Debug for ScoreRaw {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut f = f.debug_struct("ScoreRaw");
		if self.base.0 > 0 { f.field("base", &self.base); }
		if self.win_condition.0 > 0 { f.field("win_condition", &self.win_condition); }
		if self.meld1.0 > 0 { f.field("meld1", &self.meld1); }
		if self.meld2.0 > 0 { f.field("meld2", &self.meld2); }
		if self.meld3.0 > 0 { f.field("meld3", &self.meld3); }
		if self.meld4.0 > 0 { f.field("meld4", &self.meld4); }
		if self.pair.0 > 0 { f.field("pair", &self.pair); }
		if self.wait.0 > 0 { f.field("wait", &self.wait); }
		if self.open_pinfu.0 > 0 { f.field("open_pinfu", &self.open_pinfu); }
		if self.mentsumo.0 > 0 { f.field("mentsumo", &self.mentsumo); }
		if self.riichi.0 > 0 { f.field("riichi", &self.riichi); }
		if self.ippatsu.0 > 0 { f.field("ippatsu", &self.ippatsu); }
		if self.pinfu.0 > 0 { f.field("pinfu", &self.pinfu); }
		if self.iipeikou.0 > 0 { f.field("iipeikou", &self.iipeikou); }
		if self.haitei.0 > 0 { f.field("haitei", &self.haitei); }
		if self.houtei.0 > 0 { f.field("houtei", &self.houtei); }
		if self.rinshan.0 > 0 { f.field("rinshan", &self.rinshan); }
		if self.chankan.0 > 0 { f.field("chankan", &self.chankan); }
		if self.tanyao.0 > 0 { f.field("tanyao", &self.tanyao); }
		if self.yakuhai_ton.0 > 0 { f.field("yakuhai_ton", &self.yakuhai_ton); }
		if self.yakuhai_nan.0 > 0 { f.field("yakuhai_nan", &self.yakuhai_nan); }
		if self.yakuhai_shaa.0 > 0 { f.field("yakuhai_shaa", &self.yakuhai_shaa); }
		if self.yakuhai_pei.0 > 0 { f.field("yakuhai_pei", &self.yakuhai_pei); }
		if self.yakuhai_haku.0 > 0 { f.field("yakuhai_haku", &self.yakuhai_haku); }
		if self.yakuhai_hatsu.0 > 0 { f.field("yakuhai_hatsu", &self.yakuhai_hatsu); }
		if self.yakuhai_chun.0 > 0 { f.field("yakuhai_chun", &self.yakuhai_chun); }
		if self.chanta.0 > 0 { f.field("chanta", &self.chanta); }
		if self.sanshoku_doujun.0 > 0 { f.field("sanshoku_doujun", &self.sanshoku_doujun); }
		if self.ittsuu.0 > 0 { f.field("ittsuu", &self.ittsuu); }
		if self.toitoi.0 > 0 { f.field("toitoi", &self.toitoi); }
		if self.sanankou.0 > 0 { f.field("sanankou", &self.sanankou); }
		if self.sanshoku_doukou.0 > 0 { f.field("sanshoku_doukou", &self.sanshoku_doukou); }
		if self.sankantsu.0 > 0 { f.field("sankantsu", &self.sankantsu); }
		if self.chiitoi.0 > 0 { f.field("chiitoi", &self.chiitoi); }
		if self.honroutou.0 > 0 { f.field("honroutou", &self.honroutou); }
		if self.shousangen.0 > 0 { f.field("shousangen", &self.shousangen); }
		if self.honitsu.0 > 0 { f.field("honitsu", &self.honitsu); }
		if self.junchan.0 > 0 { f.field("junchan", &self.junchan); }
		if self.ryanpeikou.0 > 0 { f.field("ryanpeikou", &self.ryanpeikou); }
		if self.chinitsu.0 > 0 { f.field("chinitsu", &self.chinitsu); }
		if self.dora.0 > 0 { f.field("dora", &self.dora); }
		if self.nukidora.0 > 0 { f.field("nukidora", &self.nukidora); }
		if self.kazoe_yakuman.0 > 0 { f.field("kazoe_yakuman", &self.kazoe_yakuman); }
		if self.kokushi_musou.0 > 0 { f.field("kokushi_musou", &self.kokushi_musou); }
		if self.suuankou.0 > 0 { f.field("suuankou", &self.suuankou); }
		if self.daisangen.0 > 0 { f.field("daisangen", &self.daisangen); }
		if self.shousuushii.0 > 0 { f.field("shousuushii", &self.shousuushii); }
		if self.daisuushii.0 > 0 { f.field("daisuushii", &self.daisuushii); }
		if self.tsuuiisou.0 > 0 { f.field("tsuuiisou", &self.tsuuiisou); }
		if self.chinroutou.0 > 0 { f.field("chinroutou", &self.chinroutou); }
		if self.ryuuiisou.0 > 0 { f.field("ryuuiisou", &self.ryuuiisou); }
		if self.chuuren_poutou.0 > 0 { f.field("chuuren_poutou", &self.chuuren_poutou); }
		if self.suukantsu.0 > 0 { f.field("suukantsu", &self.suukantsu); }
		if self.tenhou.0 > 0 { f.field("tenhou", &self.tenhou); }
		if self.chiihou.0 > 0 { f.field("chiihou", &self.chiihou); }
		f.finish()
	}
}

impl Score {
	/// - `is_dealer` is `true` if the player was dealer for the round, `false` otherwise.
	pub fn score(
		self,
		is_dealer: bool,
		tsumo_or_ron: TsumoOrRon,
	) -> Points {
		let basic_points = match self.yakuman {
			0 => match self.han {
				0..=5 => (self.fu << (self.han + 2)).min(2000),
				// haneman
				6..=7 => 3000,
				// baiman
				8..=10 => 4000,
				// sanbaiman
				11..=12 => 6000,
				// kazoe yakuman
				13.. => 8000,
			},
			yakuman => yakuman * 8000,
		};
		match (is_dealer, tsumo_or_ron) {
			// 2x from non-dealers
			(true, TsumoOrRon::Tsumo) => Points::FromEveryone { dealer: 0, non_dealer: (basic_points * 2).next_multiple_of(100) },
			// 6x from ron'd player
			(true, TsumoOrRon::Ron) => Points::FromRon((basic_points * 6).next_multiple_of(100)),
			// 2x from dealer, 1x from other non-dealers
			(false, TsumoOrRon::Tsumo) => Points::FromEveryone { dealer: (basic_points * 2).next_multiple_of(100), non_dealer: basic_points.next_multiple_of(100) },
			// 4x from ron'd player
			(false, TsumoOrRon::Ron) => Points::FromRon((basic_points * 4).next_multiple_of(100)),
		}
	}
}

impl std::ops::Add for Fu {
	type Output = Self;

	fn add(self, other: Self) -> Self::Output {
		Self(self.0 + other.0)
	}
}

impl std::ops::Add for Han {
	type Output = Self;

	fn add(self, other: Self) -> Self::Output {
		Self(self.0 + other.0)
	}
}

impl std::ops::Add for Yakuman {
	type Output = Self;

	fn add(self, other: Self) -> Self::Output {
		Self(self.0 + other.0)
	}
}

impl From<ScoreRaw> for Score {
	fn from(score: ScoreRaw) -> Self {
		let ScoreRaw {
			base,
			win_condition,
			meld1,
			meld2,
			meld3,
			meld4,
			pair,
			wait,
			open_pinfu,

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

		let Fu(mut fu) =
			base +
			win_condition +
			meld1 +
			meld2 +
			meld3 +
			meld4 +
			pair +
			wait +
			open_pinfu;
		if chiitoi == Han(0) {
			fu = fu.next_multiple_of(10);
		}

		let Han(han) =
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

		let Yakuman(yakuman) =
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
	/// - `is_dealer` is `true` if the player was dealer for the round, `false` otherwise.
	// TODO: Also take args for extra tenbou and honba instead of making caller calculate them?
	pub const fn total(self, is_dealer: bool, game_type: GameType) -> u32 {
		match self {
			Self::FromEveryone { dealer, non_dealer } =>
				if is_dealer {
					let num_non_dealers = match game_type {
						GameType::FourPlayer => 3,
						GameType::ThreePlayer => 2,
					};
					non_dealer * num_non_dealers
				}
				else {
					let num_non_dealers = match game_type {
						GameType::FourPlayer => 2,
						GameType::ThreePlayer => 1,
					};
					dealer + non_dealer * num_non_dealers
				},

			Self::FromRon(points) => points,
		}
	}
}

fn dora_match(doras: &[Tile], tile: Tile) -> u32 {
	let result =
		usize::from(matches!(NumberTile::try_from(tile), Ok(t) if matches!(t.number(), Number::FiveRed))) +
		doras.iter().filter(|&&d| tile == d).count();
	result.try_into().unwrap()
}

#[cfg(test)]
mod tests {
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
		let score = Score { fu: 30, han: 1, yakuman: 0 };
		let points = score.score(false, TsumoOrRon::Ron);
		assert_eq!(points, Points::FromRon(960_u32.next_multiple_of(100)));
		assert_eq!(points.total(false, GameType::FourPlayer), 960_u32.next_multiple_of(100));

		let score = Score { fu: 30, han: 1, yakuman: 0 };
		let points = score.score(false, TsumoOrRon::Tsumo);
		assert_eq!(points, Points::FromEveryone { dealer: 480_u32.next_multiple_of(100), non_dealer: 240_u32.next_multiple_of(100) });
		assert_eq!(points.total(false, GameType::FourPlayer), 240_u32.next_multiple_of(100) + 240_u32.next_multiple_of(100) + 480_u32.next_multiple_of(100));
	}

	#[test]
	fn score_example1() {
		// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175 "Example 1"

		let hand = make_hand!(1s 2s 3s 5s 6s 9s 9s { minkou R R R } { minjun 1s 2s 3s });
		let winning_tile_from = WinningTileFrom::Ron;
		let mut hands = hand.to_scorable_hands(t!(4s), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 1s 2s 3s } { minkou R R R } { minjun 1s 2s 3s } { minjun 4s 5s 6s ryanmen_left } { 9s 9s }));

		let game_type = GameType::FourPlayer;
		let prevalent_wind = tw!(E);
		let seat_wind = tw!(S);
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			0,
			game_type,
			[],
			prevalent_wind,
			seat_wind,
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(20),
			meld3: Fu(4), // { minkou R R R }
			yakuhai_chun: Han(1),
			honitsu: Han(2),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: u32::next_multiple_of(20 + 4, 10), han: 2 + 1, yakuman: 0 },
		);

		let is_dealer = seat_wind == tw!(E);
		assert_eq!(score.score(is_dealer, winning_tile_from.into()).total(is_dealer, game_type), 3900);
	}

	#[test]
	fn score_example2() {
		// Ref: https://riichi.wiki/index.php?title=Japanese_mahjong_scoring_rules&oldid=28175 "Example 2"

		let hand = make_hand!(6p 6p 7p 7p 8p 9s 9s 9s G G { ankan 1m 1m 1m 1m });
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands = hand.to_scorable_hands(t!(8p), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 6p 7p 8p } { ankou 9s 9s 9s } { ankan 1m 1m 1m 1m } { anjun 6p 7p 8p ryanmen_right } { G G }));

		let game_type = GameType::FourPlayer;
		let prevalent_wind = tw!(E);
		let seat_wind = tw!(S);
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			0,
			game_type,
			[],
			prevalent_wind,
			seat_wind,
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(20),
			win_condition: Fu(2),
			meld1: Fu(32), // { ankan 1m 1m 1m 1m }
			meld3: Fu(8), // { ankou 9s 9s 9s }
			pair: Fu(2),
			mentsumo: Han(1),
			iipeikou: Han(1),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: u32::next_multiple_of(20 + 32 + 8 + 2 + 2, 10), han: 1 + 1, yakuman: 0 },
		);

		let is_dealer = seat_wind == tw!(E);
		assert_eq!(
			score.score(is_dealer, winning_tile_from.into()).total(is_dealer, game_type),
			2240_u32.next_multiple_of(100) + 2 * 1120_u32.next_multiple_of(100),
		);
	}

	#[test]
	fn sankantsu() {
		// Ref: https://riichi.wiki/index.php?title=Sankantsu&oldid=27944

		let hand = make_hand!(2p 3p 9p 9p { minkan 2m 2m 2m 2m } { minkan 3m 3m 3m 3m } { minkan 4m 4m 4m 4m });
		let winning_tile_from = WinningTileFrom::Ron;
		let mut hands = hand.to_scorable_hands(t!(4p), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ minkan 2m 2m 2m 2m } { minkan 3m 3m 3m 3m } { minkan 4m 4m 4m 4m } { minjun 2p 3p 4p ryanmen_right } { 9p 9p }));

		let game_type = GameType::FourPlayer;
		let prevalent_wind = tw!(E);
		let seat_wind = tw!(S);
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			0,
			game_type,
			[],
			prevalent_wind,
			seat_wind,
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(20),
			meld1: Fu(8), // { minkan 2m 2m 2m 2m }
			meld2: Fu(8), // { minkan 3m 3m 3m 3m }
			meld3: Fu(8), // { minkan 4m 4m 4m 4m }
			sankantsu: Han(2),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: u32::next_multiple_of(20 + 8 + 8 + 8, 10), han: 2, yakuman: 0 },
		);

		let is_dealer = seat_wind == tw!(E);
		assert_eq!(
			score.score(is_dealer, winning_tile_from.into()).total(is_dealer, game_type),
			3200,
		);
	}

	#[test]
	fn honroutou() {
		// Ref: https://riichi.wiki/index.php?title=Honroutou&oldid=25727

		let hand = make_hand!(1p 1p 9s 9s { minkou 9m 9m 9m } { minkou N N N } { minkou W W W });
		let winning_tile_from = WinningTileFrom::Ron;
		let hands: Vec<_> = t![1p, 9s].into_iter().flat_map(|new_tile| {
			let hands = hand.to_scorable_hands(new_tile, winning_tile_from.into());
			assert_eq!(hands.len(), 1);
			hands
		}).collect();
		assert_eq!(hands[0], make_scorable_hand!({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { minkou 1p 1p 1p shanpon } { 9s 9s }));
		assert_eq!(hands[1], make_scorable_hand!({ minkou 9m 9m 9m } { minkou N N N } { minkou W W W } { minkou 9s 9s 9s shanpon } { 1p 1p }));
		for hand in hands {
			let game_type = GameType::FourPlayer;
			let score = hand.score(
				Riichi::NotRiichi,
				winning_tile_from,
				0,
				game_type,
				[],
				tw!(E),
				tw!(E),
			).unwrap();
			assert_eq!(score, ScoreRaw {
				base: Fu(20),
				meld1: Fu(4), // { minkou 9m 9m 9m }
				meld2: Fu(4), // { minkou W W W }
				meld3: Fu(4), // { minkou N N N }
				meld4: Fu(4), // { minkou 1p 1p 1p }
				toitoi: Han(2),
				honroutou: Han(2),
				..Default::default()
			});

			let score: Score = score.into();
			assert_eq!(
				score,
				Score { fu: u32::next_multiple_of(20 + 4 + 4 + 4 + 4, 10), han: 2 + 2, yakuman: 0 },
			);
		}

		let hand = make_hand!(9m 9m 1p 1p 1s 1s 9s 9s S S W W N);
		let winning_tile_from = WinningTileFrom::Ron;
		let mut hands = hand.to_scorable_hands(t!(N), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ 9m 9m } { 1p 1p } { 1s 1s } { 9s 9s } { S S } { W W } { N N }));
		let game_type = GameType::FourPlayer;
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			0,
			game_type,
			[],
			tw!(E),
			tw!(E),
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(25),
			chiitoi: Han(2),
			honroutou: Han(2),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: 25, han: 2 + 2, yakuman: 0 },
		);
	}

	#[test]
	fn shousangen() {
		// Ref: https://riichi.wiki/index.php?title=Shousangen&oldid=27371

		let hand = make_hand!(2p 3p 4p 3s 4s G G { minkou Wh Wh Wh } { minkou R R R });
		let winning_tile_from = WinningTileFrom::Ron;
		let mut hands = hand.to_scorable_hands(t!(5s), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 2p 3p 4p } { minkou Wh Wh Wh } { minkou R R R } { minjun 3s 4s 5s ryanmen_right } { G G }));

		let game_type = GameType::FourPlayer;
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			0,
			game_type,
			[],
			tw!(E),
			tw!(E),
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(20),
			meld2: Fu(4), // { minkou Wh Wh Wh }
			meld3: Fu(4), // { minkou R R R }
			pair: Fu(2),
			yakuhai_haku: Han(1),
			yakuhai_chun: Han(1),
			shousangen: Han(2),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: u32::next_multiple_of(20 + 4 + 4 + 2, 10), han: 1 + 1 + 2, yakuman: 0 },
		);

		let hand = make_hand!(5m 6m 7m 1s 2s 3s G G R R { minkou Wh Wh Wh });
		let winning_tile_from = WinningTileFrom::Ron;
		let mut hands = hand.to_scorable_hands(t!(G), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 5m 6m 7m } { anjun 1s 2s 3s } { minkou Wh Wh Wh } { minkou G G G shanpon } { R R }));

		let game_type = GameType::FourPlayer;
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			0,
			game_type,
			[],
			tw!(E),
			tw!(E),
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(20),
			meld3: Fu(4), // { minkou Wh Wh Wh }
			meld4: Fu(4), // { minkou G G G }
			pair: Fu(2),
			yakuhai_haku: Han(1),
			yakuhai_hatsu: Han(1),
			shousangen: Han(2),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: u32::next_multiple_of(20 + 4 + 4 + 2, 10), han: 1 + 1 + 2, yakuman: 0 },
		);
	}

	#[test]
	fn kazoe_yakuman() {
		// Ref: https://old.reddit.com/r/Mahjong/comments/ceotnt/kazoe_yakuman_with_only_yakuhai_and_12_dora/

		let hand = make_hand!(6p 7p 8p 9s 9s S S { minkou 4p 4p 4p } { minkan 3s 3s 3s 3s });
		let winning_tile_from = WinningTileFrom::Tsumo;
		let mut hands = hand.to_scorable_hands(t!(S), winning_tile_from.into());
		assert_eq!(hands.len(), 1);
		let hand = hands.pop_first().unwrap();
		assert_eq!(hand, make_scorable_hand!({ anjun 6p 7p 8p } { minkou 4p 4p 4p } { minkan 3s 3s 3s 3s } { ankou S S S shanpon } { 9s 9s }));

		let game_type = GameType::ThreePlayer;
		let prevalent_wind = tw!(S);
		// Seat wind is not visible in the screenshot, but based on the score it's the dealer wind (E).
		let seat_wind = tw!(E);
		let score = hand.score(
			Riichi::NotRiichi,
			winning_tile_from,
			4,
			game_type,
			t![W, 1s, 2s, S],
			prevalent_wind,
			seat_wind,
		).unwrap();
		assert_eq!(score, ScoreRaw {
			base: Fu(20),
			win_condition: Fu(2),
			meld1: Fu(2), // { minkou 4p 4p 4p }
			meld3: Fu(8), // { minkan 3s 3s 3s 3s }
			meld4: Fu(8), // { ankou S S S }
			yakuhai_nan: Han(1),
			dora: Han(8), // 3333s NNNN
			nukidora: Han(4),
			kazoe_yakuman: Yakuman(1),
			..Default::default()
		});

		let score: Score = score.into();
		assert_eq!(
			score,
			Score { fu: u32::next_multiple_of(20 + 2 + 2 + 8 + 8, 10), han: 13, yakuman: 1 },
		);

		let is_dealer = seat_wind == tw!(E);
		assert_eq!(
			score.score(is_dealer, winning_tile_from.into()).total(is_dealer, game_type),
			32000,
		);
	}
}
