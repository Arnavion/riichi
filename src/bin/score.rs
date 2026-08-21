use riichi::{
	GameType,
	generic_array::typenum::U,
	Hand, HandStable,
	Riichi, Rules,
	ScorableHand, Score, ScoreAggregate, SeatRelative,
	Tile, Tile34MultiSet, Tile37MultiSet,
	WindTile, WinningTileFrom,
	tw,
};

fn main() {
	let mut args = std::env::args();
	let arg0 = args.next().unwrap();

	if main_inner(&mut std::io::stdout().lock(), &arg0, args).is_err() {
		print_help(&mut std::io::stderr().lock(), &arg0);
		std::process::exit(1);
	}
}

fn main_inner(stdout: &mut impl std::io::Write, arg0: &str, mut args: impl Iterator<Item = String>) -> Result<(), ()> {
	let mut game_type = GameType::Yonma;
	let mut nukidora = 0;
	let Some(mut arg) = args.next() else {
		eprintln!("could not parse GAME_TYPE / ROUND_WIND");
		return Err(());
	};
	match &*arg {
		"--help" => {
			print_help(stdout, arg0);
			std::process::exit(0);
		},
		"sanma-0" => {
			game_type = GameType::Sanma;
			nukidora = 0;
			arg = if let Some(arg) = args.next() { arg } else {
				eprintln!("could not parse ROUND_WIND");
				return Err(());
			};
		},
		"sanma-1" => {
			game_type = GameType::Sanma;
			nukidora = 1;
			arg = if let Some(arg) = args.next() { arg } else {
				eprintln!("could not parse ROUND_WIND");
				return Err(());
			};
		},
		"sanma-2" => {
			game_type = GameType::Sanma;
			nukidora = 2;
			arg = if let Some(arg) = args.next() { arg } else {
				eprintln!("could not parse ROUND_WIND");
				return Err(());
			};
		},
		"sanma-3" => {
			game_type = GameType::Sanma;
			nukidora = 3;
			arg = if let Some(arg) = args.next() { arg } else {
				eprintln!("could not parse ROUND_WIND");
				return Err(());
			};
		},
		"sanma-4" => {
			game_type = GameType::Sanma;
			nukidora = 4;
			arg = if let Some(arg) = args.next() { arg } else {
				eprintln!("could not parse ROUND_WIND");
				return Err(());
			};
		},
		_ => (),
	}

	let rules = Default::default();

	let inventory = match game_type {
		GameType::Yonma => Tile37MultiSet::INVENTORY_YONMA_111,
		GameType::Sanma => Tile37MultiSet::INVENTORY_SANMA_011,
	};

	let Ok(round_wind) = arg.parse() else {
		eprintln!("could not parse ROUND_WIND");
		return Err(());
	};

	let Some(seat_wind) = args.next() else {
		eprintln!("could not parse SEAT_WIND");
		return Err(());
	};
	let Ok(seat_wind) = seat_wind.parse() else {
		eprintln!("could not parse SEAT_WIND");
		return Err(());
	};

	let Some(dead_wall) = args.next() else {
		eprintln!("could not parse DEAD_WALL");
		return Err(());
	};
	let Ok((dead_wall, dead_wall_type, _)) = Tile::parse_run_until::<U<10>>(dead_wall.as_ref(), None) else {
		eprintln!("could not parse DEAD_WALL");
		return Err(());
	};
	if dead_wall_type.is_some() {
		eprintln!("could not parse DEAD_WALL");
		return Err(());
	}
	let dead_wall: Tile34MultiSet = dead_wall.into_iter().map(|t| (t, 1)).collect();
	let doras = dead_wall.indicates_dora(game_type);

	let Some(hand) = args.next() else {
		eprintln!("could not parse HAND");
		return Err(());
	};

	let mut riichi = Riichi::NotRiichi;
	let Some(mut arg) = args.next() else {
		eprintln!("could not parse RIICHI / WINNING_TILE_FROM");
		return Err(());
	};
	if arg == "riichi" {
		riichi = Riichi::Riichi { ippatsu: false, double: false };
		arg = if let Some(arg) = args.next() { arg } else {
			eprintln!("could not parse WINNING_TILE_FROM");
			return Err(());
		};
	}
	else if arg == "riichi-ippatsu" {
		riichi = Riichi::Riichi { ippatsu: true, double: false };
		arg = if let Some(arg) = args.next() { arg } else {
			eprintln!("could not parse WINNING_TILE_FROM");
			return Err(());
		};
	}
	else if arg == "double-riichi" {
		riichi = Riichi::Riichi { ippatsu: false, double: true };
		arg = if let Some(arg) = args.next() { arg } else {
			eprintln!("could not parse WINNING_TILE_FROM");
			return Err(());
		};
	}
	else if arg == "double-riichi-ippatsu" {
		riichi = Riichi::Riichi { ippatsu: true, double: true };
		arg = if let Some(arg) = args.next() { arg } else {
			eprintln!("could not parse WINNING_TILE_FROM");
			return Err(());
		};
	}

	let default_ron_seat = match seat_wind {
		tw!(E | S | N) => SeatRelative::Shimocha,
		tw!(W) => match game_type {
			GameType::Yonma => SeatRelative::Shimocha,
			GameType::Sanma => SeatRelative::Toimen,
		},
	};
	let winning_tile_from = match &*arg {
		"haitei" => WinningTileFrom::Haitei,
		"rinshan" => WinningTileFrom::Rinshan,
		"tenhou" => WinningTileFrom::Tenhou,
		"chiihou" => WinningTileFrom::Chiihou,
		"tsumo" => WinningTileFrom::Tsumo,

		"houtei" => WinningTileFrom::Houtei(default_ron_seat),
		"houtei-shimocha" => WinningTileFrom::Houtei(SeatRelative::Shimocha),
		"houtei-toimen" => WinningTileFrom::Houtei(SeatRelative::Toimen),
		"houtei-kamicha" => WinningTileFrom::Houtei(SeatRelative::Kamicha),

		"chankan" => WinningTileFrom::ChankanShouminkan(default_ron_seat),
		"chankan-shimocha" => WinningTileFrom::ChankanShouminkan(SeatRelative::Shimocha),
		"chankan-toimen" => WinningTileFrom::ChankanShouminkan(SeatRelative::Toimen),
		"chankan-kamicha" => WinningTileFrom::ChankanShouminkan(SeatRelative::Kamicha),

		"chankan-ankan" => WinningTileFrom::ChankanAnkan(default_ron_seat),
		"chankan-ankan-shimocha" => WinningTileFrom::ChankanAnkan(SeatRelative::Shimocha),
		"chankan-ankan-toimen" => WinningTileFrom::ChankanAnkan(SeatRelative::Toimen),
		"chankan-ankan-kamicha" => WinningTileFrom::ChankanAnkan(SeatRelative::Kamicha),

		"kanburi" => WinningTileFrom::Kanburi { seat: default_ron_seat, tsubame_gaeshi: false },
		"kanburi-shimocha" => WinningTileFrom::Kanburi { seat: SeatRelative::Shimocha, tsubame_gaeshi: false },
		"kanburi-toimen" => WinningTileFrom::Kanburi { seat: SeatRelative::Toimen, tsubame_gaeshi: false },
		"kanburi-kamicha" => WinningTileFrom::Kanburi { seat: SeatRelative::Kamicha, tsubame_gaeshi: false },

		"renhou" => WinningTileFrom::Renhou { seat: default_ron_seat, tsubame_gaeshi: false },
		"renhou-shimocha" => WinningTileFrom::Renhou { seat: SeatRelative::Shimocha, tsubame_gaeshi: false },
		"renhou-toimen" => WinningTileFrom::Renhou { seat: SeatRelative::Toimen, tsubame_gaeshi: false },
		"renhou-kamicha" => WinningTileFrom::Renhou { seat: SeatRelative::Kamicha, tsubame_gaeshi: false },

		"ron" => WinningTileFrom::Ron { seat: default_ron_seat, tsubame_gaeshi: false },
		"ron-shimocha" => WinningTileFrom::Ron { seat: SeatRelative::Shimocha, tsubame_gaeshi: false },
		"ron-toimen" => WinningTileFrom::Ron { seat: SeatRelative::Toimen, tsubame_gaeshi: false },
		"ron-kamicha" => WinningTileFrom::Ron { seat: SeatRelative::Kamicha, tsubame_gaeshi: false },
		_ => {
			eprintln!("could not parse WINNING_TILE_FROM");
			return Err(());
		},
	};

	if !matches!(riichi, Riichi::NotRiichi) {
		match winning_tile_from {
			WinningTileFrom::Tenhou => {
				eprintln!("tenhou hand cannot have riichi");
				return Err(());
			},
			WinningTileFrom::Chiihou => {
				eprintln!("chiihou hand cannot have riichi");
				return Err(());
			},
			WinningTileFrom::Renhou { .. } => {
				eprintln!("renhou hand cannot have riichi");
				return Err(());
			},
			_ => (),
		}
	}

	if let WinningTileFrom::Tenhou = winning_tile_from && let Ok(hand) = hand.parse::<Hand<U<14>, U<0>>>() {
		if let Some(_winning_tile) = args.next() {
			eprintln!("WINNING_TILE cannot be specified with 14-tile tenhou hand");
			return Err(());
		}

		if !hand.0.as_ref().is_subset_of(&inventory) {
			eprintln!("HAND is not a subset of tile inventory");
			return Err(());
		}

		print_best_tenhou_hand(stdout, game_type, &rules, &doras, round_wind, seat_wind, nukidora, riichi, winning_tile_from, hand);
	}
	else {
		let Ok(hand) = hand.parse::<HandStable>() else {
			eprintln!("could not parse HAND");
			return Err(());
		};
		if !hand.tiles().is_subset_of(&inventory) {
			eprintln!("HAND is not a subset of tile inventory");
			return Err(());
		}

		let other_waits = if let Some(winning_tile) = args.next() {
			let Ok(winning_tile) = winning_tile.parse() else {
				eprintln!("could not parse WINNING_TILE");
				return Err(());
			};

			print_best_non_tenhou_hand(stdout, game_type, &rules, &doras, round_wind, seat_wind, nukidora, riichi, winning_tile, winning_tile_from, hand.clone());

			let mut other_waits = hand.clone().tenpai(&inventory);
			other_waits.remove(winning_tile);
			if other_waits.is_empty() {
				return Ok(());
			}
			_ = writeln!(stdout);
			_ = writeln!(stdout, "Other waits:");
			_ = writeln!(stdout);
			other_waits
		}
		else {
			let waits = hand.clone().tenpai(&inventory);
			if waits.is_empty() {
				_ = writeln!(stdout, "No yaku");
				return Ok(());
			}
			_ = writeln!(stdout, "Waits:");
			_ = writeln!(stdout);
			waits
		};
		for winning_tile in other_waits {
			_ = writeln!(stdout, "+ {winning_tile}");

			print_best_non_tenhou_hand(stdout, game_type, &rules, &doras, round_wind, seat_wind, nukidora, riichi, winning_tile, winning_tile_from, hand.clone());

			_ = writeln!(stdout);
		}
	}

	Ok(())
}

fn print_help(w: &mut impl std::io::Write, arg0: &str) {
	_ = write!(w, "\
Calculates the score of the given hand.

Usage: {arg0} [GAME_TYPE] <ROUND_WIND> <SEAT_WIND> <DEAD_WALL> <HAND> [RIICHI] <WINNING_TILE_FROM> [WINNING_TILE]

    GAME_TYPE: If set to sanma-N, indicates three-player, otherwise default is four-player. N is the number of peidora, 0 to 4 inclusive.
    HAND: Specified in MPSZ format, extended to support notating minjuns / minkous / ankans / minkans. Ref: https://github.com/Arnavion/riichi/blob/main/extended-mpsz.md
    DEAD_WALL: Sequence of one or more dora and uradora indicator tiles.
    RIICHI: One of riichi, riichi-ippatsu, double-riichi, double-riichi-ippatsu, or not specified to indicate riichi was not called.
    WINNING_TILE_FROM: One of haitei, rinshan, tenhou, chiihou, tsumo, houtei, chankan, chankan-ankan, kanburi, renhou, ron.
                       The ron variants can additionally take -shimocha / -toimen / -kamicha to specify the ron'd seat, eg ron-toimen, otherwise a seat is arbitrarily chosen.

If WINNING_TILE is not specified, all waits will be checked.

If WINNING_TILE_FROM is tenhou, HAND may be specified as a 14-tile hand for rulesets where tenhou can be won by considering any tile of the starting hand as the new tile.


Examples:

    $ {arg0} E E 2s '33s40666m 666-p 3-24m' tsumo 6m

    Best hand: {{ minkou 6p 6p 6p }} {{ minjun 2m 3m 4m }} {{ anjun 4m 0m 6m }} {{ ankou 6m 6m 6m shanpon }} {{ 3s 3s }}
    Score: base: 20 fu, meld1: 2 fu, meld4: 4 fu, tsumo: 2 fu, tanyao: 1 han, dora: 3 han = 4 han 30 fu
    Points: shimocha: 3900, toimen: 3900, kamicha: 3900 = 11700
    Absolute points: ton: +11700, nan: -3900, shaa: -3900, pei: -3900

    Other waits:

    + 3m
    Best hand: {{ minkou 6p 6p 6p }} {{ minjun 2m 3m 4m }} {{ ankou 6m 6m 6m }} {{ anjun 3m 4m 0m ryanmen_low }} {{ 3s 3s }}
    Score: base: 20 fu, meld1: 2 fu, meld3: 4 fu, tsumo: 2 fu, tanyao: 1 han, dora: 3 han = 4 han 30 fu
    Points: shimocha: 3900, toimen: 3900, kamicha: 3900 = 11700
    Absolute points: ton: +11700, nan: -3900, shaa: -3900, pei: -3900

    + 3s
    Best hand: {{ minkou 6p 6p 6p }} {{ minjun 2m 3m 4m }} {{ anjun 4m 0m 6m }} {{ ankou 3s 3s 3s shanpon }} {{ 6m 6m }}
    Score: base: 20 fu, meld1: 2 fu, meld4: 4 fu, tsumo: 2 fu, tanyao: 1 han, dora: 4 han = 5 han 30 fu Mangan
    Points: shimocha: 4000, toimen: 4000, kamicha: 4000 = 12000
    Absolute points: ton: +12000, nan: -4000, shaa: -4000, pei: -4000


    $ {arg0} E W 1s6m '456s123p2245m777z' riichi ron-shimocha 3m

    Best hand: {{ anjun 1p 2p 3p }} {{ anjun 4s 5s 6s }} {{ ankou R R R }} {{ minjun 3m 4m 5m ryanmen_low }} {{ 2m 2m }}
    Score: base: 20 fu, meld3: 8 fu, menzen_kafu: 10 fu, riichi: 1 han, yakuhai_chun: 1 han = 2 han 40 fu
    Points: shimocha: 2600 = 2600
    Absolute points: shaa: +2600, pei: -2600

    Other waits:

    + 6m
    Best hand: {{ anjun 1p 2p 3p }} {{ anjun 4s 5s 6s }} {{ ankou R R R }} {{ minjun 4m 5m 6m ryanmen_high }} {{ 2m 2m }}
    Score: base: 20 fu, meld3: 8 fu, menzen_kafu: 10 fu, riichi: 1 han, yakuhai_chun: 1 han = 2 han 40 fu
    Points: shimocha: 2600 = 2600
    Absolute points: shaa: +2600, pei: -2600


    $ {arg0} E E 7m '11122233344455z' tenhou

    Best hand: {{ ankou E E E }} {{ ankou S S S }} {{ ankou W W W }} {{ ankou N N N }} {{ Wh Wh }}
    Score: base: 20 fu, meld1: 8 fu, meld2: 8 fu, meld3: 8 fu, meld4: 8 fu, pair: 2 fu, wait: 2 fu, tsumo: 2 fu, mentsumo: 1 han, yakuhai_ton: 2 han, toitoi: 2 han, suuankou: Double yakuman, daisuushii: Double yakuman, tsuuiisou: Yakuman, tenhou: Yakuman = Sextuple yakuman
    Points: shimocha: 96000, toimen: 96000, kamicha: 96000 = 288000
    Absolute points: ton: +288000, nan: -96000, shaa: -96000, pei: -96000


    $ {arg0} E E 7m '1122233344455z' tenhou

    Waits:

    + E
    Best hand: {{ ankou S S S }} {{ ankou W W W }} {{ ankou N N N }} {{ ankou E E E shanpon }} {{ Wh Wh }}
    Score: base: 20 fu, meld1: 8 fu, meld2: 8 fu, meld3: 8 fu, meld4: 8 fu, pair: 2 fu, tsumo: 2 fu, mentsumo: 1 han, yakuhai_ton: 2 han, toitoi: 2 han, suuankou: Yakuman, daisuushii: Double yakuman, tsuuiisou: Yakuman, tenhou: Yakuman = Quintuple yakuman
    Points: shimocha: 80000, toimen: 80000, kamicha: 80000 = 240000
    Absolute points: ton: +240000, nan: -80000, shaa: -80000, pei: -80000

    + Wh
    Best hand: {{ ankou S S S }} {{ ankou W W W }} {{ ankou N N N }} {{ ankou Wh Wh Wh shanpon }} {{ E E }}
    Score: base: 20 fu, meld1: 8 fu, meld2: 8 fu, meld3: 8 fu, meld4: 8 fu, pair: 4 fu, tsumo: 2 fu, mentsumo: 1 han, yakuhai_haku: 1 han, toitoi: 2 han, suuankou: Yakuman, shousuushii: Yakuman, tsuuiisou: Yakuman, tenhou: Yakuman = Quadruple yakuman
    Points: shimocha: 64000, toimen: 64000, kamicha: 64000 = 192000
    Absolute points: ton: +192000, nan: -64000, shaa: -64000, pei: -64000
");
}

fn print_best_hand(
	w: &mut impl std::io::Write,
	game_type: GameType,
	rules: &Rules,
	seat_wind: WindTile,
	winning_tile_from: WinningTileFrom,
	score: Option<(ScorableHand, Score, ScoreAggregate)>,
) {
	let Some((hand, score, score_aggregate)) = score else {
		_ = writeln!(w, "No yaku");
		return;
	};

	let points = score.score(
		game_type,
		rules,
		// TODO: take arg for riichi bou
		0,
		// TODO: take arg for honba
		0,
		seat_wind,
		winning_tile_from.ron_seat(),
		// TODO: take args for sekinin barai
		None,
		None,
	);
	let total = points.total();

	_ = writeln!(w, "Best hand: {hand}");
	_ = writeln!(w, "Score: {score} = {score_aggregate}");
	_ = writeln!(w, "Points: {points} = {total}");
	let points_absolute = points.to_absolute(seat_wind);
	_ = writeln!(w, "Absolute points: {points_absolute}");
}

fn print_best_tenhou_hand(
	w: &mut impl std::io::Write,
	game_type: GameType,
	rules: &Rules,
	doras: &Tile34MultiSet,
	round_wind: WindTile,
	seat_wind: WindTile,
	nukidora: u8,
	riichi: Riichi,
	winning_tile_from: WinningTileFrom,
	hand: Hand<U<14>, U<0>>,
) {
	// Arbitrarily use the first tile as the winning tile for the purpose of `ScorableHand::score()`.
	// It can end up disagreeing with the `ScorableHand` itself, but that's fine, because `ScorableHand::score()` only uses it
	// for calculating iipin mouyue and chuupin raoyui, both of which cannot happen with tenhou.
	//
	// TODO: Remove the need for this hack.
	let winning_tile = hand.0.clone().into_iter().next().unwrap().0;

	let score =
		hand.into_scorable_hands()
		.filter_map(|hand| {
			let (score, score_aggregate) = hand.score(
				rules,
				doras,
				round_wind,
				seat_wind,
				nukidora,
				riichi,
				winning_tile,
				winning_tile_from,
			)?;
			Some((hand, score, score_aggregate))
		})
		.max_by(|&(_, score1, score_aggregate1), &(_, score2, score_aggregate2)|
			score_aggregate1.yakuman.0.cmp(&score_aggregate2.yakuman.0)
			.then_with(|| score_aggregate1.han.0.cmp(&score_aggregate2.han.0))
			.then_with(|| score_aggregate1.fu.0.cmp(&score_aggregate2.fu.0))
			.then_with(|| score1.rounding.0.cmp(&score2.rounding.0).reverse())
		);
	print_best_hand(w, game_type, rules, seat_wind, winning_tile_from, score);
}

fn print_best_non_tenhou_hand(
	w: &mut impl std::io::Write,
	game_type: GameType,
	rules: &Rules,
	doras: &Tile34MultiSet,
	round_wind: WindTile,
	seat_wind: WindTile,
	nukidora: u8,
	riichi: Riichi,
	winning_tile: Tile,
	winning_tile_from: WinningTileFrom,
	hand: HandStable,
) {
	let score = hand.max_score(
		rules,
		doras,
		round_wind,
		seat_wind,
		nukidora,
		riichi,
		winning_tile,
		winning_tile_from,
	);
	print_best_hand(w, game_type, rules, seat_wind, winning_tile_from, score);
}
