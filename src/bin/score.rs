use generic_array::typenum::U;

use riichi::{
	GameType,
	HandStable,
	Riichi,
	ScoreAggregate, SeatRelative,
	Tile, Tile34MultiSet,
	WinningTileFrom,
	max_score,
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
	let doras = {
		let mut doras = dead_wall;
		for t in &mut doras[..] {
			*t = t.indicates_dora(game_type);
		}
		doras
	};

	let Some(hand) = args.next() else {
		eprintln!("could not parse HAND");
		return Err(());
	};
	let Ok(hand) = hand.parse::<HandStable>() else {
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

	let winning_tile_from = match &*arg {
		"haitei" => WinningTileFrom::Haitei,
		"houtei-shimocha" => WinningTileFrom::Houtei(SeatRelative::Shimocha),
		"houtei-toimen" => WinningTileFrom::Houtei(SeatRelative::Toimen),
		"houtei-kamicha" => WinningTileFrom::Houtei(SeatRelative::Kamicha),
		"rinshan" => WinningTileFrom::Rinshan,
		"chankan-shimocha" => WinningTileFrom::ChankanShouminkan(SeatRelative::Shimocha),
		"chankan-toimen" => WinningTileFrom::ChankanShouminkan(SeatRelative::Toimen),
		"chankan-kamicha" => WinningTileFrom::ChankanShouminkan(SeatRelative::Kamicha),
		"tenhou" => WinningTileFrom::Tenhou,
		"chiihou" => WinningTileFrom::Chiihou,
		"tsumo" => WinningTileFrom::Tsumo,
		"ron-shimocha" => WinningTileFrom::Ron(SeatRelative::Shimocha),
		"ron-toimen" => WinningTileFrom::Ron(SeatRelative::Toimen),
		"ron-kamicha" => WinningTileFrom::Ron(SeatRelative::Kamicha),
		_ => {
			eprintln!("could not parse WINNING_TILE_FROM");
			return Err(());
		},
	};

	let other_waits = if let Some(winning_tile) = args.next() {
		let Ok(winning_tile) = winning_tile.parse() else {
			eprintln!("could not parse WINNING_TILE");
			return Err(());
		};

		let hands = hand.to_scorable_hands(winning_tile, winning_tile_from.into());
		let score = max_score(
			game_type,
			// TODO: take arg for riichi bou
			0,
			// TODO: take arg for honba
			0,
			&doras,
			round_wind,
			seat_wind,
			nukidora,
			riichi,
			winning_tile_from,
			// TODO: take args for sekinin barai
			None,
			None,
			hands,
		);

		{
			let Some((hand, score, points, total)) = score else {
				_ = writeln!(stdout, "No yaku");
				return Ok(());
			};

			_ = writeln!(stdout, "Best hand: {hand}");
			_ = writeln!(stdout, "Score: {score} = {}", ScoreAggregate::from(score));
			_ = writeln!(stdout, "Points: {points} = {total}");
			let points_absolute = points.to_absolute(seat_wind);
			_ = writeln!(stdout, "Absolute points: {points_absolute}");
		}

		let other_waits: Tile34MultiSet = hand.tenpai(game_type).filter(|&t| t != winning_tile).collect();
		if other_waits.is_empty() {
			return Ok(());
		}
		_ = writeln!(stdout);
		_ = writeln!(stdout, "Other waits:");
		_ = writeln!(stdout);
		other_waits
	}
	else {
		let waits: Tile34MultiSet = hand.tenpai(game_type).collect();
		if waits.is_empty() {
			_ = writeln!(stdout, "No yaku");
			return Ok(());
		}
		waits
	};
	for (winning_tile, _) in other_waits {
		_ = writeln!(stdout, "+ {winning_tile}");
		let hands = hand.to_scorable_hands(winning_tile, winning_tile_from.into());
		let score = max_score(
			game_type,
			// TODO: take arg for riichi bou
			0,
			// TODO: take arg for honba
			0,
			&doras,
			round_wind,
			seat_wind,
			nukidora,
			riichi,
			winning_tile_from,
			// TODO: take args for sekinin barai
			None,
			None,
			hands,
		);

		let Some((hand, score, points, total)) = score else {
			_ = writeln!(stdout, "No yaku");
			_ = writeln!(stdout);
			continue;
		};

		_ = writeln!(stdout, "Best hand: {hand}");
		_ = writeln!(stdout, "Score: {score} = {}", ScoreAggregate::from(score));
		_ = writeln!(stdout, "Points: {points} = {total}");
		let points_absolute = points.to_absolute(seat_wind);
		_ = writeln!(stdout, "Absolute points: {points_absolute}");
		_ = writeln!(stdout);
	}

	Ok(())
}

fn print_help(w: &mut impl std::io::Write, arg0: &str) {
	_ = writeln!(w, "Calculates the score of the given hand.");
	_ = writeln!(w);
	_ = writeln!(w, "Usage: {arg0} [GAME_TYPE] <ROUND_WIND> <SEAT_WIND> <DEAD_WALL> <HAND> [RIICHI] <WINNING_TILE_FROM> [WINNING_TILE]");
	_ = writeln!(w);
	_ = writeln!(w, "    GAME_TYPE: If set to sanma-N, indicates three-player, otherwise default is four-player. N is the number of peidora, 0 to 4 inclusive.");
	_ = writeln!(w, "    HAND: Specified in MPSZ format, extended to support notating minjuns / minkous / ankans / minkans. Ref: https://note.com/yuarasino/n/n1ba95bf3b618");
	_ = writeln!(w, "    DEAD_WALL: Sequence of one or more dora and uradora indicator tiles.");
	_ = writeln!(w, "    RIICHI: One of riichi, riichi-ippatsu, double-riichi, double-riichi-ippatsu, or not specified to indicate riichi was not called.");
	_ = writeln!(w, "    WINNING_TILE_FROM: One of haitei, houtei-shimocha, houtei-toimen, houtei-kamicha, rinshan, chankan-shimocha, chankan-toimen, chankan-kamicha, tenhou, chiihou, tsumo, ron-shimocha, ron-toimen, ron-kamicha.");
	_ = writeln!(w);
	_ = writeln!(w, "If WINNING_TILE is not specified, all waits will be checked.");
	_ = writeln!(w);
	_ = writeln!(w);
	_ = writeln!(w, "Examples:");
	_ = writeln!(w);
	_ = writeln!(w, "    $ {arg0} E E 2s '33s40666m 666-p 3-24m' tsumo 6m");
	_ = writeln!(w);
	_ = writeln!(w, "    Best hand: {{ minjun 2m 3m 4m }} {{ ankou 6m 6m 6m }} {{ minkou 6p 6p 6p }} {{ anjun 4m 0m 6m ryanmen_high }} {{ 3s 3s }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 2 fu, meld2: 4 fu, meld3: 2 fu, tanyao: 1 han, dora: 3 han = 4 han 30 fu");
	_ = writeln!(w, "    Points: shimocha: 3900, toimen: 3900, kamicha: 3900 = 11700");
	_ = writeln!(w, "    Absolute points: ton: +11700, nan: -3900, shaa: -3900, pei: -3900");
	_ = writeln!(w);
	_ = writeln!(w, "    Other waits:");
	_ = writeln!(w);
	_ = writeln!(w, "    + 3m");
	_ = writeln!(w, "    Best hand: {{ minjun 2m 3m 4m }} {{ ankou 6m 6m 6m }} {{ minkou 6p 6p 6p }} {{ anjun 3m 4m 0m ryanmen_low }} {{ 3s 3s }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 2 fu, meld2: 4 fu, meld3: 2 fu, tanyao: 1 han, dora: 3 han = 4 han 30 fu");
	_ = writeln!(w, "    Points: shimocha: 3900, toimen: 3900, kamicha: 3900 = 11700");
	_ = writeln!(w, "    Absolute points: ton: +11700, nan: -3900, shaa: -3900, pei: -3900");
	_ = writeln!(w);
	_ = writeln!(w, "    + 3s");
	_ = writeln!(w, "    Best hand: {{ minjun 2m 3m 4m }} {{ anjun 4m 0m 6m }} {{ minkou 6p 6p 6p }} {{ ankou 3s 3s 3s shanpon }} {{ 6m 6m }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 2 fu, meld3: 2 fu, meld4: 4 fu, tanyao: 1 han, dora: 4 han = 5 han 30 fu Mangan");
	_ = writeln!(w, "    Points: shimocha: 4000, toimen: 4000, kamicha: 4000 = 12000");
	_ = writeln!(w, "    Absolute points: ton: +12000, nan: -4000, shaa: -4000, pei: -4000");
	_ = writeln!(w);
	_ = writeln!(w);
	_ = writeln!(w, "    $ {arg0} E W 1s6m '456s123p2245m777z' riichi ron-shimocha 3m");
	_ = writeln!(w);
	_ = writeln!(w, "    Best hand: {{ anjun 1p 2p 3p }} {{ anjun 4s 5s 6s }} {{ ankou R R R }} {{ minjun 3m 4m 5m ryanmen_low }} {{ 2m 2m }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 10 fu, meld3: 8 fu, riichi: 1 han, yakuhai_chun: 1 han = 2 han 40 fu");
	_ = writeln!(w, "    Points: shimocha: 2600 = 2600");
	_ = writeln!(w, "    Absolute points: shaa: +2600, pei: -2600");
	_ = writeln!(w);
	_ = writeln!(w, "    Other waits:");
	_ = writeln!(w);
	_ = writeln!(w, "    + 6m");
	_ = writeln!(w, "    Best hand: {{ anjun 1p 2p 3p }} {{ anjun 4s 5s 6s }} {{ ankou R R R }} {{ minjun 4m 5m 6m ryanmen_high }} {{ 2m 2m }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 10 fu, meld3: 8 fu, riichi: 1 han, yakuhai_chun: 1 han = 2 han 40 fu");
	_ = writeln!(w, "    Points: shimocha: 2600 = 2600");
	_ = writeln!(w, "    Absolute points: shaa: +2600, pei: -2600");
}
