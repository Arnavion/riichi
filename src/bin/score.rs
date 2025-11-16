use riichi::{
	GameType,
	HandStable,
	Riichi,
	ScoreAggregate, SeatRelative,
	Tile,
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
	let mut arg = args.next().ok_or(())?;
	if arg == "--help" {
		print_help(stdout, arg0);
		std::process::exit(0);
	}
	else if arg == "sanma" {
		game_type = GameType::Sanma;
		arg = args.next().ok_or(())?;
	}

	let round_wind = arg.parse()?;

	let seat_wind = args.next().ok_or(())?.parse()?;

	let (dead_wall, dead_wall_type) = Tile::parse_run(&args.next().ok_or(())?)?;
	if dead_wall_type.is_some() {
		return Err(());
	}
	let doras: Vec<_> = dead_wall.into_iter().map(|t| t.indicates_dora(game_type)).collect();

	let hand: HandStable = args.next().ok_or(())?.parse()?;

	let mut riichi = Riichi::NotRiichi;
	let mut arg = args.next().ok_or(())?;
	if arg == "riichi" {
		riichi = Riichi::Riichi { ippatsu: false, double: false };
		arg = args.next().ok_or(())?;
	}
	else if arg == "riichi-ippatsu" {
		riichi = Riichi::Riichi { ippatsu: true, double: false };
		arg = args.next().ok_or(())?;
	}
	else if arg == "double-riichi" {
		riichi = Riichi::Riichi { ippatsu: false, double: true };
		arg = args.next().ok_or(())?;
	}
	else if arg == "double-riichi-ippatsu" {
		riichi = Riichi::Riichi { ippatsu: true, double: true };
		arg = args.next().ok_or(())?;
	}

	let winning_tile_from = match &*arg {
		"haitei" => WinningTileFrom::Haitei,
		"houtei-shimocha" => WinningTileFrom::Houtei(SeatRelative::Shimocha),
		"houtei-toimen" => WinningTileFrom::Houtei(SeatRelative::Toimen),
		"houtei-kamicha" => WinningTileFrom::Houtei(SeatRelative::Kamicha),
		"rinshan" => WinningTileFrom::Rinshan,
		"chankan-shimocha" => WinningTileFrom::ChankanMinkan(SeatRelative::Shimocha),
		"chankan-toimen" => WinningTileFrom::ChankanMinkan(SeatRelative::Toimen),
		"chankan-kamicha" => WinningTileFrom::ChankanMinkan(SeatRelative::Kamicha),
		"tenhou" => WinningTileFrom::Tenhou,
		"chiihou" => WinningTileFrom::Chiihou,
		"tsumo" => WinningTileFrom::Tsumo,
		"ron-shimocha" => WinningTileFrom::Ron(SeatRelative::Shimocha),
		"ron-toimen" => WinningTileFrom::Ron(SeatRelative::Toimen),
		"ron-kamicha" => WinningTileFrom::Ron(SeatRelative::Kamicha),
		_ => return Err(()),
	};

	let winning_tile = args.next().ok_or(())?.parse()?;

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
		// TODO: take arg for nukidora
		0,
		riichi,
		winning_tile_from,
		// TODO: take args for sekinin barai
		None,
		None,
		hands,
	);
	if let Some((hand, score, points, total)) = score {
		_ = writeln!(stdout, "Best hand: {hand}");
		_ = writeln!(stdout, "Score: {score} = {}", ScoreAggregate::from(score));
		_ = writeln!(stdout, "Points: {points} = {total}");
		let points_absolute = points.to_absolute(seat_wind);
		_ = writeln!(stdout, "Absolute points: {points_absolute}");
	}
	else {
		_ = writeln!(stdout, "No yaku");
	}

	Ok(())
}

fn print_help(w: &mut impl std::io::Write, arg0: &str) {
	_ = writeln!(w, "Calculates the score of the given hand.");
	_ = writeln!(w);
	_ = writeln!(w, "Usage: {arg0} [GAME_TYPE] <PREVALENT_WIND> <SEAT_WIND> <DEAD_WALL> <HAND> [RIICHI] <WINNING_TILE_FROM> <WINNING_TILE>");
	_ = writeln!(w);
	_ = writeln!(w, "    GAME_TYPE: If set to sanma, indicates three-player, otherwise default is four-player.");
	_ = writeln!(w, "    HAND: Specified in MPSZ format, extended to support notating minjuns / minkous / ankans / minkans. Ref: https://note.com/yuarasino/n/n1ba95bf3b618");
	_ = writeln!(w, "    DEAD_WALL: Sequence of one or more dora and uradora indicator tiles.");
	_ = writeln!(w, "    RIICHI: One of riichi, riichi-ippatsu, double-riichi, double-riichi-ippatsu, or not specified to indicate riichi was not called.");
	_ = writeln!(w, "    WINNING_TILE_FROM: One of haitei, houtei-shimocha, houtei-toimen, houtei-kamicha, rinshan, chankan-shimocha, chankan-toimen, chankan-kamicha, tenhou, chiihou, tsumo, ron-shimocha, ron-toimen, ron-kamicha.");
	_ = writeln!(w);
	_ = writeln!(w);
	_ = writeln!(w, "Examples:");
	_ = writeln!(w);
	_ = writeln!(w, "    $ {arg0} E E 2s '33s40666m 666-p 3-24m' tsumo 6m");
	_ = writeln!(w);
	_ = writeln!(w, "    Best hand: {{ minjun 2m 3m 4m }} {{ ankou 6m 6m 6m }} {{ minkou 6p 6p 6p }} {{ anjun 4m 0m 6m ryanmen_right }} {{ 3s 3s }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 2 fu, meld2: 4 fu, meld3: 2 fu, tanyao: 1 han, dora: 3 han = 4 han 30 fu");
	_ = writeln!(w, "    Points: shimocha: 3900, toimen: 3900, kamicha: 3900 = 11700");
	_ = writeln!(w, "    Absolute points: ton: +11700, nan: -3900, shaa: -3900, pei: -3900");
	_ = writeln!(w);
	_ = writeln!(w);
	_ = writeln!(w, "    $ {arg0} E W 1s6m '456s123p2245m777z' riichi ron-shimocha 3m");
	_ = writeln!(w);
	_ = writeln!(w, "    Best hand: {{ anjun 1p 2p 3p }} {{ anjun 4s 5s 6s }} {{ ankou R R R }} {{ minjun 3m 4m 5m ryanmen_left }} {{ 2m 2m }}");
	_ = writeln!(w, "    Score: base: 20 fu, win_condition: 10 fu, meld3: 8 fu, riichi: 1 han, yakuhai_chun: 1 han = 2 han 40 fu");
	_ = writeln!(w, "    Points: shimocha: 2600 = 2600");
	_ = writeln!(w, "    Absolute points: shaa: +2600, pei: -2600");
}
