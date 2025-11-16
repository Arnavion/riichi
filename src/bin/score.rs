use riichi::{
	GameType,
	HandStable,
	Riichi,
	Score,
	Tile,
	WinningTileFrom,
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
	let mut game_type = GameType::FourPlayer;
	let mut arg = args.next().ok_or(())?;
	if arg == "--help" {
		print_help(stdout, arg0);
		std::process::exit(0);
	}
	else if arg == "sanma" {
		game_type = GameType::ThreePlayer;
		arg = args.next().ok_or(())?;
	}

	let prevalent_wind = arg.parse()?;

	let seat_wind = args.next().ok_or(())?.parse()?;

	let (dora, _) = Tile::parse_run(&args.next().ok_or(())?)?;

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
		"houtei" => WinningTileFrom::Houtei,
		"rinshan" => WinningTileFrom::Rinshan,
		"chankan" => WinningTileFrom::Chankan,
		"tenhou" => WinningTileFrom::Tenhou,
		"chiihou" => WinningTileFrom::Chiihou,
		"tsumo" => WinningTileFrom::Tsumo,
		"ron" => WinningTileFrom::Ron,
		_ => return Err(()),
	};

	let winning_tile = args.next().ok_or(())?.parse()?;

	let is_dealer = seat_wind == tw!(E);

	let hands = hand.to_scorable_hands(winning_tile, winning_tile_from.into());
	let score =
		hands.into_iter()
		.filter_map(|hand| hand.score(
			riichi,
			winning_tile_from,
			0,
			game_type,
			dora.iter().copied(),
			prevalent_wind,
			seat_wind,
		))
		.map(|score_raw| {
			let score: Score = score_raw.into();
			let points = score.score(is_dealer, winning_tile_from.into());
			let total = points.total(is_dealer, game_type);
			(score_raw, score, points, total)
		})
		.max_by_key(|&(_, _, _, total)| total);
	if let Some((score_raw, score, points, total)) = score {
		_ = writeln!(stdout, "Raw score: {score_raw:?}");
		_ = writeln!(stdout, "Score: {score:?}");
		_ = writeln!(stdout, "Points: {points:?}");
		_ = writeln!(stdout, "Total: {total:?}");
	}
	else {
		_ = writeln!(stdout, "No yaku");
	}

	Ok(())
}

fn print_help(w: &mut impl std::io::Write, arg0: &str) {
	_ = writeln!(w, "Calculates the score of the given hand.");
	_ = writeln!(w);
	_ = writeln!(w, "Usage: {arg0} [sanma] <PREVALENT_WIND> <SEAT_WIND> <DORA> <HAND> [riichi | riichi-ippatsu | double-riichi | double-riichi-ippatsu] <haitei | houtei | rinshan | chankan | tenhou | chiihou | tsumo | ron> <WINNING_TILE>");
	_ = writeln!(w);
	_ = writeln!(w, "    <HAND> is specified in MPSZ format, extended to support notating minjuns / minkous / ankans / minkans. Ref: https://note.com/yuarasino/n/n1ba95bf3b618");
	_ = writeln!(w, "    <DORA> is a sequence of 1 or more dora and uradora tiles.");
	_ = writeln!(w);
	_ = writeln!(w);
	_ = writeln!(w, "Examples:");
	_ = writeln!(w);
	_ = writeln!(w, "    $ {arg0} E E 2s '33s40666m 666-p 3-24m' tsumo 6m");
	_ = writeln!(w);
	_ = writeln!(w, "    Raw score: ScoreRaw {{ base: Fu(20), win_condition: Fu(2), meld2: Fu(4), meld3: Fu(2), tanyao: Han(1), dora: Han(3) }}");
	_ = writeln!(w, "    Score: Score {{ fu: 30, han: 4, yakuman: 0 }}");
	_ = writeln!(w, "    Points: FromEveryone {{ dealer: 0, non_dealer: 3900 }}");
	_ = writeln!(w, "    Total: 11700");
	_ = writeln!(w);
	_ = writeln!(w);
	_ = writeln!(w, "    $ {arg0} E W 1s6m '456s123p2245m777z' riichi ron 3m");
	_ = writeln!(w);
	_ = writeln!(w, "    Raw score: ScoreRaw {{ base: Fu(20), win_condition: Fu(10), meld3: Fu(8), riichi: Han(1), yakuhai_chun: Han(1) }}");
	_ = writeln!(w, "    Score: Score {{ fu: 40, han: 2, yakuman: 0 }}");
	_ = writeln!(w, "    Points: FromRon(2600)");
	_ = writeln!(w, "    Total: 2600");
}
