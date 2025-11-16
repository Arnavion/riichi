use riichi::{GameType, Tile};

fn main() {
	println!("{}", Tile::all(GameType::FourPlayer).len());
	for &tile in Tile::all(GameType::FourPlayer) {
		print!("{tile} ");
	}
	println!();
}
