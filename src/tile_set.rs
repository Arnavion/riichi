use crate::{
	GameType,
	NumberTile,
	Tile,
};

macro_rules! make_tset {
	(
		$( $(#[ $meta:meta ])* pub type $tset:ident = TileSet<$tile:ty, $n:literal, $tile_to_offset:ident, $offsets_to_tiles:ident, $all_yonma:ident, $all_sanma:ident, IntoIter = $tset_intoiter:ident>; )*
	) => {
		$(
			$(#[ $meta ])*
			#[derive(Clone, Default, PartialEq, Eq)]
			#[repr(transparent)]
			pub struct $tset {
				present: u64,
			}

			impl $tset {
				pub const fn new() -> Self {
					Self {
						present: 0,
					}
				}

				pub fn all(game_type: GameType) -> Self {
					const YONMA_RESULT: $tset = {
						let tiles = $all_yonma();

						// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
						let mut result = $tset::new();
						let mut i = 0;
						while i < tiles.len() {
							result.insert(tiles[i]);
							i += 1;
						}

						result
					};

					const SANMA_RESULT: $tset = {
						let tiles = $all_sanma();

						// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
						let mut result = $tset::new();
						let mut i = 0;
						while i < tiles.len() {
							result.insert(tiles[i]);
							i += 1;
						}

						result
					};

					match game_type {
						GameType::Yonma => YONMA_RESULT,
						GameType::Sanma => SANMA_RESULT,
					}
				}

				pub const fn is_empty(&self) -> bool {
					self.present == 0
				}

				/// Gets the number of occurences of the given tile in this set.
				pub const fn contains(&self, tile: $tile) -> bool {
					self.tile_to_present_ref(tile)
				}

				/// Inserts the given tile into this set.
				///
				/// Returns `false` when the tile was already present in the set.
				pub const fn insert(&mut self, tile: $tile) -> bool {
					let mut count = self.tile_to_present_mut(tile);
					if count.get() {
						false
					}
					else {
						count.set(true);
						true
					}
				}

				/// Inserts all tiles from the given iterator into this set.
				///
				/// # Errors
				///
				/// Returns `Err()` when inserting more of a tile than should exist.
				pub fn try_extend(&mut self, iter: impl IntoIterator<Item = $tile>) -> Result<(), $tile> {
					for tile in iter {
						if !self.insert(tile) {
							return Err(tile);
						}
					}
					Ok(())
				}

				/// Removes the given tile from this set.
				///
				/// Returns `true` if this tile existed in the set, `false` otherwise.
				pub const fn remove(&mut self, tile: $tile) -> bool {
					let mut count = self.tile_to_present_mut(tile);
					let result = count.get();
					count.set(false);
					result
				}

				const fn tile_to_present_ref(&self, tile: $tile) -> bool {
					let offset = $tile_to_offset(tile);
					self.present & (0b1 << offset) != 0
				}

				const fn tile_to_present_mut(&mut self, tile: $tile) -> U1Mut<'_> {
					let offset = $tile_to_offset(tile);
					U1Mut {
						present: &mut self.present,
						offset,
					}
				}
			}

			impl core::fmt::Debug for $tset
			where
				Self: Clone + IntoIterator<Item = $tile>,
			{
				fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
					f.debug_set().entries(self.clone()).finish()
				}
			}

			impl FromIterator<$tile> for $tset {
				fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = $tile> {
					let mut result = Self::default();
					for tile in iter {
						_ = result.insert(tile);
					}
					result
				}
			}

			impl IntoIterator for $tset {
				type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
				type IntoIter = $tset_intoiter;

				fn into_iter(self) -> Self::IntoIter {
					$tset_intoiter {
						present: self.present,
					}
				}
			}

			#[derive(Clone)]
			#[repr(transparent)]
			pub struct $tset_intoiter {
				present: u64,
			}

			impl core::fmt::Debug for $tset_intoiter {
				fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
					f.debug_struct(stringify!($tset_intoiter)).finish_non_exhaustive()
				}
			}

			impl Iterator for $tset_intoiter {
				type Item = $tile;

				fn next(&mut self) -> Option<Self::Item> {
					#[expect(clippy::cast_possible_truncation)]
					let offset = self.present.trailing_zeros() as u8;
					let tile = *$offsets_to_tiles().get(usize::from(offset))?;
					let mut count = U1Mut {
						present: &mut self.present,
						offset,
					};
					count.set(false);
					Some(tile)
				}

				fn size_hint(&self) -> (usize, Option<usize>) {
					(0, Some($n))
				}
			}

			impl core::iter::FusedIterator for $tset_intoiter {}
		)*
	};
}

make_tset! {
	/// A set specialized to hold [`NumberTile`]s in a compact non-allocating representation.
	///
	/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
	/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
	pub type Tile27Set = TileSet<NumberTile, 27, number_tile_to_offset, offsets_to_number_tiles, number_tiles_all_yonma, number_tiles_all_sanma, IntoIter = Tile27SetIntoIter>;

	/// A set specialized to hold [`Tile`]s in a compact non-allocating representation.
	///
	/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
	/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
	pub type Tile34Set = TileSet<Tile, 34, tile_to_offset, offsets_to_tiles, tiles_all_yonma, tiles_all_sanma, IntoIter = Tile34SetIntoIter>;
}

assert_size_of!(Tile27Set, 8);
assert_size_of!(Tile34Set, 8);

const fn number_tile_to_offset(tile: NumberTile) -> u8 {
	(tile as u8) >> 1
}

const fn offsets_to_number_tiles() -> &'static [NumberTile] {
	&tn![
		1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
	]
}

const fn number_tiles_all_yonma() -> &'static [NumberTile] {
	NumberTile::each(GameType::Yonma)
}

const fn number_tiles_all_sanma() -> &'static [NumberTile] {
	NumberTile::each(GameType::Sanma)
}

const fn tile_to_offset(tile: Tile) -> u8 {
	(tile as u8) >> 1
}

const fn offsets_to_tiles() -> &'static [Tile] {
	&t![
		1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
		E, S, W, N,
		Wh, G, R,
	]
}

const fn tiles_all_yonma() -> &'static [Tile] {
	Tile::each(GameType::Yonma)
}

const fn tiles_all_sanma() -> &'static [Tile] {
	Tile::each(GameType::Sanma)
}

struct U1Mut<'a> {
	present: &'a mut u64,
	offset: u8,
}

impl U1Mut<'_> {
	const fn get(&self) -> bool {
		*self.present & (0b1 << self.offset) != 0
	}

	const fn set(&mut self, value: bool) {
		*self.present = *self.present & !(0b1 << self.offset) | ((value as u64) << self.offset);
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

	use crate::GameType;
	use super::*;

	#[test]
	fn all_27() {
		let mut set = Tile27Set::default();

		for &tile in NumberTile::each(GameType::Yonma) {
			assert!(set.insert(tile));
		}
		for &tile in NumberTile::each(GameType::Yonma) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in NumberTile::each(GameType::Yonma).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in NumberTile::each(GameType::Yonma).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in NumberTile::each(GameType::Yonma) {
			assert!(!set.remove(tile));
		}
		assert_eq!(set, Default::default());

		let set: Tile27Set = NumberTile::each(GameType::Yonma).iter().copied().collect();
		assert_eq!(set, Tile27Set::all(GameType::Yonma));
		assert_eq!(
			std::format!("{set:?}"),
			"{1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m, 1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p, 1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s}",
		);

		{
			let mut set = set.clone();

			assert!(set.contains(tn!(5m)));
			assert!(set.contains(tn!(0m)));

			assert!(!set.insert(tn!(5m)));
			assert!(set.contains(tn!(5m)));
			assert!(set.contains(tn!(0m)));

			assert!(!set.insert(tn!(0m)));
			assert!(set.contains(tn!(5m)));
			assert!(set.contains(tn!(0m)));

			{
				let mut set = set.clone();
				assert!(set.remove(tn!(5m)));
				assert!(!set.contains(tn!(5m)));
				assert!(!set.contains(tn!(0m)));
			}

			{
				let mut set = set.clone();
				assert!(set.remove(tn!(0m)));
				assert!(!set.contains(tn!(5m)));
				assert!(!set.contains(tn!(0m)));
			}
		}

		assert_eq!(set.clone().into_iter().count(), 27);

		assert!(set.into_iter().eq(NumberTile::each(GameType::Yonma).iter().copied()));
	}

	#[test]
	fn all_34() {
		let mut set = Tile34Set::default();

		for &tile in Tile::each(GameType::Yonma) {
			assert!(set.insert(tile));
		}
		for &tile in Tile::each(GameType::Yonma) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::each(GameType::Yonma).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in Tile::each(GameType::Yonma).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::each(GameType::Yonma) {
			assert!(!set.remove(tile));
		}
		assert_eq!(set, Default::default());

		let set: Tile34Set = Tile::each(GameType::Yonma).iter().copied().collect();
		assert_eq!(set, Tile34Set::all(GameType::Yonma));
		assert_eq!(
			std::format!("{set:?}"),
			"{1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m, 1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p, 1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s, E, S, W, N, Wh, G, R}",
		);

		{
			let mut set = set.clone();

			assert!(set.contains(t!(5m)));
			assert!(set.contains(t!(0m)));

			assert!(!set.insert(t!(5m)));
			assert!(set.contains(t!(5m)));
			assert!(set.contains(t!(0m)));

			assert!(!set.insert(t!(0m)));
			assert!(set.contains(t!(5m)));
			assert!(set.contains(t!(0m)));

			{
				let mut set = set.clone();
				assert!(set.remove(t!(5m)));
				assert!(!set.contains(t!(5m)));
				assert!(!set.contains(t!(0m)));
			}

			{
				let mut set = set.clone();
				assert!(set.remove(t!(0m)));
				assert!(!set.contains(t!(5m)));
				assert!(!set.contains(t!(0m)));
			}
		}

		assert_eq!(set.clone().into_iter().count(), 34);

		assert!(set.into_iter().eq(Tile::each(GameType::Yonma).iter().copied()));
	}
}
