use crate::{
	GameType,
	NumberTile,
	Tile,
};

macro_rules! make_tset {
	(
		$( $(#[ $meta:meta ])* pub type $tset:ident = TileSet<$tile:ty, $n:literal, $tile_to_offset:ident, $offset_to_tile:ident, $all_yonma:ident, $all_sanma:ident, IntoIter = $tset_intoiter:ident>; )*
	) => {
		$(
			$(#[ $meta ])*
			#[derive(Clone, Default, PartialEq, Eq)]
			#[repr(transparent)]
			pub struct $tset {
				pub(crate) present: u64,
			}

			impl $tset {
				pub const fn new() -> Self {
					Self {
						present: 0,
					}
				}

				#[doc = concat!("Create a `", stringify!($tset), "` that contains all the tiles that exist in the given game type.")]
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

				/// Returns `true` if this set is empty.
				pub const fn is_empty(&self) -> bool {
					self.present == 0
				}

				/// Returns `true` if this set contains the given tile.
				pub const fn contains(&self, tile: $tile) -> bool {
					self.tile_to_present_ref(tile)
				}

				/// Inserts the given tile into this set.
				///
				/// Returns `false` when the tile was already present in the set.
				pub const fn insert(&mut self, tile: $tile) -> bool {
					let mut count = self.tile_to_present_mut(tile);
					!count.set(true)
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
					count.set(false)
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

			#[doc = concat!("Returns a `", stringify!($tset), "` containing all the elements of this set that are also present in the given set.")]
			impl core::ops::BitAnd for $tset {
				type Output = Self;

				fn bitand(self, other: Self) -> Self::Output {
					Self { present: self.present & other.present }
				}
			}

			/// Retains only the elements of this set that are also present in the given set.
			impl core::ops::BitAndAssign for $tset {
				fn bitand_assign(&mut self, other: Self) {
					self.present &= other.present;
				}
			}

			#[doc = concat!("Returns a `", stringify!($tset), "` containing all the elements of this set and all the elements of the given set.")]
			impl core::ops::BitOr for $tset {
				type Output = Self;

				fn bitor(self, other: Self) -> Self::Output {
					Self { present: self.present | other.present }
				}
			}

			/// Inserts all the elements of the given set into this set.
			impl core::ops::BitOrAssign for $tset {
				fn bitor_assign(&mut self, other: Self) {
					self.present |= other.present;
				}
			}

			#[doc = concat!("Returns a `", stringify!($tset), "` with all the elements of this set and all the elements of the given set")]
			/// except the elements that are present in both sets.
			impl core::ops::BitXor for $tset {
				type Output = Self;

				fn bitxor(self, other: Self) -> Self::Output {
					Self { present: self.present ^ other.present }
				}
			}

			/// Inserts all elements of the given set into this set and removes all elements from this set that are also present in the given set.
			impl core::ops::BitXorAssign for $tset {
				fn bitxor_assign(&mut self, other: Self) {
					self.present ^= other.present;
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

			#[doc = concat!("Returns a `", stringify!($tset), "` with all the elements that this type of set could have except the elements present in this set.")]
			impl core::ops::Not for $tset {
				type Output = Self;

				fn not(self) -> Self::Output {
					Self { present: !(self.present) & ((0b1 << $n) - 1) }
				}
			}

			#[doc = concat!("An [`Iterator`] of all [`", stringify!($tile), "`]s in a [`", stringify!($tset), "`].")]
			#[derive(Clone)]
			#[repr(transparent)]
			pub struct $tset_intoiter {
				present: u64,
			}

			impl $tset_intoiter {
				fn next_inner(&mut self, offset: u32) -> $tile {
					#[expect(clippy::cast_possible_truncation)]
					let offset = offset as u8;
					let tile = $offset_to_tile(offset);
					let mut count = U1Mut {
						present: &mut self.present,
						offset,
					};
					count.set(false);
					tile
				}
			}

			impl core::fmt::Debug for $tset_intoiter {
				fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
					f.debug_struct(stringify!($tset_intoiter)).finish_non_exhaustive()
				}
			}

			impl Iterator for $tset_intoiter {
				type Item = $tile;

				fn next(&mut self) -> Option<Self::Item> {
					Some(self.next_inner(self.present.lowest_one()?))
				}

				fn size_hint(&self) -> (usize, Option<usize>) {
					let len = self.len();
					(len, Some(len))
				}
			}

			impl DoubleEndedIterator for $tset_intoiter {
				fn next_back(&mut self) -> Option<Self::Item> {
					Some(self.next_inner(self.present.highest_one()?))
				}
			}

			impl ExactSizeIterator for $tset_intoiter {
				fn len(&self) -> usize {
					self.present.count_ones() as usize
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
	pub type Tile27Set = TileSet<NumberTile, 27, number_tile_to_offset, offset_to_number_tile, number_tiles_all_yonma, number_tiles_all_sanma, IntoIter = Tile27SetIntoIter>;

	/// A set specialized to hold [`Tile`]s in a compact non-allocating representation.
	///
	/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
	/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
	pub type Tile34Set = TileSet<Tile, 34, tile34_to_offset, offset_to_tile34, tiles34_all_yonma, tiles34_all_sanma, IntoIter = Tile34SetIntoIter>;

	/// A set specialized to hold [`Tile`]s in a compact non-allocating representation.
	///
	/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as distinct tiles
	/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
	pub type Tile37Set = TileSet<Tile, 37, tile37_to_offset, offset_to_tile37, tiles37_all_yonma, tiles37_all_sanma, IntoIter = Tile37SetIntoIter>;
}

assert_size_of!(Tile27Set, 8);
assert_size_of!(Tile34Set, 8);
assert_size_of!(Tile37Set, 8);

const fn number_tile_to_offset(tile: NumberTile) -> u8 {
	(tile as u8 - tn!(1m) as u8) >> 1
}

const fn offset_to_number_tile(offset: u8) -> NumberTile {
	let offset = (offset << 1) + tn!(1m) as u8;
	unsafe { core::mem::transmute::<u8, NumberTile>(offset) }
}

const fn number_tiles_all_yonma() -> &'static [NumberTile] {
	&tn![
		1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
	]
}

const fn number_tiles_all_sanma() -> &'static [NumberTile] {
	&tn![
		1m, 9m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
	]
}

const fn tile34_to_offset(tile: Tile) -> u8 {
	(tile as u8 - t!(1m) as u8) >> 1
}

const fn offset_to_tile34(offset: u8) -> Tile {
	let offset = (offset << 1) + t!(1m) as u8;
	unsafe { core::mem::transmute::<u8, Tile>(offset) }
}

const fn tiles34_all_yonma() -> &'static [Tile] {
	&t![
		1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
		E, S, W, N,
		Wh, G, R,
	]
}

const fn tiles34_all_sanma() -> &'static [Tile] {
	&t![
		1m, 9m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
		E, S, W, N,
		Wh, G, R,
	]
}

const fn tile37_to_offset(tile: Tile) -> u8 {
	((tile as u8 - t!(1m) as u8) >> 1) + 3 - ((tile as u8) < (t!(0m) as u8)) as u8 - ((tile as u8) < (t!(0p) as u8)) as u8 - ((tile as u8) < (t!(0s) as u8)) as u8
}

const fn offset_to_tile37(offset: u8) -> Tile {
	let tile = offset - (offset >= 5) as u8 - (offset >= 15) as u8 - (offset >= 25) as u8;
	let tile = ((tile << 1) + t!(1m) as u8) | (offset == 5 || offset == 15 || offset == 25) as u8;
	unsafe { core::mem::transmute::<u8, Tile>(tile) }
}

const fn tiles37_all_yonma() -> &'static [Tile] {
	Tile::each(GameType::Yonma)
}

const fn tiles37_all_sanma() -> &'static [Tile] {
	Tile::each(GameType::Sanma)
}

struct U1Mut<'a> {
	present: &'a mut u64,
	offset: u8,
}

impl U1Mut<'_> {
	const fn set(&mut self, value: bool) -> bool {
		let mask = 0b1 << self.offset;
		let previous = *self.present & mask != 0;
		*self.present = (*self.present & !mask) | ((value as u64) << self.offset);
		previous
	}
}

impl Tile34Set {
	pub(crate) const TERMINALS: Self = t34set! { 1m, 9m, 1p, 9p, 1s, 9s };

	pub(crate) const HONORS: Self = t34set! { E, S, W, G, N, Wh, G, R };

	pub(crate) const KOKUSHI_MUSOU_VALID: Self = t34set! { 1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R };
}

impl From<Tile37Set> for Tile34Set {
	fn from(set: Tile37Set) -> Self {
		let present = set.present;
		let present =
			( present & 0b0000000_0000000000_0000000000_0000011111) |
			((present & 0b0000000_0000000000_0000011111_1111100000) >> 1) |
			((present & 0b0000000_0000011111_1111100000_0000000000) >> 2) |
			((present & 0b1111111_1111100000_0000000000_0000000000) >> 3);
		Self { present }
	}
}

impl From<Tile34Set> for Tile37Set {
	fn from(set: Tile34Set) -> Self {
		let present = set.present;
		let present = cfg_select! {
			all(target_arch = "x86_64", target_feature = "bmi2") => unsafe { core::arch::x86_64::_pdep_u64(present, 0b1111111_1111011111_1111011111_1111011111) },
			_ =>
				( present & 0b0000000_000000000_000000000_000011111) |
				((present & 0b0000000_000000000_000011111_111100000) << 1) |
				((present & 0b0000000_000011111_111100000_000000000) << 2) |
				((present & 0b1111111_111100000_000000000_000000000) << 3),
		};
		Self { present }
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
			if matches!(tile, t!(0m | 0p | 0s)) {
				assert!(!set.insert(tile));
			}
			else {
				assert!(set.insert(tile));
			}
		}
		for &tile in Tile::each(GameType::Yonma) {
			if matches!(tile, t!(0m | 0p | 0s)) {
				assert!(!set.remove(tile));
			}
			else {
				assert!(set.remove(tile));
			}
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::each(GameType::Yonma).iter().rev() {
			if matches!(tile, t!(5m | 5p | 5s)) {
				assert!(!set.insert(tile));
			}
			else {
				assert!(set.insert(tile));
			}
		}
		for &tile in Tile::each(GameType::Yonma).iter().rev() {
			if matches!(tile, t!(5m | 5p | 5s)) {
				assert!(!set.remove(tile));
			}
			else {
				assert!(set.remove(tile));
			}
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

		assert!(set.into_iter().eq(Tile::each(GameType::Yonma).iter().copied().filter(|&t| !matches!(t, t!(0m | 0p | 0s)))));
	}
}
