use crate::{
	GameType,
	NumberTile,
	Tile,
};

/// A set specialized to hold [`Tile`]s or [`NumberTile`] in a compact non-allocating representation.
///
/// See the pre-defined aliases [`Tile27Set`] and [`Tile34Set`].
pub struct TileSet<TElement>
where
	TElement: const TileSetElement,
{
	present: u64,
	element: core::marker::PhantomData<TElement>,
}

pub const trait TileSetElement {
	type Tile: Copy + core::fmt::Debug + 'static;
	const N: usize;

	fn tile_to_offset(tile: Self::Tile) -> u8;

	fn offsets_to_tiles() -> &'static [Self::Tile];

	fn all_yonma() -> &'static [Self::Tile];

	fn all_sanma() -> &'static [Self::Tile];
}

impl<TElement> TileSet<TElement>
where
	TElement: const TileSetElement,
{
	pub const fn all(game_type: GameType) -> Self {
		match game_type {
			GameType::Yonma => const { tile_set_all_yonma() },
			GameType::Sanma => const { tile_set_all_sanma() },
		}
	}

	pub const fn is_empty(&self) -> bool {
		*self == Self::default()
	}

	/// Gets the number of occurences of the given tile in this set.
	pub const fn contains(&self, tile: TElement::Tile) -> bool {
		self.tile_to_present_ref(tile)
	}

	/// Inserts the given tile into this set.
	///
	/// Returns `false` when the tile was already present in the set.
	pub const fn insert(&mut self, tile: TElement::Tile) -> bool {
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
	pub fn try_extend(&mut self, iter: impl IntoIterator<Item = TElement::Tile>) -> Result<(), TElement::Tile> {
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
	pub const fn remove(&mut self, tile: TElement::Tile) -> bool {
		let mut count = self.tile_to_present_mut(tile);
		let result = count.get();
		count.set(false);
		result
	}

	const fn tile_to_present_ref(&self, tile: TElement::Tile) -> bool {
		let offset = TElement::tile_to_offset(tile);
		self.present & (0b1 << offset) != 0
	}

	const fn tile_to_present_mut(&mut self, tile: TElement::Tile) -> U1Mut<'_> {
		let offset = TElement::tile_to_offset(tile);
		U1Mut {
			present: &mut self.present,
			offset,
		}
	}
}

impl<TElement> const Clone for TileSet<TElement>
where
	TElement: const TileSetElement,
{
	fn clone(&self) -> Self {
		Self {
			present: self.present,
			element: self.element,
		}
	}
}

impl<TElement> core::fmt::Debug for TileSet<TElement>
where
	TElement: const TileSetElement,
	Self: Clone + IntoIterator<Item = TElement::Tile>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_set().entries(self.clone()).finish()
	}
}

impl<TElement> const Default for TileSet<TElement>
where
	TElement: const TileSetElement,
{
	fn default() -> Self {
		Self {
			present: 0,
			element: core::marker::PhantomData,
		}
	}
}

impl<TElement> FromIterator<TElement::Tile> for TileSet<TElement>
where
	TElement: const TileSetElement,
{
	fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = TElement::Tile> {
		let mut result = Self::default();
		for tile in iter {
			_ = result.insert(tile);
		}
		result
	}
}

impl<TElement> IntoIterator for TileSet<TElement>
where
	TElement: const TileSetElement,
	TileSetIntoIter<TElement>: Iterator,
{
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = TileSetIntoIter<TElement>;

	fn into_iter(self) -> Self::IntoIter {
		TileSetIntoIter {
			present: self.present,
			element: Default::default(),
		}
	}
}

impl<TElement> const PartialEq for TileSet<TElement>
where
	TElement: const TileSetElement,
{
	fn eq(&self, other: &Self) -> bool {
		self.present == other.present
	}
}

impl<TElement> const Eq for TileSet<TElement>
where
	TElement: const TileSetElement,
{}

const fn tile_set_all_yonma<TElement>() -> TileSet<TElement>
where
	TElement: const TileSetElement,
{
	let tiles = TElement::all_yonma();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileSet::default();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

const fn tile_set_all_sanma<TElement>() -> TileSet<TElement>
where
	TElement: const TileSetElement,
{
	let tiles = TElement::all_sanma();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileSet::default();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

pub struct TileSetIntoIter<TElement>
where
	TElement: const TileSetElement,
{
	present: u64,
	element: core::marker::PhantomData<TElement>,
}

impl<TElement> const Clone for TileSetIntoIter<TElement>
where
	TElement: const TileSetElement,
{
	fn clone(&self) -> Self {
		Self {
			present: self.present,
			element: self.element,
		}
	}
}

impl<TElement> core::fmt::Debug for TileSetIntoIter<TElement>
where
	TElement: const TileSetElement,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("TileSetIntoIter").finish_non_exhaustive()
	}
}

impl<TElement> Iterator for TileSetIntoIter<TElement>
where
	TElement: const TileSetElement,
{
	type Item = TElement::Tile;

	fn next(&mut self) -> Option<Self::Item> {
		#[expect(clippy::cast_possible_truncation)]
		let offset = self.present.trailing_zeros() as u8;
		let tile = *TElement::offsets_to_tiles().get(usize::from(offset))?;
		let mut count = U1Mut {
			present: &mut self.present,
			offset,
		};
		count.set(false);
		Some(tile)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		(0, Some(TElement::N))
	}
}

impl<TElement> core::iter::FusedIterator for TileSetIntoIter<TElement>
where
	TElement: const TileSetElement,
{}

/// A set specialized to hold [`NumberTile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile27Set = TileSet<Tile27SetElement>;

assert_size_of!(Tile27Set, 8);

#[derive(Copy, Debug)]
#[derive_const(Clone)]
pub struct Tile27SetElement;

impl const TileSetElement for Tile27SetElement {
	type Tile = NumberTile;
	const N: usize = 27_usize;

	fn tile_to_offset(tile: Self::Tile) -> u8 {
		(tile as u8) >> 1
	}

	fn offsets_to_tiles() -> &'static [Self::Tile] {
		&tn![
			1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
			1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
			1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
		]
	}

	fn all_yonma() -> &'static [Self::Tile] {
		NumberTile::each(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		NumberTile::each(GameType::Sanma)
	}
}

/// A set specialized to hold [`Tile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile34Set = TileSet<Tile34SetElement>;

assert_size_of!(Tile34Set, 8);

#[derive(Copy, Debug)]
#[derive_const(Clone)]
pub struct Tile34SetElement;

impl const TileSetElement for Tile34SetElement {
	type Tile = Tile;
	const N: usize = 34_usize;

	fn tile_to_offset(tile: Self::Tile) -> u8 {
		(tile as u8) >> 1
	}

	fn offsets_to_tiles() -> &'static [Self::Tile] {
		&t![
			1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
			1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
			1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
			E, S, W, N,
			Wh, G, R,
		]
	}

	fn all_yonma() -> &'static [Self::Tile] {
		Tile::each(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		Tile::each(GameType::Sanma)
	}
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
		*self.present = *self.present & !(0b1 << self.offset) | (u64::from(value) << self.offset);
	}
}

#[cfg(test)]
#[coverage(off)]
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
