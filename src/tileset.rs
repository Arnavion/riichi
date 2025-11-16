use generic_array::{
	ArrayLength,
	GenericArray,
	typenum,
};

use crate::{
	GameType,
	NumberTile,
	Tile,
};

// Being precise about there being only one of each `FiveRed` and three of each `Five` means that
// we only need ceil(log2(5^31 * 4^3 * 2^3)) = 81 bits to store the whole 37-tile set. However this will require
// lots of divrem by awkward divisors to find each element. It's better to store every count as a separate
// uniformly 3-bit value 0..=4, which makes operations like `TileSetIntoIter::next()`'s search for the next non-zero count
// more convenient and faster.
//
// If we stored 3 bits consecutively, that would require 3 * 37 = 111 bits = 14 bytes.
// If we used a `[u8; 14]`, some 3-bit values cross the u8 boundary which complicates the code and assembly.
//
// If we use a u128 instead, it's easy to shift and extract the count from. However shifts of u128 and
// the multiplication / division by 3 still generates suboptimal assembly for x86_64 and RV64.
//
// So the approach we use is to store the low 2 bits in one `[U2x8; 5]` array and the high 1 bit in another `[U1x8; 5]` array.
//
// Another approach is to use an `[(U2x8, U1x8); 5]` array, but this ends up needing alignment padding
// between the array elements which increases the size from 10 + 5 + 1 = 16B to 5 * 4 = 20B.
//
// Lastly, the type is parameterized by the functions that map `Tile` to offset and vice versa.
// This allows the same implementation to be used for `TileSet27`, `TileSet34` and `TileSet37`.

/// A multiset specialized to hold [`Tile`]s or [`NumberTile`] in a compact non-allocating representation.
///
/// Don't use this type directly. Instead use the pre-defined aliases [`TileSet27`], [`TileSet34`] and [`TileSet37`].
pub struct TileSet<TElement>
where
	TElement: TileSetElement,
{
	counts_lo: GenericArray<U2x8, TElement::N>,
	counts_hi: GenericArray<U1x8, TElement::N>,
}

pub trait TileSetElement {
	type N: ArrayLength;
	type Tile: Copy + std::fmt::Debug + 'static;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize);

	fn offsets_to_tiles() -> &'static [Self::Tile];

	fn all_four_player() -> &'static [Self::Tile];

	fn all_three_player() -> &'static [Self::Tile];
}

impl<TElement> TileSet<TElement>
where
	TElement: TileSetElement,
	GenericArray<U2x8, TElement::N>: const_default::ConstDefault,
	GenericArray<U1x8, TElement::N>: const_default::ConstDefault,
{
	pub const fn new() -> Self {
		Self {
			counts_lo: GenericArray::const_default(),
			counts_hi: GenericArray::const_default(),
		}
	}

	pub fn all(game_type: GameType) -> Self {
		match game_type {
			GameType::FourPlayer => tileset_all_four_player(),
			GameType::ThreePlayer => tileset_all_three_player(),
		}
	}

	pub fn is_empty(&self) -> bool {
		*self == Self::new()
	}
}

impl<TElement> TileSet<TElement>
where
	TElement: TileSetElement,
{
	/// Gets the number of occurences of the given tile in this set.
	pub fn get(&self, tile: TElement::Tile) -> usize {
		tile_to_count_ref::<TElement>(tile, &self.counts_lo, &self.counts_hi)
	}

	/// Inserts the given tile into this set.
	///
	/// Returns `false` when inserting more of a tile than should exist.
	pub fn insert(&mut self, tile: TElement::Tile) -> bool {
		let (mut count, max) = tile_to_count_max_mut::<TElement>(tile, &mut self.counts_lo, &mut self.counts_hi);
		let new_count = count.get() + 1;
		if new_count <= max {
			count.set(new_count);
			true
		}
		else {
			false
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
	pub fn remove(&mut self, tile: TElement::Tile) -> bool {
		let (mut count, _) = tile_to_count_max_mut::<TElement>(tile, &mut self.counts_lo, &mut self.counts_hi);
		match count.get().checked_sub(1) {
			Some(new_count) => {
				count.set(new_count);
				true
			},
			None => false,
		}
	}

	/// Removes all instances of the given tile from this set.
	///
	/// Returns the number of instances removed.
	pub fn remove_all(&mut self, tile: TElement::Tile) -> usize {
		let (mut count, _) = tile_to_count_max_mut::<TElement>(tile, &mut self.counts_lo, &mut self.counts_hi);
		let result = count.get();
		count.set(0);
		result
	}
}

impl<TElement> Clone for TileSet<TElement>
where
	TElement: TileSetElement,
	GenericArray<U2x8, TElement::N>: Clone,
	GenericArray<U1x8, TElement::N>: Clone,
{
	fn clone(&self) -> Self {
		Self {
			counts_lo: self.counts_lo.clone(),
			counts_hi: self.counts_hi.clone(),
		}
	}
}

impl<TElement> std::fmt::Debug for TileSet<TElement>
where
	TElement: TileSetElement,
	Self: Clone + IntoIterator<Item = (TElement::Tile, std::num::NonZero<usize>)>,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_map().entries(self.clone()).finish()
	}
}

impl<TElement> Default for TileSet<TElement>
where
	TElement: TileSetElement,
	GenericArray<U2x8, TElement::N>: const_default::ConstDefault,
	GenericArray<U1x8, TElement::N>: const_default::ConstDefault,
{
	fn default() -> Self {
		Self::new()
	}
}

impl<TElement> FromIterator<TElement::Tile> for TileSet<TElement>
where
	TElement: TileSetElement,
	GenericArray<U2x8, TElement::N>: const_default::ConstDefault,
	GenericArray<U1x8, TElement::N>: const_default::ConstDefault,
{
	fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = TElement::Tile> {
		let mut result = Self::new();
		result.try_extend(iter).unwrap();
		result
	}
}

impl<TElement> IntoIterator for TileSet<TElement>
where
	TElement: TileSetElement,
	TileSetIntoIter<TElement>: Iterator,
{
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = TileSetIntoIter<TElement>;

	fn into_iter(self) -> Self::IntoIter {
		TileSetIntoIter {
			counts_lo: self.counts_lo,
			counts_hi: self.counts_hi,
			offset_i: 0,
		}
	}
}

impl<TElement> PartialEq for TileSet<TElement>
where
	TElement: TileSetElement,
{
	fn eq(&self, other: &Self) -> bool {
		self.counts_lo == other.counts_lo && self.counts_hi == other.counts_hi
	}
}

impl<TElement> Eq for TileSet<TElement>
where
	TElement: TileSetElement,
{}

fn tileset_all_four_player<TElement>() -> TileSet<TElement>
where
	TElement: TileSetElement,
	GenericArray<U2x8, TElement::N>: const_default::ConstDefault,
	GenericArray<U1x8, TElement::N>: const_default::ConstDefault,
{
	let tiles = TElement::all_four_player();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileSet::new();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

fn tileset_all_three_player<TElement>() -> TileSet<TElement>
where
	TElement: TileSetElement,
	GenericArray<U2x8, TElement::N>: const_default::ConstDefault,
	GenericArray<U1x8, TElement::N>: const_default::ConstDefault,
{
	let tiles = TElement::all_three_player();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileSet::new();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

pub struct TileSetIntoIter<TElement>
where
	TElement: TileSetElement,
{
	counts_lo: GenericArray<U2x8, TElement::N>,
	counts_hi: GenericArray<U1x8, TElement::N>,
	offset_i: u8,
}

impl<TElement> std::fmt::Debug for TileSetIntoIter<TElement>
where
	TElement: TileSetElement,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("TileSetIntoIter").finish_non_exhaustive()
	}
}

impl<TElement> Iterator for TileSetIntoIter<TElement>
where
	TElement: TileSetElement,
{
	type Item = (TElement::Tile, std::num::NonZero<usize>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let counts_lo = self.counts_lo.get_mut(usize::from(self.offset_i))?;
			let counts_hi = &mut self.counts_hi[usize::from(self.offset_i)];

			#[expect(clippy::cast_possible_truncation)]
			let offset_b = {
				let counts_lo_offset = (counts_lo.0.trailing_zeros() as u8) / 2;
				let counts_hi_offset = counts_hi.0.trailing_zeros() as u8;
				counts_lo_offset.min(counts_hi_offset)
			};
			if offset_b == 8 {
				self.offset_i += 1;
				continue;
			}

			let tile = {
				let offset = self.offset_i * 8 + offset_b;
				*TElement::offsets_to_tiles().get(usize::from(offset))?
			};
			let mut count = U3x8Mut {
				counts_lo,
				counts_hi,
				offset_b,
			};
			let count_ = count.get();
			count.set(0);
			let count_ = unsafe { std::num::NonZero::new_unchecked(count_) };
			return Some((tile, count_));
		}
	}
}

/// A multiset specialized to hold [`NumberTile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type TileSet27 = TileSet<TileSetElement27>;

assert_size_of!(TileSet27, 12);

#[derive(Clone, Copy)]
pub struct TileSetElement27;

impl TileSetElement for TileSetElement27 {
	type Tile = NumberTile;
	type N = typenum::U<{ 27_usize.div_ceil(8) }>;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = match tile {
			tn!(1m | 2m | 3m | 4m | 5m) => tile as u8,
			tn!(0m | 6m | 7m | 8m | 9m | 1p | 2p | 3p | 4p | 5p) => tile as u8 - 1,
			tn!(0p | 6p | 7p | 8p | 9p | 1s | 2s | 3s | 4s | 5s) => tile as u8 - 2,
			tn!(0s | 6s | 7s | 8s | 9s) => tile as u8 - 3,
		};

		let max = 4;

		(offset, max)
	}

	fn offsets_to_tiles() -> &'static [Self::Tile] {
		&tn![
			1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
			1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
			1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
		]
	}

	fn all_four_player() -> &'static [Self::Tile] {
		NumberTile::all(GameType::FourPlayer)
	}

	fn all_three_player() -> &'static [Self::Tile] {
		NumberTile::all(GameType::ThreePlayer)
	}
}

/// A multiset specialized to hold [`Tile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type TileSet34 = TileSet<TileSetElement34>;

assert_size_of!(TileSet34, 16);

#[derive(Clone, Copy)]
pub struct TileSetElement34;

impl TileSetElement for TileSetElement34 {
	type Tile = Tile;
	type N = typenum::U<{ 34_usize.div_ceil(8) }>;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = match tile {
			t!(1m | 2m | 3m | 4m | 5m) => tile as u8,
			t!(0m | 6m | 7m | 8m | 9m | 1p | 2p | 3p | 4p | 5p) => tile as u8 - 1,
			t!(0p | 6p | 7p | 8p | 9p | 1s | 2s | 3s | 4s | 5s) => tile as u8 - 2,
			t!(0s | 6s | 7s | 8s | 9s | E | S | W | N | Wh | G | R) => tile as u8 - 3,
		};

		let max = 4;

		(offset, max)
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

	fn all_four_player() -> &'static [Self::Tile] {
		Tile::all(GameType::FourPlayer)
	}

	fn all_three_player() -> &'static [Self::Tile] {
		Tile::all(GameType::ThreePlayer)
	}
}

/// A multiset specialized to hold [`Tile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as distinct tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type TileSet37 = TileSet<TileSetElement37>;

assert_size_of!(TileSet37, 16);

#[derive(Clone, Copy)]
pub struct TileSetElement37;

impl TileSetElement for TileSetElement37 {
	type Tile = Tile;
	type N = typenum::U<{ 37_usize.div_ceil(8) }>;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = tile as u8;

		let max = match tile {
			t!(5m) | t!(5p) | t!(5s) => 3,
			t!(0m) | t!(0p) | t!(0s) => 1,
			_ => 4,
		};

		(offset, max)
	}

	fn offsets_to_tiles() -> &'static [Self::Tile] {
		&t![
			1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m,
			1p, 2p, 3p, 4p, 5p, 0p, 6p, 7p, 8p, 9p,
			1s, 2s, 3s, 4s, 5s, 0s, 6s, 7s, 8s, 9s,
			E, S, W, N,
			Wh, G, R,
		]
	}

	fn all_four_player() -> &'static [Self::Tile] {
		Tile::all(GameType::FourPlayer)
	}

	fn all_three_player() -> &'static [Self::Tile] {
		Tile::all(GameType::ThreePlayer)
	}
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct U1x8(u8);

#[derive(Clone, Copy, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct U2x8(u16);

impl const_default::ConstDefault for U1x8 {
	const DEFAULT: Self = Self(0);
}

impl const_default::ConstDefault for U2x8 {
	const DEFAULT: Self = Self(0);
}

fn tile_to_count_ref<TElement>(
	tile: TElement::Tile,
	counts_lo: &GenericArray<U2x8, TElement::N>,
	counts_hi: &GenericArray<U1x8, TElement::N>,
) -> usize
where
	TElement: TileSetElement,
{
	let (offset, _) = TElement::tile_to_offset(tile);
	let (offset_i, offset_b) = (offset / 8, offset % 8);
	let offset_i = offset_i as usize;
	let count_lo = (counts_lo.as_slice()[offset_i].0 >> (offset_b * 2)) & 0b11;
	let count_hi = (counts_hi.as_slice()[offset_i].0 >> offset_b) & 0b1;
	(count_hi << 2 | (count_lo as u8)) as usize
}

fn tile_to_count_max_mut<'a, TElement>(
	tile: TElement::Tile,
	counts_lo: &'a mut GenericArray<U2x8, TElement::N>,
	counts_hi: &'a mut GenericArray<U1x8, TElement::N>,
) -> (U3x8Mut<'a>, usize)
where
	TElement: TileSetElement,
{
	let (offset, max) = TElement::tile_to_offset(tile);
	let (offset_i, offset_b) = (offset / 8, offset % 8);
	let offset_i = offset_i as usize;
	(
		U3x8Mut {
			counts_lo: &mut counts_lo.as_mut_slice()[offset_i],
			counts_hi: &mut counts_hi.as_mut_slice()[offset_i],
			offset_b,
		},
		max,
	)
}

struct U3x8Mut<'a> {
	counts_lo: &'a mut U2x8,
	counts_hi: &'a mut U1x8,
	offset_b: u8,
}

impl U3x8Mut<'_> {
	const fn get(&self) -> usize {
		let count_lo = (self.counts_lo.0 >> (self.offset_b * 2)) & 0b11;
		let count_hi = (self.counts_hi.0 >> self.offset_b) & 0b1;
		(count_hi << 2 | (count_lo as u8)) as usize
	}

	#[expect(clippy::cast_possible_truncation)]
	const fn set(&mut self, value: usize) {
		self.counts_lo.0 = self.counts_lo.0 & !(0b11 << (self.offset_b * 2)) | (((value & 0b11) as u16) << (self.offset_b * 2));
		self.counts_hi.0 = self.counts_hi.0 & !(0b1 << self.offset_b) | ((((value >> 2) & 0b1) as u8) << self.offset_b);
	}
}

#[cfg(test)]
mod tests {
	use crate::GameType;
	use super::*;

	#[test]
	fn all_27() {
		let mut set = TileSet27::new();

		for &tile in NumberTile::all(GameType::FourPlayer) {
			assert!(set.insert(tile));
		}
		for &tile in NumberTile::all(GameType::FourPlayer) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in NumberTile::all(GameType::FourPlayer).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in NumberTile::all(GameType::FourPlayer).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in NumberTile::all(GameType::FourPlayer) {
			assert!(!set.remove(tile));
		}

		let set: TileSet27 = NumberTile::all(GameType::FourPlayer).iter().copied().collect();
		assert_eq!(set, TileSet27::all(GameType::FourPlayer));
		for (tile, count) in set.clone() {
			print!("{tile}: {}, ", count.get());
		}
		println!();

		let total_count: usize = set.clone().into_iter().map(|(_, count)| count.get()).sum();
		assert_eq!(total_count, 108);

		assert!(set.into_iter().flat_map(|(t, n)| std::iter::repeat_n(t, n.get())).eq(NumberTile::all(GameType::FourPlayer).iter().copied()));
	}

	#[test]
	fn all_34() {
		let mut set = TileSet34::new();

		for &tile in Tile::all(GameType::FourPlayer) {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::FourPlayer) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::FourPlayer).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::FourPlayer).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::FourPlayer) {
			assert!(!set.remove(tile));
		}

		let set: TileSet34 = Tile::all(GameType::FourPlayer).iter().copied().collect();
		assert_eq!(set, TileSet34::all(GameType::FourPlayer));
		for (tile, count) in set.clone() {
			print!("{tile}: {}, ", count.get());
		}
		println!();

		let total_count: usize = set.clone().into_iter().map(|(_, count)| count.get()).sum();
		assert_eq!(total_count, 136);

		assert!(set.into_iter().flat_map(|(t, n)| std::iter::repeat_n(t, n.get())).eq(Tile::all(GameType::FourPlayer).iter().copied()));
	}

	#[test]
	fn all_37() {
		let mut set = TileSet37::new();

		for &tile in Tile::all(GameType::FourPlayer) {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::FourPlayer) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::FourPlayer).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::FourPlayer).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::FourPlayer) {
			assert!(!set.remove(tile));
		}

		let set: TileSet37 = Tile::all(GameType::FourPlayer).iter().copied().collect();
		assert_eq!(set, TileSet37::all(GameType::FourPlayer));
		for (tile, count) in set.clone() {
			print!("{tile}: {}, ", count.get());
		}
		println!();

		let total_count: usize = set.clone().into_iter().map(|(_, count)| count.get()).sum();
		assert_eq!(total_count, 136);

		assert!(set.into_iter().flat_map(|(t, n)| std::iter::repeat_n(t, n.get())).eq(Tile::all(GameType::FourPlayer).iter().copied()));
	}
}
