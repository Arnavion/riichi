use crate::{
	GameType,
	NumberTile,
	Tile,
};

// Being precise about there being only one of each `FiveRed` and three of each `Five` means that
// we only need ceil(log2(5^31 * 4^3 * 2^3)) = 81 bits to store the whole 37-tile set. However this will require
// lots of divrem by awkward divisors to find each element. It's better to store every count as a separate
// uniformly 3-bit value 0..=4, which makes operations like `TileMultiSetIntoIter::next()`'s search for the next non-zero count
// more convenient and faster.
//
// If we stored 3 bits consecutively, that would require 3 * 37 = 111 bits = 14 bytes.
// If we used a `[u8; 14]`, some 3-bit values cross the u8 boundary which complicates the code and assembly.
//
// If we use a u128 instead, it's easy to shift and extract the count from. However shifts of u128 and
// the multiplication / division by 3 still generates suboptimal assembly for x86_64 and RV64.
//
// So the approach we use is to store the low 2 bits in one `[u16; 5]` array and the high 1 bit in another `[u8; 5]` array.
//
// Another approach is to use an `[(u16, u8); 5]` array, but this ends up needing alignment padding
// between the array elements which increases the size from 10 + 5 + 1 = 16B to 5 * 4 = 20B.
//
// Lastly, the type is parameterized by the functions that map `Tile` to offset and vice versa.
// This allows the same implementation to be used for `Tile27MultiSet`, `Tile34MultiSet` and `Tile37MultiSet`.

/// A multiset specialized to hold [`Tile`]s or [`NumberTile`] in a compact non-allocating representation.
///
/// See the pre-defined aliases [`Tile27MultiSet`], [`Tile34MultiSet`] and [`Tile37MultiSet`].
pub struct TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	counts_lo: [u16; TElement::N],
	counts_hi: [u8; TElement::N],
}

pub const trait TileMultiSetElement {
	type Tile: Copy + core::fmt::Debug + 'static;
	const N: usize;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize);

	fn offsets_to_tiles() -> &'static [Self::Tile];

	fn all_yonma() -> &'static [Self::Tile];

	fn all_sanma() -> &'static [Self::Tile];
}

impl<TElement> TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	pub const fn all(game_type: GameType) -> Self {
		match game_type {
			GameType::Yonma => const { tile_multi_set_all_yonma() },
			GameType::Sanma => const { tile_multi_set_all_sanma() },
		}
	}

	pub const fn is_empty(&self) -> bool {
		*self == Self::default()
	}

	/// Gets the number of occurences of the given tile in this set.
	pub const fn get(&self, tile: TElement::Tile) -> usize {
		self.tile_to_count_ref(tile)
	}

	/// Inserts the given tile into this set.
	///
	/// Returns `false` when inserting more of a tile than should exist.
	pub const fn insert(&mut self, tile: TElement::Tile) -> bool {
		let (mut count, max) = self.tile_to_count_max_mut(tile);
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
	pub const fn remove(&mut self, tile: TElement::Tile) -> bool {
		let (mut count, _) = self.tile_to_count_max_mut(tile);
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
	pub const fn remove_all(&mut self, tile: TElement::Tile) -> usize {
		let (mut count, _) = self.tile_to_count_max_mut(tile);
		let result = count.get();
		count.set(0);
		result
	}

	const fn tile_to_count_ref(&self, tile: TElement::Tile) -> usize {
		let (offset, _) = TElement::tile_to_offset(tile);
		let (offset_i, offset_b) = (offset / 8, offset % 8);
		let offset_i = offset_i as usize;
		let count_lo = (self.counts_lo[offset_i] >> (offset_b * 2)) & 0b11;
		let count_hi = (self.counts_hi[offset_i] >> offset_b) & 0b1;
		(count_hi << 2 | (count_lo as u8)) as usize
	}

	const fn tile_to_count_max_mut(&mut self, tile: TElement::Tile) -> (U3Mut<'_>, usize) {
		let (offset, max) = TElement::tile_to_offset(tile);
		let (offset_i, offset_b) = (offset / 8, offset % 8);
		let offset_i = offset_i as usize;
		(
			U3Mut {
				counts_lo: &mut self.counts_lo[offset_i],
				counts_hi: &mut self.counts_hi[offset_i],
				offset_b,
			},
			max,
		)
	}
}

impl<TElement> const Clone for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	fn clone(&self) -> Self {
		Self {
			counts_lo: self.counts_lo,
			counts_hi: self.counts_hi,
		}
	}
}

impl<TElement> core::fmt::Debug for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
	Self: Clone + IntoIterator<Item = (TElement::Tile, core::num::NonZero<usize>)>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_map().entries(self.clone()).finish()
	}
}

impl<TElement> const Default for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	fn default() -> Self {
		Self {
			counts_lo: [0; TElement::N],
			counts_hi: [0; TElement::N],
		}
	}
}

impl<TElement> FromIterator<TElement::Tile> for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = TElement::Tile> {
		let mut result = Self::default();
		for tile in iter {
			_ = result.insert(tile);
		}
		result
	}
}

impl<TElement> IntoIterator for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
	TileMultiSetIntoIter<TElement>: Iterator,
{
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = TileMultiSetIntoIter<TElement>;

	fn into_iter(self) -> Self::IntoIter {
		TileMultiSetIntoIter {
			counts_lo: self.counts_lo,
			counts_hi: self.counts_hi,
			offset_i: 0,
		}
	}
}

impl<TElement> const PartialEq for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	fn eq(&self, other: &Self) -> bool {
		self.counts_lo == other.counts_lo && self.counts_hi == other.counts_hi
	}
}

impl<TElement> const Eq for TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{}

const fn tile_multi_set_all_yonma<TElement>() -> TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	let tiles = TElement::all_yonma();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileMultiSet::default();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

const fn tile_multi_set_all_sanma<TElement>() -> TileMultiSet<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	let tiles = TElement::all_sanma();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileMultiSet::default();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

pub struct TileMultiSetIntoIter<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	counts_lo: [u16; TElement::N],
	counts_hi: [u8; TElement::N],
	offset_i: u8,
}

impl<TElement> const Clone for TileMultiSetIntoIter<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	fn clone(&self) -> Self {
		Self {
			counts_lo: self.counts_lo,
			counts_hi: self.counts_hi,
			offset_i: self.offset_i,
		}
	}
}

impl<TElement> core::fmt::Debug for TileMultiSetIntoIter<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("TileMultiSetIntoIter").finish_non_exhaustive()
	}
}

impl<TElement> Iterator for TileMultiSetIntoIter<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{
	type Item = (TElement::Tile, core::num::NonZero<usize>);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let counts_lo = self.counts_lo.get_mut(usize::from(self.offset_i))?;
			let counts_hi = &mut self.counts_hi[usize::from(self.offset_i)];

			#[expect(clippy::cast_possible_truncation)]
			let offset_b = {
				let counts_lo_offset = (counts_lo.trailing_zeros() as u8) / 2;
				let counts_hi_offset = counts_hi.trailing_zeros() as u8;
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
			let mut count = U3Mut {
				counts_lo,
				counts_hi,
				offset_b,
			};
			let count_ = count.get();
			count.set(0);
			let count_ = unsafe { core::num::NonZero::new_unchecked(count_) };
			return Some((tile, count_));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		(0, Some((TElement::N - usize::from(self.offset_i)) * 8))
	}
}

impl<TElement> core::iter::FusedIterator for TileMultiSetIntoIter<TElement>
where
	TElement: const TileMultiSetElement,
	[(); TElement::N]:,
{}

/// A multiset specialized to hold [`NumberTile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile27MultiSet = TileMultiSet<Tile27MultiSetElement>;

assert_size_of!(Tile27MultiSet, 12);

#[derive(Copy, Debug)]
#[derive_const(Clone)]
pub struct Tile27MultiSetElement;

impl const TileMultiSetElement for Tile27MultiSetElement {
	type Tile = NumberTile;
	const N: usize = 27_usize.div_ceil(8);

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = (tile as u8) >> 1;
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

	fn all_yonma() -> &'static [Self::Tile] {
		NumberTile::all(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		NumberTile::all(GameType::Sanma)
	}
}

/// A multiset specialized to hold [`Tile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile34MultiSet = TileMultiSet<Tile34MultiSetElement>;

assert_size_of!(Tile34MultiSet, 16);

#[derive(Copy, Debug)]
#[derive_const(Clone)]
pub struct Tile34MultiSetElement;

impl const TileMultiSetElement for Tile34MultiSetElement {
	type Tile = Tile;
	const N: usize = 34_usize.div_ceil(8);

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = (tile as u8) >> 1;
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

	fn all_yonma() -> &'static [Self::Tile] {
		Tile::all(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		Tile::all(GameType::Sanma)
	}
}

/// A multiset specialized to hold [`Tile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as distinct tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile37MultiSet = TileMultiSet<Tile37MultiSetElement>;

assert_size_of!(Tile37MultiSet, 16);

#[derive(Copy, Debug)]
#[derive_const(Clone)]
pub struct Tile37MultiSetElement;

impl const TileMultiSetElement for Tile37MultiSetElement {
	type Tile = Tile;
	const N: usize = 37_usize.div_ceil(8);

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = ((tile as u8) >> 1) + u8::from(tile >= t!(0m)) + u8::from(tile >= t!(0p)) + u8::from(tile >= t!(0s));
		let max = match tile {
			t!(5m | 5p | 5s) => 3,
			t!(0m | 0p | 0s) => 1,
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

	fn all_yonma() -> &'static [Self::Tile] {
		Tile::all(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		Tile::all(GameType::Sanma)
	}
}

struct U3Mut<'a> {
	counts_lo: &'a mut u16,
	counts_hi: &'a mut u8,
	offset_b: u8,
}

impl U3Mut<'_> {
	const fn get(&self) -> usize {
		let count_lo = (*self.counts_lo >> (self.offset_b * 2)) & 0b11;
		let count_hi = (*self.counts_hi >> self.offset_b) & 0b1;
		(count_hi << 2 | (count_lo as u8)) as usize
	}

	#[expect(clippy::cast_possible_truncation)]
	const fn set(&mut self, value: usize) {
		*self.counts_lo = *self.counts_lo & !(0b11 << (self.offset_b * 2)) | (((value & 0b11) as u16) << (self.offset_b * 2));
		*self.counts_hi = *self.counts_hi & !(0b1 << self.offset_b) | ((((value >> 2) & 0b1) as u8) << self.offset_b);
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
		let mut set = Tile27MultiSet::default();

		for &tile in NumberTile::all(GameType::Yonma) {
			assert!(set.insert(tile));
		}
		for &tile in NumberTile::all(GameType::Yonma) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in NumberTile::all(GameType::Yonma).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in NumberTile::all(GameType::Yonma).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in NumberTile::all(GameType::Yonma) {
			assert!(!set.remove(tile));
		}
		assert_eq!(set, Default::default());

		let set: Tile27MultiSet = NumberTile::all(GameType::Yonma).iter().copied().collect();
		assert_eq!(set, Tile27MultiSet::all(GameType::Yonma));
		assert_eq!(
			std::format!("{set:?}"),
			"{1m: 4, 2m: 4, 3m: 4, 4m: 4, 5m: 4, 6m: 4, 7m: 4, 8m: 4, 9m: 4, 1p: 4, 2p: 4, 3p: 4, 4p: 4, 5p: 4, 6p: 4, 7p: 4, 8p: 4, 9p: 4, 1s: 4, 2s: 4, 3s: 4, 4s: 4, 5s: 4, 6s: 4, 7s: 4, 8s: 4, 9s: 4}",
		);

		{
			let mut set = set.clone();

			assert_eq!(set.get(tn!(5m)), 4);
			assert_eq!(set.get(tn!(0m)), 4);

			assert!(!set.insert(tn!(5m)));
			assert_eq!(set.get(tn!(5m)), 4);
			assert_eq!(set.get(tn!(0m)), 4);

			assert!(!set.insert(tn!(0m)));
			assert_eq!(set.get(tn!(5m)), 4);
			assert_eq!(set.get(tn!(0m)), 4);

			assert!(set.remove(tn!(5m)));
			assert_eq!(set.get(tn!(5m)), 3);
			assert_eq!(set.get(tn!(0m)), 3);

			assert!(set.remove(tn!(0m)));
			assert_eq!(set.get(tn!(5m)), 2);
			assert_eq!(set.get(tn!(0m)), 2);
		}

		let total_count: usize = set.clone().into_iter().map(|(_, count)| count.get()).sum();
		assert_eq!(total_count, 108);

		assert!(set.into_iter().flat_map(|(t, n)| core::iter::repeat_n(t, n.get())).eq(NumberTile::all(GameType::Yonma).iter().copied().map(|t| match t {
			tn!(0m) => tn!(5m),
			tn!(0p) => tn!(5p),
			tn!(0s) => tn!(5s),
			t => t,
		})));
	}

	#[test]
	fn all_34() {
		let mut set = Tile34MultiSet::default();

		for &tile in Tile::all(GameType::Yonma) {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::Yonma) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::Yonma).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::Yonma).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::Yonma) {
			assert!(!set.remove(tile));
		}
		assert_eq!(set, Default::default());

		let set: Tile34MultiSet = Tile::all(GameType::Yonma).iter().copied().collect();
		assert_eq!(set, Tile34MultiSet::all(GameType::Yonma));
		assert_eq!(
			std::format!("{set:?}"),
			"{1m: 4, 2m: 4, 3m: 4, 4m: 4, 5m: 4, 6m: 4, 7m: 4, 8m: 4, 9m: 4, 1p: 4, 2p: 4, 3p: 4, 4p: 4, 5p: 4, 6p: 4, 7p: 4, 8p: 4, 9p: 4, 1s: 4, 2s: 4, 3s: 4, 4s: 4, 5s: 4, 6s: 4, 7s: 4, 8s: 4, 9s: 4, E: 4, S: 4, W: 4, N: 4, Wh: 4, G: 4, R: 4}",
		);

		{
			let mut set = set.clone();

			assert_eq!(set.get(t!(5m)), 4);
			assert_eq!(set.get(t!(0m)), 4);

			assert!(!set.insert(t!(5m)));
			assert_eq!(set.get(t!(5m)), 4);
			assert_eq!(set.get(t!(0m)), 4);

			assert!(!set.insert(t!(0m)));
			assert_eq!(set.get(t!(5m)), 4);
			assert_eq!(set.get(t!(0m)), 4);

			assert!(set.remove(t!(5m)));
			assert_eq!(set.get(t!(5m)), 3);
			assert_eq!(set.get(t!(0m)), 3);

			assert!(set.remove(t!(0m)));
			assert_eq!(set.get(t!(5m)), 2);
			assert_eq!(set.get(t!(0m)), 2);
		}

		let total_count: usize = set.clone().into_iter().map(|(_, count)| count.get()).sum();
		assert_eq!(total_count, 136);

		assert!(set.into_iter().flat_map(|(t, n)| core::iter::repeat_n(t, n.get())).eq(Tile::all(GameType::Yonma).iter().copied().map(|t| match t {
			t!(0m) => t!(5m),
			t!(0p) => t!(5p),
			t!(0s) => t!(5s),
			t => t,
		})));
	}

	#[test]
	fn all_37() {
		let mut set = Tile37MultiSet::default();

		for &tile in Tile::all(GameType::Yonma) {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::Yonma) {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::Yonma).iter().rev() {
			assert!(set.insert(tile));
		}
		for &tile in Tile::all(GameType::Yonma).iter().rev() {
			assert!(set.remove(tile));
		}
		assert_eq!(set, Default::default());

		for &tile in Tile::all(GameType::Yonma) {
			assert!(!set.remove(tile));
		}
		assert_eq!(set, Default::default());

		let set: Tile37MultiSet = Tile::all(GameType::Yonma).iter().copied().collect();
		assert_eq!(set, Tile37MultiSet::all(GameType::Yonma));
		assert_eq!(
			std::format!("{set:?}"),
			"{1m: 4, 2m: 4, 3m: 4, 4m: 4, 5m: 3, 0m: 1, 6m: 4, 7m: 4, 8m: 4, 9m: 4, 1p: 4, 2p: 4, 3p: 4, 4p: 4, 5p: 3, 0p: 1, 6p: 4, 7p: 4, 8p: 4, 9p: 4, 1s: 4, 2s: 4, 3s: 4, 4s: 4, 5s: 3, 0s: 1, 6s: 4, 7s: 4, 8s: 4, 9s: 4, E: 4, S: 4, W: 4, N: 4, Wh: 4, G: 4, R: 4}",
		);

		{
			let mut set = set.clone();

			assert_eq!(set.get(t!(5m)), 3);
			assert_eq!(set.get(t!(0m)), 1);

			assert!(!set.insert(t!(5m)));
			assert_eq!(set.get(t!(5m)), 3);
			assert_eq!(set.get(t!(0m)), 1);

			assert!(!set.insert(t!(0m)));
			assert_eq!(set.get(t!(5m)), 3);
			assert_eq!(set.get(t!(0m)), 1);

			assert!(set.remove(t!(5m)));
			assert_eq!(set.get(t!(5m)), 2);
			assert_eq!(set.get(t!(0m)), 1);

			assert!(set.remove(t!(0m)));
			assert_eq!(set.get(t!(5m)), 2);
			assert_eq!(set.get(t!(0m)), 0);
		}

		let total_count: usize = set.clone().into_iter().map(|(_, count)| count.get()).sum();
		assert_eq!(total_count, 136);

		assert!(set.into_iter().flat_map(|(t, n)| core::iter::repeat_n(t, n.get())).eq(Tile::all(GameType::Yonma).iter().copied()));
	}
}
