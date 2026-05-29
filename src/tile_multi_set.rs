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
// So we use a `u128`.
//
// Lastly, the type is parameterized by the functions that map `Tile` to offset and vice versa.
// This allows the same implementation to be used for `Tile27MultiSet`, `Tile34MultiSet` and `Tile37MultiSet`.

/// A multiset specialized to hold [`Tile`]s or [`NumberTile`] in a compact non-allocating representation.
///
/// See the pre-defined aliases [`Tile27MultiSet`], [`Tile34MultiSet`] and [`Tile37MultiSet`].
pub struct TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	counts: u128,
	element: core::marker::PhantomData<TElement>,
}

pub trait TileMultiSetElement {
	type Tile: Copy + core::fmt::Debug + 'static;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize);

	fn offset_to_tile(offset: u8) -> Option<Self::Tile>;

	fn all_yonma() -> &'static [Self::Tile];

	fn all_sanma() -> &'static [Self::Tile];
}

impl<TElement> TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	pub const fn new() -> Self {
		Self {
			counts: 0,
			element: core::marker::PhantomData,
		}
	}

	pub fn all(game_type: GameType) -> Self {
		match game_type {
			GameType::Yonma => tile_multi_set_all_yonma(),
			GameType::Sanma => tile_multi_set_all_sanma(),
		}
	}

	#[expect(clippy::cast_possible_truncation)]
	pub const fn is_empty(&self) -> bool {
		// Micro-optimization: `self.counts == 0` compiles correctly to the equivalent ASM of
		// `(counts as u64) | ((counts >> 64) as u64) == 0` on x86_64 and RV,
		// but on RVV it compiles to an extremely silly sequence:
		//
		// ```asm
		// vsetivli        zero, 16, e8, m1, ta, ma
		// vle8.v  v8, (a0)
		// vsetivli        zero, 2, e64, m1, ta, ma
		// vmv.v.i v9, 0
		// vsetivli        zero, 16, e8, m1, ta, ma
		// vmsne.vv        v8, v8, v9
		// vcpop.m a0, v8
		// seqz    a0, a0
		// ret
		// ```
		//
		// This is with rustc nightly using LLVM 22.1.8. With LLVM main, the `vmsne` is at least fixed to use an immediate
		// `vmsne.vi v8, v8, 0` to obviate the middle three instructions for preparing a zero vector, but it's still bad
		// compared to the scalar version.
		//
		// So implement the scalar version manually.
		(self.counts as u64) | ((self.counts >> 64) as u64) == 0
	}
}

impl<TElement> TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	/// Gets the number of occurences of the given tile in this set.
	pub fn get(&self, tile: TElement::Tile) -> usize {
		self.tile_to_count_ref(tile)
	}

	/// Inserts the given tile into this set.
	///
	/// Returns `false` when inserting more of a tile than should exist.
	pub fn insert(&mut self, tile: TElement::Tile) -> bool {
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

	/// Inserts the given tile into this set.
	///
	/// Returns `false` when inserting more of a tile than should exist.
	pub fn insert_many(&mut self, tile: TElement::Tile, additional: usize) -> bool {
		let (mut count, max) = self.tile_to_count_max_mut(tile);
		let new_count = count.get().saturating_add(additional);
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
		let (mut count, _) = self.tile_to_count_max_mut(tile);
		if let Some(new_count) = count.get().checked_sub(1) {
			count.set(new_count);
			true
		}
		else {
			false
		}
	}

	/// Removes all instances of the given tile from this set.
	///
	/// Returns the number of instances removed.
	pub fn remove_all(&mut self, tile: TElement::Tile) -> usize {
		let (mut count, _) = self.tile_to_count_max_mut(tile);
		let result = count.get();
		count.set(0);
		result
	}

	fn tile_to_count_ref(&self, tile: TElement::Tile) -> usize {
		let (offset, _) = TElement::tile_to_offset(tile);
		let count = (self.counts >> (offset * 3)) & 0b111;
		count as usize
	}

	fn tile_to_count_max_mut(&mut self, tile: TElement::Tile) -> (U3Mut<'_>, usize) {
		let (offset, max) = TElement::tile_to_offset(tile);
		(
			U3Mut {
				counts: &mut self.counts,
				offset,
			},
			max,
		)
	}
}

impl<TElement> Clone for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	fn clone(&self) -> Self {
		Self {
			counts: self.counts,
			element: self.element,
		}
	}
}

impl<TElement> core::fmt::Debug for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
	Self: Clone + IntoIterator<Item = (TElement::Tile, core::num::NonZero<usize>)>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_map().entries(self.clone()).finish()
	}
}

impl<TElement> Default for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	fn default() -> Self {
		Self::new()
	}
}

impl<TElement> FromIterator<(TElement::Tile, usize)> for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = (TElement::Tile, usize)> {
		let mut result = Self::new();
		for (tile, additional) in iter {
			_ = result.insert_many(tile, additional);
		}
		result
	}
}

impl<TElement> IntoIterator for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
	TileMultiSetIntoIter<TElement>: Iterator,
{
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = TileMultiSetIntoIter<TElement>;

	fn into_iter(self) -> Self::IntoIter {
		TileMultiSetIntoIter {
			counts: self.counts,
			element: self.element,
		}
	}
}

impl<TElement> PartialEq for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	fn eq(&self, other: &Self) -> bool {
		self.counts == other.counts
	}
}

impl<TElement> Eq for TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{}

fn tile_multi_set_all_yonma<TElement>() -> TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	let tiles = TElement::all_yonma();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileMultiSet::new();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

fn tile_multi_set_all_sanma<TElement>() -> TileMultiSet<TElement>
where
	TElement: TileMultiSetElement,
{
	let tiles = TElement::all_sanma();

	// This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`
	let mut result = TileMultiSet::new();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}

	result
}

pub struct TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{
	counts: u128,
	element: core::marker::PhantomData<TElement>,
}

impl<TElement> TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{
	fn next_inner(&mut self, offset: u32) -> Option<(TElement::Tile, core::num::NonZero<usize>)> {
		#[expect(clippy::cast_possible_truncation)]
		let offset = (offset / 3) as u8;
		let tile = TElement::offset_to_tile(offset)?;
		let mut count = U3Mut { counts: &mut self.counts, offset };
		let count_ = count.get();
		count.set(0);
		let count_ = unsafe { core::num::NonZero::new_unchecked(count_) };
		Some((tile, count_))
	}
}

impl<TElement> Clone for TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{
	fn clone(&self) -> Self {
		Self {
			counts: self.counts,
			element: self.element,
		}
	}
}

impl<TElement> core::fmt::Debug for TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("TileMultiSetIntoIter").finish_non_exhaustive()
	}
}

impl<TElement> Iterator for TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{
	type Item = (TElement::Tile, core::num::NonZero<usize>);

	fn next(&mut self) -> Option<Self::Item> {
		self.next_inner(self.counts.lowest_one()?)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.counts == 0 {
			(0, Some(0))
		}
		else {
			(1, Some(37))
		}
	}
}

impl<TElement> DoubleEndedIterator for TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		self.next_inner(self.counts.highest_one()?)
	}
}

impl<TElement> core::iter::FusedIterator for TileMultiSetIntoIter<TElement>
where
	TElement: TileMultiSetElement,
{}

/// A multiset specialized to hold [`NumberTile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`get`](Self::get), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile27MultiSet = TileMultiSet<Tile27MultiSetElement>;

assert_size_of!(Tile27MultiSet, 16);

#[derive(Clone, Copy, Debug)]
pub struct Tile27MultiSetElement;

impl TileMultiSetElement for Tile27MultiSetElement {
	type Tile = NumberTile;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = (tile as u8) >> 1;
		let max = 4;
		(offset, max)
	}

	fn offset_to_tile(offset: u8) -> Option<Self::Tile> {
		let offset = offset << 1;
		if offset <= t!(9s) as u8 {
			Some(unsafe { core::mem::transmute::<u8, NumberTile>(offset) })
		}
		else {
			None
		}
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

#[derive(Clone, Copy, Debug)]
pub struct Tile34MultiSetElement;

impl TileMultiSetElement for Tile34MultiSetElement {
	type Tile = Tile;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = (tile as u8) >> 1;
		let max = 4;
		(offset, max)
	}

	fn offset_to_tile(offset: u8) -> Option<Self::Tile> {
		let offset = offset << 1;
		if offset <= t!(R) as u8 {
			Some(unsafe { core::mem::transmute::<u8, Tile>(offset) })
		}
		else {
			None
		}
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

#[derive(Clone, Copy, Debug)]
pub struct Tile37MultiSetElement;

impl TileMultiSetElement for Tile37MultiSetElement {
	type Tile = Tile;

	fn tile_to_offset(tile: Self::Tile) -> (u8, usize) {
		let offset = ((tile as u8) >> 1) + 3 - u8::from(tile < t!(0m)) - u8::from(tile < t!(0p)) - u8::from(tile < t!(0s));
		let max = match tile {
			t!(5m | 5p | 5s) => 3,
			t!(0m | 0p | 0s) => 1,
			_ => 4,
		};
		(offset, max)
	}

	fn offset_to_tile(offset: u8) -> Option<Self::Tile> {
		if offset < 37 {
			let tile = offset - u8::from(offset >= 5) - u8::from(offset >= 15) - u8::from(offset >= 25);
			let tile = (tile << 1) | u8::from(offset == 5 || offset == 15 || offset == 25);
			Some(unsafe { core::mem::transmute::<u8, Tile>(tile) })
		}
		else {
			None
		}
	}

	fn all_yonma() -> &'static [Self::Tile] {
		Tile::all(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		Tile::all(GameType::Sanma)
	}
}

struct U3Mut<'a> {
	counts: &'a mut u128,
	offset: u8,
}

impl U3Mut<'_> {
	const fn get(&self) -> usize {
		let count = (*self.counts >> (self.offset * 3)) & 0b111;
		count as usize
	}

	const fn set(&mut self, value: usize) {
		*self.counts = *self.counts & !(0b111 << (self.offset * 3)) | (((value & 0b111) as u128) << (self.offset * 3));
	}
}

impl Tile34MultiSet {
	/// Treats this `Tile34MultiSet` as containing dora indicators, and returns a new `Tile34MultiSet` containing the corresponding dora.
	pub fn indicates_dora(&self, game_type: GameType) -> Self {
		const MASK_MAN_YONMA: u128 = 0b000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_111_111_111_111_111_111_111_111;
		const MASK_MAN_SANMA: u128 = 0b000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_111;
		const MASK_NEXT: u128 =      0b000_111_111_000_111_111_111_000_111_111_111_111_111_111_111_111_000_111_111_111_111_111_111_111_111_000_000_000_000_000_000_000_000_000;
		const MASK_9X: u128 =        0b000_000_000_000_000_000_000_111_000_000_000_000_000_000_000_000_111_000_000_000_000_000_000_000_000_111_000_000_000_000_000_000_000_000;
		const MASK_N: u128 =         0b000_000_000_111_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000;
		const MASK_R: u128 =         0b111_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000;

		let Self { counts, element } = self;

		let counts =
			match game_type {
				GameType::Yonma => (counts & MASK_MAN_YONMA) << 3,
				GameType::Sanma => (counts & MASK_MAN_SANMA) << 24,
			} |
			((counts & MASK_NEXT) << 3) |
			((counts & MASK_9X) >> 24) |
			((counts & MASK_N) >> 9) |
			((counts & MASK_R) >> 6);

		Self { counts, element: *element }
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

	use crate::GameType;
	use super::*;

	#[test]
	fn all_27() {
		let mut set = Tile27MultiSet::new();

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

		let set: Tile27MultiSet = NumberTile::all(GameType::Yonma).iter().copied().map(|t| (t, 1)).collect();
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
		let mut set = Tile34MultiSet::new();

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

		let set: Tile34MultiSet = Tile::all(GameType::Yonma).iter().copied().map(|t| (t, 1)).collect();
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
		let mut set = Tile37MultiSet::new();

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

		let set: Tile37MultiSet = Tile::all(GameType::Yonma).iter().copied().map(|t| (t, 1)).collect();
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

	#[test]
	fn indicates_dora() {
		for (input, expected_yonma, expected_sanma) in [
			(t!(1m), t!(2m), Some(t!(9m))),
			(t!(2m), t!(3m), None),
			(t!(3m), t!(4m), None),
			(t!(4m), t!(5m), None),
			(t!(5m), t!(6m), None),
			(t!(0m), t!(6m), None),
			(t!(6m), t!(7m), None),
			(t!(7m), t!(8m), None),
			(t!(8m), t!(9m), None),
			(t!(9m), t!(1m), Some(t!(1m))),
			(t!(1p), t!(2p), Some(t!(2p))),
			(t!(2p), t!(3p), Some(t!(3p))),
			(t!(3p), t!(4p), Some(t!(4p))),
			(t!(4p), t!(5p), Some(t!(5p))),
			(t!(5p), t!(6p), Some(t!(6p))),
			(t!(0p), t!(6p), Some(t!(6p))),
			(t!(6p), t!(7p), Some(t!(7p))),
			(t!(7p), t!(8p), Some(t!(8p))),
			(t!(8p), t!(9p), Some(t!(9p))),
			(t!(9p), t!(1p), Some(t!(1p))),
			(t!(1s), t!(2s), Some(t!(2s))),
			(t!(2s), t!(3s), Some(t!(3s))),
			(t!(3s), t!(4s), Some(t!(4s))),
			(t!(4s), t!(5s), Some(t!(5s))),
			(t!(5s), t!(6s), Some(t!(6s))),
			(t!(0s), t!(6s), Some(t!(6s))),
			(t!(6s), t!(7s), Some(t!(7s))),
			(t!(7s), t!(8s), Some(t!(8s))),
			(t!(8s), t!(9s), Some(t!(9s))),
			(t!(9s), t!(1s), Some(t!(1s))),
			(t!(E), t!(S), Some(t!(S))),
			(t!(S), t!(W), Some(t!(W))),
			(t!(W), t!(N), Some(t!(N))),
			(t!(N), t!(E), Some(t!(E))),
			(t!(Wh), t!(G), Some(t!(G))),
			(t!(G), t!(R), Some(t!(R))),
			(t!(R), t!(Wh), Some(t!(Wh))),
		] {
			let input = [(input, 4)].into_iter().collect::<Tile34MultiSet>();

			let actual = input.indicates_dora(GameType::Yonma);
			let expected_yonma = [(expected_yonma, 4)].into_iter().collect::<Tile34MultiSet>();
			assert_eq!(actual, expected_yonma);

			let actual = input.indicates_dora(GameType::Sanma);
			let expected_sanma = expected_sanma.map(|t| (t, 4)).into_iter().collect::<Tile34MultiSet>();
			assert_eq!(actual, expected_sanma);
		}
	}
}
