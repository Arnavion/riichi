use crate::{
	GameType,
	NumberTile,
	Tile, Tile27, Tile34, Tile34MultiSet, Tile37, Tile37MultiSet,
};

/// A set specialized to hold [`Tile`]s or [`NumberTile`] in a compact non-allocating representation.
///
/// See the pre-defined aliases [`Tile27Set`], [`Tile34Set`] and [`Tile37Set`].
pub struct TileSet<TKind> {
	pub(crate) present: u64,
	kind: core::marker::PhantomData<TKind>,
}

/// Parameter for [`TileSet`] to control what type of tiles it holds.
pub const trait Kind {
	type Tile: Copy + core::fmt::Debug + 'static;
	const N: usize;

	fn tile_to_offset(tile: Self::Tile) -> u8;

	/// # Safety
	///
	/// `offset` must be a valid value that corresponds to a `Tile`.
	unsafe fn offset_to_tile(offset: u8) -> Self::Tile;

	fn all_yonma() -> &'static [Self::Tile];

	fn all_sanma() -> &'static [Self::Tile];
}

impl<TKind> TileSet<TKind>
where
	TKind: const Kind,
{
	/// Create a `TileSet` that contains all the tiles that exist in the given game type.
	pub const fn all(game_type: GameType) -> Self {
		// `const {}` wrapper is required, otherwise rustc emits construction code instead of a literal.
		match game_type {
			GameType::Yonma => const { make_tile_set(TKind::all_yonma()) },
			GameType::Sanma => const { make_tile_set(TKind::all_sanma()) },
		}
	}

	/// Returns `true` if this set is empty.
	pub const fn is_empty(&self) -> bool {
		self.present == 0
	}

	/// Returns `true` if this set contains the given tile.
	pub const fn contains(&self, tile: TKind::Tile) -> bool {
		self.tile_to_present_ref(tile)
	}

	/// Inserts the given tile into this set.
	///
	/// Returns `false` when the tile was already present in the set.
	pub const fn insert(&mut self, tile: TKind::Tile) -> bool {
		let mut count = self.tile_to_present_mut(tile);
		!count.set(true)
	}

	/// Inserts all tiles from the given iterator into this set.
	///
	/// # Errors
	///
	/// Returns `Err()` when inserting more of a tile than should exist.
	pub fn try_extend(&mut self, iter: impl IntoIterator<Item = TKind::Tile>) -> Result<(), TKind::Tile> {
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
	pub const fn remove(&mut self, tile: TKind::Tile) -> bool {
		let mut count = self.tile_to_present_mut(tile);
		count.set(false)
	}

	/// Retains only those tiles in this set that satisfy the given predicate.
	pub fn retain(&mut self, mut f: impl FnMut(TKind::Tile) -> bool) {
		let mut result = 0_u64;

		while let Some(offset) = self.present.lowest_one() {
			self.present &= !(0b1 << offset);
			#[expect(clippy::cast_possible_truncation)]
			let offset = offset as u8;
			let tile = unsafe { TKind::offset_to_tile(offset) };
			let retain = f(tile);
			result |= u64::from(retain) << offset;
		}

		self.present = result;
	}

	pub(crate) const fn simd_splat<const N: usize>(self) -> core::simd::Simd<u64, N> {
		core::simd::Simd::splat(self.present)
	}

	const fn tile_to_present_ref(&self, tile: TKind::Tile) -> bool {
		let offset = TKind::tile_to_offset(tile);
		self.present & (0b1 << offset) != 0
	}

	const fn tile_to_present_mut(&mut self, tile: TKind::Tile) -> U1Mut<'_> {
		let offset = TKind::tile_to_offset(tile);
		U1Mut {
			present: &mut self.present,
			offset,
		}
	}
}

/// Returns a `TileSet` containing all the elements of this set that are also present in the given set.
const impl<TKind> core::ops::BitAnd for TileSet<TKind> {
	type Output = Self;

	fn bitand(self, other: Self) -> Self::Output {
		Self { present: self.present & other.present, kind: self.kind }
	}
}

/// Retains only the elements of this set that are also present in the given set.
const impl<TKind> core::ops::BitAndAssign for TileSet<TKind> {
	fn bitand_assign(&mut self, other: Self) {
		self.present &= other.present;
	}
}

/// Returns a `TileSet` containing all the elements of this set and all the elements of the given set.
const impl<TKind> core::ops::BitOr for TileSet<TKind> {
	type Output = Self;

	fn bitor(self, other: Self) -> Self::Output {
		Self { present: self.present | other.present, kind: self.kind }
	}
}

/// Inserts all the elements of the given set into this set.
const impl<TKind> core::ops::BitOrAssign for TileSet<TKind> {
	fn bitor_assign(&mut self, other: Self) {
		self.present |= other.present;
	}
}

/// Returns a `TileSet` with all the elements of this set and all the elements of the given set
/// except the elements that are present in both sets.
const impl<TKind> core::ops::BitXor for TileSet<TKind> {
	type Output = Self;

	fn bitxor(self, other: Self) -> Self::Output {
		Self { present: self.present ^ other.present, kind: self.kind }
	}
}

/// Inserts all elements of the given set into this set and removes all elements from this set that are also present in the given set.
const impl<TKind> core::ops::BitXorAssign for TileSet<TKind> {
	fn bitxor_assign(&mut self, other: Self) {
		self.present ^= other.present;
	}
}

const impl<TKind> Clone for TileSet<TKind> {
	fn clone(&self) -> Self {
		Self {
			present: self.present,
			kind: self.kind,
		}
	}
}

impl<TKind> core::fmt::Debug for TileSet<TKind>
where
	TKind: Kind,
	Self: Clone + IntoIterator<Item = TKind::Tile>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_set().entries(self.clone()).finish()
	}
}

const impl<TKind> Default for TileSet<TKind> {
	fn default() -> Self {
		Self {
			present: 0,
			kind: Default::default(),
		}
	}
}

impl<TKind> FromIterator<TKind::Tile> for TileSet<TKind>
where
	TKind: const Kind,
{
	fn from_iter<T>(iter: T) -> Self
	where
		T: IntoIterator<Item = TKind::Tile>,
	{
		let mut result = Self::default();
		for tile in iter {
			_ = result.insert(tile);
		}
		result
	}
}

impl<TKind> IntoIterator for TileSet<TKind>
where
	TileSetIntoIter<TKind>: Iterator,
{
	type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
	type IntoIter = TileSetIntoIter<TKind>;

	fn into_iter(self) -> Self::IntoIter {
		TileSetIntoIter {
			present: self.present,
			kind: Default::default(),
		}
	}
}

/// Returns a `TileSet` with all the elements that this type of set could have except the elements present in this set.
const impl<TKind> core::ops::Not for TileSet<TKind>
where
	TKind: Kind,
{
	type Output = Self;

	fn not(self) -> Self::Output {
		Self { present: !(self.present) & ((0b1 << TKind::N) - 1), kind: self.kind }
	}
}

const impl<TKind> PartialEq for TileSet<TKind> {
	fn eq(&self, other: &Self) -> bool {
		self.present == other.present
	}
}

const impl<TKind> Eq for TileSet<TKind> {}

const fn make_tile_set<TKind>(tiles: &[TKind::Tile]) -> TileSet<TKind>
where
	TKind: const Kind,
{
	// TODO(rustup): This uses an indexed `while` loop instead of `.collect()` so that it can be `const fn`.
	let mut result = TileSet::default();
	let mut i = 0;
	while i < tiles.len() {
		result.insert(tiles[i]);
		i += 1;
	}
	result
}

/// An [`Iterator`] of all tiles in a [`TileSet`].
pub struct TileSetIntoIter<TKind> {
	present: u64,
	kind: core::marker::PhantomData<TKind>,
}

impl<TKind> TileSetIntoIter<TKind>
where
	TKind: Kind,
{
	fn next_inner(&mut self, offset: u32) -> TKind::Tile {
		#[expect(clippy::cast_possible_truncation)]
		let offset = offset as u8;
		let tile = unsafe { TKind::offset_to_tile(offset) };
		let mut count = U1Mut {
			present: &mut self.present,
			offset,
		};
		count.set(false);
		tile
	}
}

const impl<TKind> Clone for TileSetIntoIter<TKind> {
	fn clone(&self) -> Self {
		Self {
			present: self.present,
			kind: self.kind,
		}
	}
}

impl<TKind> core::fmt::Debug for TileSetIntoIter<TKind> {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("TileSetIntoIter").finish_non_exhaustive()
	}
}

impl<TKind> Iterator for TileSetIntoIter<TKind>
where
	TKind: Kind,
{
	type Item = TKind::Tile;

	fn next(&mut self) -> Option<Self::Item> {
		Some(self.next_inner(self.present.lowest_one()?))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<TKind> DoubleEndedIterator for TileSetIntoIter<TKind>
where
	TKind: Kind,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		Some(self.next_inner(self.present.highest_one()?))
	}
}

impl<TKind> ExactSizeIterator for TileSetIntoIter<TKind>
where
	Self: Iterator,
{
	fn len(&self) -> usize {
		self.present.count_ones() as usize
	}
}

impl<TKind> core::iter::FusedIterator for TileSetIntoIter<TKind>
where
	Self: Iterator,
{}

unsafe impl<TKind> core::iter::TrustedLen for TileSetIntoIter<TKind>
where
	Self: Iterator,
{}

/// A set specialized to hold [`NumberTile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as identical tiles
/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile27Set = TileSet<Tile27>;
/// An [`Iterator`] of all [`NumberTile`]s in a [`Tile27Set`].
pub type Tile27SetIntoIter = TileSetIntoIter<Tile27>;

assert_size_of!(Tile27Set, 8);

const impl Kind for Tile27 {
	type Tile = NumberTile;
	const N: usize = 27;

	//                                      |    s    |    p    |    m
	// 0000000000000000000000000000000000000|987654321|987654321|987654321

	fn tile_to_offset(tile: Self::Tile) -> u8 {
		Tile::offset(tile.into())
	}

	unsafe fn offset_to_tile(offset: u8) -> Self::Tile {
		let tile = (offset << 1) + t!(1m) as u8;
		unsafe { core::mem::transmute::<u8, NumberTile>(tile) }
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
pub type Tile34Set = TileSet<Tile34>;
/// An [`Iterator`] of all [`Tile`]s in a [`Tile34Set`].
pub type Tile34SetIntoIter = TileSetIntoIter<Tile34>;

assert_size_of!(Tile34Set, 8);

const impl Kind for Tile34 {
	type Tile = Tile;
	const N: usize = 34;

	//                               |   z   |    s    |    p    |    m
	// 000000000000000000000000000000|7654321|987654321|987654321|987654321

	fn tile_to_offset(tile: Self::Tile) -> u8 {
		Tile::offset(tile)
	}

	unsafe fn offset_to_tile(offset: u8) -> Self::Tile {
		let tile = (offset << 1) + t!(1m) as u8;
		unsafe { core::mem::transmute::<u8, Tile>(tile) }
	}

	fn all_yonma() -> &'static [Self::Tile] {
		Tile::each(GameType::Yonma)
	}

	fn all_sanma() -> &'static [Self::Tile] {
		Tile::each(GameType::Sanma)
	}
}

/// A set specialized to hold [`Tile`]s in a compact non-allocating representation.
///
/// This type considers [`Five`](crate::Number::Five) and [`FiveRed`](crate::Number::FiveRed) as distinct tiles
/// in its implementation of [`contains`](Self::contains), [`insert`](Self::insert) and [`remove`](Self::remove).
pub type Tile37Set = TileSet<Tile37>;
/// An [`Iterator`] of all [`Tile`]s in a [`Tile37Set`].
pub type Tile37SetIntoIter = TileSetIntoIter<Tile37>;

assert_size_of!(Tile37Set, 8);

const impl Kind for Tile37 {
	type Tile = Tile;
	const N: usize = 37;

	//                            |   z   |     s    |     p    |     m
	// 000000000000000000000000000|7654321|9876054321|9876054321|9876054321

	fn tile_to_offset(tile: Self::Tile) -> u8 {
		Tile::offset(tile) + 3 - u8::from(tile < t!(0m)) - u8::from(tile < t!(0p)) - u8::from(tile < t!(0s))
	}

	unsafe fn offset_to_tile(offset: u8) -> Self::Tile {
		let tile = offset - u8::from(offset >= 5) - u8::from(offset >= 15) - u8::from(offset >= 25);
		let tile = ((tile << 1) + t!(1m) as u8) | u8::from(offset == 5 || offset == 15 || offset == 25);
		unsafe { core::mem::transmute::<u8, Tile>(tile) }
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
	const fn set(&mut self, value: bool) -> bool {
		let mask = 0b1 << self.offset;
		let previous = *self.present & mask != 0;
		*self.present = (*self.present & !mask) | ((value as u64) << self.offset);
		previous
	}
}

impl Tile27Set {
	pub(crate) const FIVES: Tile27Set = t27set![5m, 5p, 5s];

	pub(crate) const HAS_PREVIOUS: Tile27Set = t27set![
		2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,
		2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,
		2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,
	];

	pub(crate) const HAS_NEXT: Tile27Set = t27set![
		1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m,
		1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p,
		1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s,
	];
}

impl Tile34Set {
	pub(crate) const TERMINALS: Self = t34set![1m, 9m, 1p, 9p, 1s, 9s];

	pub(crate) const HONORS: Self = t34set![E, S, W, N, Wh, G, R];

	pub(crate) const TERMINALS_AND_HONORS: Self = Self::TERMINALS | Self::HONORS;

	pub(crate) const REVERSIBLE: Self = t34set![1p, 2p, 3p, 4p, 5p, 8p, 9p, 2s, 4s, 5s, 6s, 8s, 9s, Wh];

	pub(crate) const BLACK: Self = t34set![2p, 4p, 8p, E, S, W, N];

	fn from_suit_counts(mut sets: core::simd::Simd<u32, 4>) -> Self {
		const fn to_set(count: u32) -> u32 {
			count.extract_bits(0b001_001_001_001_001_001_001_001_001)
		}

		sets[0] = to_set(sets[0]);
		sets[1] = to_set(sets[1]);
		sets[2] = to_set(sets[2]);
		sets[3] = to_set(sets[3]);
		let sets = core::simd::num::SimdUint::cast::<u64>(sets);
		let sets = sets << core::simd::Simd::from_array([0, 9, 18, 27]);
		let present = core::simd::num::SimdUint::reduce_or(sets);
		Self { present, kind: Default::default() }
	}

	#[cfg_attr(use_core_simd, expect(unused))]
	pub(crate) fn atleast_two(set: &Tile34MultiSet) -> Self {
		let counts = set.to_suits_simd();
		let sets = (counts >> 1) | (counts >> 2);
		Self::from_suit_counts(sets)
	}

	#[cfg_attr(use_core_simd, expect(unused))]
	pub(crate) fn atleast_three(set: &Tile34MultiSet) -> Self {
		let counts = set.to_suits_simd();
		let sets = (counts & (counts >> 1)) | (counts >> 2);
		Self::from_suit_counts(sets)
	}

	pub(crate) fn atleast_four(set: &Tile34MultiSet) -> Self {
		let counts = set.to_suits_simd();
		let sets = counts >> 2;
		Self::from_suit_counts(sets)
	}
}

impl From<&Tile34MultiSet> for Tile34Set {
	fn from(set: &Tile34MultiSet) -> Self {
		let counts = set.to_suits_simd();
		let sets = counts | (counts >> 1) | (counts >> 2);
		Self::from_suit_counts(sets)
	}
}

const impl From<Tile37Set> for Tile34Set {
	fn from(set: Tile37Set) -> Self {
		let present = set.present;
		let present =
			( present & 0b0000000_0000000000_0000000000_0000011111) |
			((present & 0b0000000_0000000000_0000011111_1111100000) >> 1) |
			((present & 0b0000000_0000011111_1111100000_0000000000) >> 2) |
			((present & 0b1111111_1111100000_0000000000_0000000000) >> 3);
		Self { present, kind: Default::default() }
	}
}

impl Tile37Set {
	pub(crate) const TERMINALS_AND_HONORS: Self = t37set![1m, 9m, 1p, 9p, 1s, 9s, E, S, W, N, Wh, G, R];

	pub(crate) const fn remove_ignore_red(&mut self, tile: Tile) {
		let offset = Tile37::tile_to_offset(tile.remove_red());
		let mask = if tile.make_red().is_some() { 0b11 } else { 0b1 };
		self.present &= !(mask << offset);
	}
}

impl From<Tile37MultiSet> for Tile37Set {
	fn from(set: Tile37MultiSet) -> Self {
		const fn to_set(count: u32) -> u32 {
			count.extract_bits(0b001_001_001_001_001_001_001_001_001_001)
		}

		let sets = set.to_suits_simd();
		let mut sets = sets | (sets >> 1) | (sets >> 2);
		sets[0] = to_set(sets[0]);
		sets[1] = to_set(sets[1]);
		sets[2] = to_set(sets[2]);
		sets[3] = to_set(sets[3]);
		let sets = core::simd::num::SimdUint::cast::<u64>(sets);
		let sets = sets << core::simd::Simd::from_array([0, 10, 20, 30]);
		let present = core::simd::num::SimdUint::reduce_or(sets);
		Self { present, kind: Default::default() }
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
			concat!(
				"{1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,",
				" 1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,",
				" 1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s}",
			),
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
			concat!(
				"{1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m,",
				" 1p, 2p, 3p, 4p, 5p, 6p, 7p, 8p, 9p,",
				" 1s, 2s, 3s, 4s, 5s, 6s, 7s, 8s, 9s,",
				" E, S, W, N, Wh, G, R}",
			),
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

	#[test]
	fn all_37() {
		let mut set = Tile37Set::default();

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

		let set: Tile37Set = Tile::each(GameType::Yonma).iter().copied().collect();
		assert_eq!(set, Tile37Set::all(GameType::Yonma));
		assert_eq!(
			std::format!("{set:?}"),
			concat!(
				"{1m, 2m, 3m, 4m, 5m, 0m, 6m, 7m, 8m, 9m,",
				" 1p, 2p, 3p, 4p, 5p, 0p, 6p, 7p, 8p, 9p,",
				" 1s, 2s, 3s, 4s, 5s, 0s, 6s, 7s, 8s, 9s,",
				" E, S, W, N, Wh, G, R}",
			),
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
				assert!(set.contains(t!(0m)));
			}

			{
				let mut set = set.clone();
				assert!(set.remove(t!(0m)));
				assert!(set.contains(t!(5m)));
				assert!(!set.contains(t!(0m)));
			}
		}

		assert_eq!(set.clone().into_iter().count(), 37);

		assert!(set.into_iter().eq(Tile::each(GameType::Yonma).iter().copied()));
	}
}
