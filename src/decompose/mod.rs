use crate::{
	ArrayVec,
	KouWait,
	NumberTile,
	ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ScorableHandRegularPair, ScorableHandRegularPairTag, ShunLowTileAndHasFiveRed, ShunWait,
	Tile, Tile27Set, Tile37CountedMultiSet, Tile37MultiSet, Tile37Set, Tile37SetIntoIter, TsumoOrRon,
};

#[derive(Copy, Debug)]
struct Meld<M> {
	len: u8,
	ms: [core::mem::MaybeUninit<M>; 4],
}

#[expect(clippy::expl_impl_clone_on_copy)] // TODO(rustup): Replace with `#[derive_const(Clone)]` when `[T; N]: [const] Clone`
const impl<M> Clone for Meld<M>
where
	M: Copy,
{
	fn clone(&self) -> Self {
		*self
	}
}

#[derive(Copy, Debug)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(clippy::eq_op)]
enum Honor {
	/// Ton
	E = t!(E) as u8 - t!(E) as u8,
	/// Nan
	S = t!(S) as u8 - t!(E) as u8,
	/// Shaa
	W = t!(W) as u8 - t!(E) as u8,
	/// Pei
	N = t!(N) as u8 - t!(E) as u8,
	/// Haku
	P = t!(Wh) as u8 - t!(E) as u8,
	/// Hatsu
	F = t!(G) as u8 - t!(E) as u8,
	/// Chun
	C = t!(R) as u8 - t!(E) as u8,
}

impl From<Honor> for ScorableHandMeld {
	fn from(honor: Honor) -> Self {
		let t = unsafe { core::mem::transmute::<u8, Tile>(t!(E) as u8 + honor as u8) };
		ScorableHandMeld::Ankou(t)
	}
}

impl Meld<Honor> {
	/// # Safety
	///
	/// `melds` must have enough elements to write all of `self`'s melds.
	unsafe fn write_to<'a>(self, mut melds: impl Iterator<Item = &'a mut core::mem::MaybeUninit<ScorableHandMeld>>) {
		let len = usize::from(self.len);
		unsafe { core::hint::assert_unchecked(len <= self.ms.len()); }
		for m in &self.ms[..len] {
			let m = unsafe { m.assume_init() };
			let slot = melds.next();
			let slot = unsafe { slot.unwrap_unchecked() };
			slot.write(m.into());
		}
	}
}

#[allow(clippy::enum_glob_use)]
mod honors {
	use {Some as O, None as X};
	use super::{Meld, Honor, Honor::*};

	const M0: Meld<Honor> = Meld { len: 0, ms: [const { core::mem::MaybeUninit::uninit() }; 4] };

	const fn m1(m1: Honor) -> Meld<Honor> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		Meld { len: 1, ms }
	}

	const fn m2(m1: Honor, m2: Honor) -> Meld<Honor> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		Meld { len: 2, ms }
	}

	const fn m3(m1: Honor, m2: Honor, m3: Honor) -> Meld<Honor> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		ms[2].write(m3);
		Meld { len: 3, ms }
	}

	const fn m4(m1: Honor, m2: Honor, m3: Honor, m4: Honor) -> Meld<Honor> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		ms[2].write(m3);
		ms[3].write(m4);
		Meld { len: 4, ms }
	}

	include!("honors.generated.rs");
}

#[derive(Copy, Debug)]
#[derive_const(Clone)]
#[repr(u8)]
#[expect(clippy::eq_op)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K1 = Tile::Man1 as u8 - Tile::Man1 as u8,
	/// Ankou 222 / Pair 22
	K2 = Tile::Man2 as u8 - Tile::Man1 as u8,
	/// Ankou 333 / Pair 33
	K3 = Tile::Man3 as u8 - Tile::Man1 as u8,
	/// Ankou 444 / Pair 44
	K4 = Tile::Man4 as u8 - Tile::Man1 as u8,
	/// Ankou 555 / Pair 55
	K5 = Tile::Man5 as u8 - Tile::Man1 as u8,
	/// Ankou 550 / Pair 50
	K0 = Tile::Man0 as u8 - Tile::Man1 as u8,
	/// Ankou 666 / Pair 66
	K6 = Tile::Man6 as u8 - Tile::Man1 as u8,
	/// Ankou 777 / Pair 77
	K7 = Tile::Man7 as u8 - Tile::Man1 as u8,
	/// Ankou 888 / Pair 88
	K8 = Tile::Man8 as u8 - Tile::Man1 as u8,
	/// Ankou 999 / Pair 99
	K9 = Tile::Man9 as u8 - Tile::Man1 as u8,

	/// Shun 123
	S0 = (ShunLowTileAndHasFiveRed::Man1 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 234
	S1 = (ShunLowTileAndHasFiveRed::Man2 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 345
	S2 = (ShunLowTileAndHasFiveRed::Man3 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 340
	S3 = (ShunLowTileAndHasFiveRed::Man3Red as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 456
	S4 = (ShunLowTileAndHasFiveRed::Man4 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 406
	S5 = (ShunLowTileAndHasFiveRed::Man4Red as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 567
	S6 = (ShunLowTileAndHasFiveRed::Man5 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 067
	S7 = (ShunLowTileAndHasFiveRed::Man5Red as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 678
	S8 = (ShunLowTileAndHasFiveRed::Man6 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 789
	S9 = (ShunLowTileAndHasFiveRed::Man7 as u8 - ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
}

impl NumberMeld {
	fn with_base(self, base: NumberTile) -> ScorableHandMeld {
		let number = self as u8;
		if number & (1 << 7) == 0 {
			// Ankou
			let t = base as u8 + number;
			let t = unsafe { core::mem::transmute::<u8, NumberTile>(t) };
			ScorableHandMeld::Ankou(t.into())
		}
		else {
			// Anjun
			let number = number & !(1 << 7);
			let t = base as u8 + number;
			let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(t) };
			ScorableHandMeld::Anjun(t)
		}
	}
}

impl Meld<NumberMeld> {
	/// # Safety
	///
	/// `melds` must have enough elements to write all of `self`'s melds.
	unsafe fn write_to<'a>(self, mut melds: impl Iterator<Item = &'a mut core::mem::MaybeUninit<ScorableHandMeld>>, base: NumberTile) {
		let len = usize::from(self.len);
		unsafe { core::hint::assert_unchecked(len <= self.ms.len()); }
		for m in &self.ms[..len] {
			let m = unsafe { m.assume_init() };
			let slot = melds.next();
			let slot = unsafe { slot.unwrap_unchecked() };
			slot.write(m.with_base(base));
		}
	}
}

#[allow(clippy::enum_glob_use)]
mod numbers {
	use {Some as O, None as X};
	use super::{Meld, NumberMeld, NumberMeld::*};

	const M0: Meld<NumberMeld> = Meld { len: 0, ms: [const { core::mem::MaybeUninit::uninit() }; 4] };

	const fn m1(m1: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		Meld { len: 1, ms }
	}

	const fn m2(m1: NumberMeld, m2: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		Meld { len: 2, ms }
	}

	const fn m3(m1: NumberMeld, m2: NumberMeld, m3: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		ms[2].write(m3);
		Meld { len: 3, ms }
	}

	const fn m4(m1: NumberMeld, m2: NumberMeld, m3: NumberMeld, m4: NumberMeld) -> Meld<NumberMeld> {
		let mut ms = [const { core::mem::MaybeUninit::uninit() }; 4];
		ms[0].write(m1);
		ms[1].write(m2);
		ms[2].write(m3);
		ms[3].write(m4);
		Meld { len: 4, ms }
	}

	include!("numbers.generated.rs");
}

#[derive(Debug)]
#[derive_const(Clone, Default)]
pub(crate) struct Lookup<const NM: usize>(LookupInner);

// Common implementation independent of `NM` to combat monomorphization bloat.
#[derive(Debug)]
#[derive_const(Clone, Default)]
struct LookupInner {
	ji: Option<&'static (Option<Honor>, Meld<Honor>)>,
	i_sou: u8,
	sou: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	i_pin: u8,
	pin: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	man: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	pair_suit: PairSuit,
}

#[derive(Copy, Debug)]
#[derive_const(Clone, Default)]
#[repr(u8)]
enum PairSuit {
	#[default]
	Man = tn!(1m) as u8,
	Pin = tn!(1p) as u8,
	Sou = tn!(1s) as u8,
	Ji = t!(E) as u8,
}

impl<const NM: usize> Lookup<NM> {
	pub(crate) fn new(ts: &Tile37CountedMultiSet<{ NM * 3 + 2 }>) -> Self {
		Self(LookupInner::new(ts.as_ref()))
	}
}

impl<const NM: usize> Iterator for Lookup<NM> {
	type Item = ([ScorableHandMeld; NM], ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		let mut melds = [const { core::mem::MaybeUninit::uninit() }; NM];
		let pair = unsafe { self.0.next_to(&mut melds)? };
		// SAFETY: The size of `melds` is correct based on the number of tiles in `ts`. So if `self.0.next_to()` returned `Some(_)`,
		// we know that `melds` must have been completely filled with melds.
		let melds = unsafe { core::mem::MaybeUninit::array_assume_init(melds) };
		Some((melds, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<const NM: usize> ExactSizeIterator for Lookup<NM> {
	fn len(&self) -> usize {
		self.0.len()
	}
}

impl<const NM: usize> core::iter::FusedIterator for Lookup<NM> {}

unsafe impl<const NM: usize> core::iter::TrustedLen for Lookup<NM> {}

impl LookupInner {
	fn new(ts: &Tile37MultiSet) -> Self {
		fn lookup_honors((key, len): (u32, u8)) -> Option<&'static (Option<Honor>, Meld<Honor>)> {
			let map = [
				honors::ZEROS,
				&[],
				honors::TWOS,
				honors::THREES,
				&[],
				honors::FIVES,
				honors::SIXES,
				&[],
				honors::EIGHTS,
				honors::NINES,
				&[],
				honors::ELEVENS,
				honors::TWELVES,
				&[],
				honors::FOURTEENS,
			].get(usize::from(len)).copied().unwrap_or_default();
			map.binary_search_by_key(&key, |(key, _)| *key).ok().map(|i| &map[i].1)
		}

		fn lookup_numbers((key, len): (u32, u8)) -> &'static [(Option<NumberMeld>, Meld<NumberMeld>)] {
			let map = [
				numbers::ZEROS,
				&[],
				numbers::TWOS,
				numbers::THREES,
				&[],
				numbers::FIVES,
				numbers::SIXES,
				&[],
				numbers::EIGHTS,
				numbers::NINES,
				&[],
				numbers::ELEVENS,
				numbers::TWELVES,
				&[],
				numbers::FOURTEENS,
			].get(usize::from(len)).copied().unwrap_or_default();
			map.binary_search_by_key(&key, |(key, _, _)| *key).ok().map_or(&[], |i| {
				let (_, storage_start, storage_end) = map[i];
				let storage_start = usize::from(storage_start);
				let storage_end = usize::from(storage_end);
				unsafe { core::hint::assert_unchecked(storage_start < storage_end); }
				unsafe { core::hint::assert_unchecked(storage_end <= numbers::STORAGE.len()); }
				&numbers::STORAGE[storage_start..storage_end]
			})
		}

		fn at_most_one_some<T>(a: Option<T>, b: Option<T>) -> Result<Option<T>, ()> {
			match (a, b) {
				(None, x) | (x, None) => Ok(x),
				(Some(_), Some(_)) => Err(()),
			}
		}

		let mut result = Self::default();
		// If any lookup failed, then the hand as a whole cannot be decomposed, so we can just terminate early.
		//
		// Also, all elements of each slice have the same shape. Eg if the first element of `man` is `(Some(_), m2(..))`,
		// then the other elements of `man` will also be `(Some(_), m2(..))`. This means that if we find one combination of elements
		// that produces zero or more than two pairs, then every combination will also do that, so we can just terminate early.
		if
			let Some(ji @ (ji_pair, _)) = lookup_honors(ts.ji()) &&
			let pair_suit = ji_pair.map(|_| PairSuit::Ji) &&
			let sou = lookup_numbers(ts.sou()) &&
			let Some((sou_pair, _)) = sou.first() &&
			let Ok(pair_suit) = at_most_one_some(pair_suit, sou_pair.map(|_| PairSuit::Sou)) &&
			let pin = lookup_numbers(ts.pin()) &&
			let Some((pin_pair, _)) = pin.first() &&
			let Ok(pair_suit) = at_most_one_some(pair_suit, pin_pair.map(|_| PairSuit::Pin)) &&
			let man = lookup_numbers(ts.man()) &&
			let Some((man_pair, _)) = man.first() &&
			let Ok(Some(pair_suit)) = at_most_one_some(pair_suit, man_pair.map(|_| PairSuit::Man))
		{
			result.ji = Some(ji);
			result.sou = sou;
			result.pin = pin;
			result.man = man;
			result.pair_suit = pair_suit;
		}
		result
	}

	/// # Safety
	///
	/// `melds` must have enough elements to write (number of tiles - 2) / 3 melds.
	unsafe fn next_to(&mut self, melds: &mut [core::mem::MaybeUninit<ScorableHandMeld>]) -> Option<ScorableHandPair> {
		let &(ji_pair, ji_melds) = self.ji?;

		let mut i_sou = usize::from(self.i_sou);
		unsafe { core::hint::assert_unchecked(i_sou < self.sou.len()); }
		let (sou_pair, sou_melds) = self.sou[i_sou];

		let mut i_pin = usize::from(self.i_pin);
		unsafe { core::hint::assert_unchecked(i_pin < self.pin.len()); }
		let (pin_pair, pin_melds) = self.pin[i_pin];

		let (&(man_pair, man_melds), man_rest) = {
			let man = self.man.split_first();
			unsafe { core::hint::assert_unchecked(!self.man.is_empty()); }
			unsafe { man.unwrap_unchecked() }
		};

		let mut melds = melds.iter_mut();
		// SAFETY: In order to have gotten here, we know that two of the given tiles correspond to a pair and the rest are in melds.
		// If there was not one pair, we would've returned a neutered iterator in `new()`.
		// If one or more of the tiles did not form a valid meld, the corresponding slice would've been empty and we would've returned a neutered iterator in `new()`.
		//
		// So, as long as the caller upheld our safety requirement, we will fill the `melds` slice exactly.
		unsafe { man_melds.write_to(&mut melds, tn!(1m)); }
		unsafe { pin_melds.write_to(&mut melds, tn!(1p)); }
		unsafe { sou_melds.write_to(&mut melds, tn!(1s)); }
		unsafe { ji_melds.write_to(melds); }
		let pair = unsafe { self.pair_suit.make_pair(man_pair, pin_pair, sou_pair, ji_pair) };

		i_sou += 1;
		if i_sou == self.sou.len() {
			i_sou = 0;

			i_pin += 1;
			if i_pin == self.pin.len() {
				i_pin = 0;

				self.man = man_rest;
				if self.man.is_empty() {
					self.ji = None;
				}
			}
			#[expect(clippy::cast_possible_truncation)]
			{ self.i_pin = i_pin as u8; }
		}
		#[expect(clippy::cast_possible_truncation)]
		{ self.i_sou = i_sou as u8; }

		Some(pair)
	}

	fn len(&self) -> usize {
		if self.ji.is_some() {
			let max = self.sou.len() * self.pin.len() * self.man.len();
			let processed = usize::from(self.i_sou) + usize::from(self.i_pin) * self.sou.len();
			let result = max - processed;
			unsafe { core::hint::assert_unchecked(result > 0); }
			result
		}
		else {
			0
		}
	}
}

impl PairSuit {
	/// # Safety
	///
	/// The `pair` parameter corresponding to `self` must be `Some(_)`.
	const unsafe fn make_pair(
		self,
		man_pair: Option<NumberMeld>,
		pin_pair: Option<NumberMeld>,
		sou_pair: Option<NumberMeld>,
		ji_pair: Option<Honor>,
	) -> ScorableHandPair {
		// Micro-optimization: A `match` on `self as u8` generates a tree of branches.
		// We can do better by merging all the pairs and shifting out the right one.

		// SAFETY: Rustonomicon guarantees that `Option` uses the niches of `repr(u8)` enums.
		// Thus `Some::<NumberMeld | Honor>` has an identical bit representation to `NumberMeld | Honor` and is thus transmutable to `u8`,
		// and `None::<NumberMeld | Honor>` occupies some niche that is also transmutable to `u8`.
		let pairs = u32::from_le_bytes([
			unsafe { core::mem::transmute::<Option<NumberMeld>, u8>(man_pair) },
			unsafe { core::mem::transmute::<Option<NumberMeld>, u8>(pin_pair) },
			unsafe { core::mem::transmute::<Option<NumberMeld>, u8>(sou_pair) },
			unsafe { core::mem::transmute::<Option<Honor>, u8>(ji_pair) },
		]);
		// `self as u8 - t!(1m) as u8` is one of 0x00, 0x12, 0x24 and 0x36. When shifted left by 2,
		// the lower five bits of these form 0, 8, 16, 24, which are exactly the shifts needed to extract the pair from `pairs`.
		let pair_i = (self as u8 - t!(1m) as u8) << 2;
		let pair = pairs.wrapping_shr(pair_i.into());
		#[expect(clippy::cast_possible_truncation)]
		let pair = self as u8 + pair as u8;
		let pair = unsafe { core::mem::transmute::<u8, Tile>(pair) };
		ScorableHandPair(pair)
	}
}

#[derive(Clone, Debug)]
pub(crate) struct LookupForNewTile<const NM: usize>
where
	[(); NM + 1]:,
	[(); (NM + 2).min(4)]:,
{
	current: core::array::IntoIter<([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair), { (NM + 2).min(4) }>,
	lookup: Lookup<{ NM + 1 }>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<const NM: usize> LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 2).min(4)]:,
{
	pub(crate) const fn new(lookup: Lookup<{ NM + 1 }>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		Self {
			// TODO(rustup): Use `Default::default()` when `core::array::IntoIter: const Default`.
			current: core::array::IntoIter::empty(),
			lookup,
			new_tile,
			tsumo_or_ron,
		}
	}
}

const impl<const NM: usize> Default for LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 2).min(4)]:,
{
	fn default() -> Self {
		Self {
			// TODO(rustup): Use `Default::default()` when `core::array::IntoIter: const Default`.
			current: core::array::IntoIter::empty(),
			lookup: Default::default(),
			new_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
		}
	}
}

impl<const NM: usize> Iterator for LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 2).min(4)]:,
{
	type Item = ([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current.next() else {
				let (ms, pair) = self.lookup.next()?;
				self.current = extract_fourth_meld(ms, pair, self.new_tile, self.tsumo_or_ron);
				continue;
			};
			break Some((ms, md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_len = self.current.len();
		let (lookup_lo, lookup_hi) = self.lookup.size_hint();
		(current_len + lookup_lo, lookup_hi.map(|lookup_hi| current_len + lookup_hi * (NM + 2)))
	}
}

impl<const NM: usize> core::iter::FusedIterator for LookupForNewTile<NM>
where
	[(); NM + 1]:,
	[(); (NM + 2).min(4)]:,
{}

#[derive(Clone, Debug)]
pub(crate) struct LookupForTenhou {
	current_a: core::array::IntoIter<([ScorableHandMeld; 3], ScorableHandFourthMeld, ScorableHandRegularPair), 4>,
	current_b: Option<([ScorableHandMeld; 4], ScorableHandPair, Tile37SetIntoIter)>,
	lookup: Lookup<4>,
	tiles: Tile37Set,
}

impl LookupForTenhou {
	pub(crate) fn new(ts: Tile37CountedMultiSet<14>) -> Self {
		let lookup = Lookup::new(&ts);
		let tiles = Tile37Set::from(Tile37MultiSet::from(ts));
		Self {
			current_a: Default::default(),
			current_b: None,
			lookup,
			tiles,
		}
	}
}

const impl Default for LookupForTenhou {
	fn default() -> Self {
		Self {
			// TODO(rustup): Use `Default::default()` when `core::array::IntoIter: const Default`.
			current_a: core::array::IntoIter::empty(),
			current_b: None,
			lookup: Default::default(),
			tiles: Default::default(),
		}
	}
}

impl Iterator for LookupForTenhou {
	type Item = ([ScorableHandMeld; 3], ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current_a.next() else {
				let (ms, pair, new_tile) =
					if
						let Some((ms, pair, new_tiles)) = &mut self.current_b &&
						let Some(new_tile) = new_tiles.next()
					{
						(ms, pair, new_tile)
					}
					else {
						let (ms, pair) = self.lookup.next()?;
						let new_tiles = self.tiles.clone().into_iter();
						let (ms, pair, new_tiles) = self.current_b.insert((ms, pair, new_tiles));
						let new_tile = new_tiles.next();
						// SAFETY: `self.tiles` contains fourteen tiles so `new_tiles` contains at least ceil(14 / 4) elements.
						let new_tile = unsafe { new_tile.unwrap_unchecked() };
						(ms, pair, new_tile)
					};
				self.current_a = extract_fourth_meld(*ms, *pair, new_tile, TsumoOrRon::Tsumo);
				continue;
			};
			break Some((ms, md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_a_len = self.current_a.len();
		(current_a_len, None)
	}
}

impl core::iter::FusedIterator for LookupForTenhou {}

fn extract_fourth_meld<const NM: usize>(
	ms: [ScorableHandMeld; NM + 1],
	pair: ScorableHandPair,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
) -> core::array::IntoIter<([ScorableHandMeld; NM], ScorableHandFourthMeld, ScorableHandRegularPair), { (NM + 2).min(4) }>
{
	const ONES: Tile27Set = t27set![1m, 1p, 1s];
	const SEVENS: Tile27Set = t27set![7m, 7p, 7s];

	let mut current = ArrayVec::new();
	//  pair.0 | new_tile |   should match
	// ========+==========+==================
	//    5m   |    5m    | yes, pair is 55m
	//    5m   |    0m    | no,  pair is 55m
	//    0m   |    5m    | yes, pair is 50m
	//    0m   |    0m    | yes, pair is 50m
	if pair.0 == new_tile || pair.0.remove_red() == new_tile {
		let md = ms[ms.len() - 1];
		let ms = unsafe { except(&ms, ms.len() - 1) };
		let pair_tag = match tsumo_or_ron {
			TsumoOrRon::Tsumo => ScorableHandRegularPairTag::Antoi,
			TsumoOrRon::Ron => ScorableHandRegularPairTag::Mentoi,
		};
		let pair = ScorableHandRegularPair { tag: pair_tag, inner: pair };
		let result = current.push((ms, ScorableHandFourthMeld::tanki(md), pair));
		unsafe { result.unwrap_unchecked(); }
	}
	current.extend(ms.iter().enumerate().filter_map(|(i, &md)| {
		let md = match md {
			ScorableHandMeld::Ankou(tile) => {
				//  tile | new_tile |   should match
				// ======+==========+==================
				//   5m  |    5m    | yes, kou is 555m
				//   5m  |    0m    | no,  kou is 555m
				//   0m  |    5m    | yes, kou is 550m
				//   0m  |    0m    | yes, kou is 550m
				if tile != new_tile && tile.remove_red() != new_tile {
					return None;
				}
				ScorableHandFourthMeld::kou(tile, tsumo_or_ron, KouWait::Shanpon)
			},

			ScorableHandMeld::Anjun(tile) => {
				let (t1, t2, t3) = tile.shun();
				let wait =
					if Tile::from(t1) == new_tile {
						if SEVENS.contains(t1) { ShunWait::Penchan } else { ShunWait::RyanmenLow }
					}
					else if Tile::from(t2) == new_tile {
						ShunWait::Kanchan
					}
					else if Tile::from(t3) == new_tile {
						if ONES.contains(t1) { ShunWait::Penchan } else { ShunWait::RyanmenHigh }
					}
					else {
						return None;
					};
				ScorableHandFourthMeld::shun(tile, tsumo_or_ron, wait)
			},

			_ => unsafe { core::hint::unreachable_unchecked(); },
		};
		let ms = unsafe { except(&ms, i) };
		let pair = ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Antoi, inner: pair };
		Some((ms, md, pair))
	}));
	current.into_iter()
}

/// # Safety
///
/// `ts_discard` must be within the bounds of `ts`.
unsafe fn except<T, const N: usize>(ts: &[T; N + 1], ts_discard: usize) -> [T; N]
where
	T: Clone,
{
	unsafe { core::hint::assert_unchecked(ts_discard <= N); }
	let mut result = [const { core::mem::MaybeUninit::uninit() }; N];
	result[..ts_discard].write_clone_of_slice(&ts[..ts_discard]);
	result[ts_discard..].write_clone_of_slice(&ts[(ts_discard + 1)..]);
	unsafe { core::mem::MaybeUninit::array_assume_init(result) }
}

#[cfg(test)]
#[coverage(off)]
mod tests {
	extern crate std;

	use crate::Number;
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		let mut result = ArrayVec::<_, 3>::new();
		m.for_each_tile(|t| result.push(t).unwrap());
		result.try_into().unwrap()
	}

	fn fourth_meld_to_tiles(m: ScorableHandFourthMeld) -> ArrayVec<([Tile; 4], Tile), 2> {
		let mut result = ArrayVec::new();

		match m {
			m @ (
				ScorableHandFourthMeld::Ankou(_, KouWait::Tanki) |
				ScorableHandFourthMeld::Anjun(_, ShunWait::Tanki)
			) => {
				let [t1, t2, t3] = meld_to_tiles(m.into());
				result.push(([t1, t2, t3, t!(1p)], t!(1p))).unwrap();
			},

			ScorableHandFourthMeld::Ankou(tile, KouWait::Shanpon) => {
				let t = tile.remove_red();
				result.push(([t, t, t!(1p), t!(1p)], tile)).unwrap();
				if t != tile {
					result.push(([t, tile, t!(1p), t!(1p)], t)).unwrap();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Kanchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t3, t!(1p), t!(1p)], t2)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Penchan) => {
				let (t1, t2, t3) = tile.shun();
				if t1.number() == Number::One {
					result.push(([t1.into(), t2.into(), t!(1p), t!(1p)], t3.into())).unwrap();
				}
				else if t1.number() == Number::Seven {
					result.push(([t2.into(), t3.into(), t!(1p), t!(1p)], t1.into())).unwrap();
				}
				else {
					unreachable!();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenLow) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t2, t3, t!(1p), t!(1p)], t1)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenHigh) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t2, t!(1p), t!(1p)], t3)).unwrap();
			},

			_ => unreachable!(),
		}

		result
	}

	fn melds() -> [ScorableHandMeld; 20] {
		[
			make_scorable_hand!(@meld { ankou 1s 1s 1s }),
			make_scorable_hand!(@meld { anjun 1s 2s 3s }),
			make_scorable_hand!(@meld { ankou 2s 2s 2s }),
			make_scorable_hand!(@meld { anjun 2s 3s 4s }),
			make_scorable_hand!(@meld { ankou 3s 3s 3s }),
			make_scorable_hand!(@meld { anjun 3s 4s 5s }),
			make_scorable_hand!(@meld { anjun 3s 4s 0s }),
			make_scorable_hand!(@meld { ankou 4s 4s 4s }),
			make_scorable_hand!(@meld { anjun 4s 5s 6s }),
			make_scorable_hand!(@meld { anjun 4s 0s 6s }),
			make_scorable_hand!(@meld { ankou 5s 5s 5s }),
			make_scorable_hand!(@meld { anjun 5s 6s 7s }),
			make_scorable_hand!(@meld { ankou 5s 5s 0s }),
			make_scorable_hand!(@meld { anjun 0s 6s 7s }),
			make_scorable_hand!(@meld { ankou 6s 6s 6s }),
			make_scorable_hand!(@meld { anjun 6s 7s 8s }),
			make_scorable_hand!(@meld { ankou 7s 7s 7s }),
			make_scorable_hand!(@meld { anjun 7s 8s 9s }),
			make_scorable_hand!(@meld { ankou 8s 8s 8s }),
			make_scorable_hand!(@meld { ankou 9s 9s 9s }),
		]
	}

	fn melds_last() -> [ScorableHandFourthMeld; 40] {
		[
			make_scorable_hand!(@meldr4 { ankou 1s 1s 1s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s penchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s ryanmen_low }),
			make_scorable_hand!(@meldr4 { ankou 2s 2s 2s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 3s 3s 3s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 0s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 0s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 0s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 4s 4s 4s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 4s 0s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 0s 6s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 4s 0s 6s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 5s 5s 5s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 5s 5s 0s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 0s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 0s 6s 7s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 0s 6s 7s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 6s 6s 6s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 7s 7s 7s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s penchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s ryanmen_high }),
			make_scorable_hand!(@meldr4 { ankou 8s 8s 8s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 9s 9s 9s shanpon }),
		]
	}

	#[test]
	fn to_meld() {
		for ma in melds_last() {
			for (ts, new_tile) in fourth_meld_to_tiles(ma) {
				let expected = ([], ma, ScorableHandRegularPair::antoi(t!(1p)));
				let actual: std::vec::Vec<_> =
					LookupForNewTile::new(
						Lookup::<1>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
						new_tile,
						TsumoOrRon::Tsumo,
					).collect();
				assert_eq!(actual, [expected], "{ma} on {new_tile} did not meld into {expected:?}, only into {actual:?}");
			}
		}

		// 124 -> X
		assert!(Lookup::<1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p]).unwrap()).next().is_none());
	}

	#[test]
	fn to_melds_2() {
		for ma in melds() {
			let ts @ [t1, t2, t3] = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			used.try_extend(ts).unwrap();

			for mb in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
				for ([t4, t5, t6, t7], new_tile) in fourth_meld_to_tiles(mb) {
					let mut used = used.clone();
					if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
						continue;
					}

					let expected =
						if let Some(mb) = mb.to_tanki() {
							let mut ms = [ma, mb];
							ms.sort_unstable();
							let [m3, m4] = ms;
							([m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
						}
						else {
							([ma], mb, ScorableHandRegularPair::antoi(t!(1p)))
						};

					let ts = [t1, t2, t3, t4, t5, t6, t7];
					let actual: std::vec::Vec<_> =
						LookupForNewTile::new(
							Lookup::<2>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
							new_tile,
							TsumoOrRon::Tsumo,
						).collect();

					assert!(
						actual.contains(&expected),
						"{ma} + {mb} on {new_tile} did not meld into {expected:?}, only into {actual:?}",
					);
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_3() {
		for (ma_i, ma) in melds().into_iter().enumerate() {
			let ts @ [t1, t2, t3] = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			used.try_extend(ts).unwrap();

			for &mb in &melds()[ma_i..] {
				let ts @ [t4, t5, t6] = meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend(ts).is_err() {
					continue;
				}

				for mc in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
					for ([t7, t8, t9, t10], new_tile) in fourth_meld_to_tiles(mc) {
						let mut used = used.clone();
						if used.try_extend([t7, t8, t9, t10, new_tile]).is_err() {
							continue;
						}

						let expected =
							if let Some(mc) = mc.to_tanki() {
								let mut ms = [ma, mb, mc];
								ms.sort_unstable();
								let [m2, m3, m4] = ms;
								([m2, m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
							}
							else {
								([ma, mb], mc, ScorableHandRegularPair::antoi(t!(1p)))
							};

						let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10];
						let actual: std::vec::Vec<_> =
							LookupForNewTile::new(
								Lookup::<3>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
								new_tile,
								TsumoOrRon::Tsumo,
							).collect();

						assert!(
							actual.contains(&expected),
							"{ma} + {mb} + {mc} on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
						);
					}
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_4() {
		for (ma_i, ma) in melds().into_iter().enumerate() {
			let ts @ [t1, t2, t3] = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			used.try_extend(ts).unwrap();

			for (mb_i, &mb) in melds()[ma_i..].iter().enumerate() {
				let ts @ [t4, t5, t6] = meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend(ts).is_err() {
					continue;
				}

				for &mc in &melds()[(ma_i + mb_i)..] {
					let ts @ [t7, t8, t9] = meld_to_tiles(mc);
					let mut used = used.clone();
					if used.try_extend(ts).is_err() {
						continue;
					}

					for md in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
						for ([t10, t11, t12, t13], new_tile) in fourth_meld_to_tiles(md) {
							let mut used = used.clone();
							if used.try_extend([t10, t11, t12, t13, new_tile]).is_err() {
								continue;
							}

							let expected =
								if let Some(md) = md.to_tanki() {
									let mut ms = [ma, mb, mc, md];
									ms.sort_unstable();
									let [m1, m2, m3, m4] = ms;
									([m1, m2, m3], ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(t!(1p)))
								}
								else {
									([ma, mb, mc], md, ScorableHandRegularPair::antoi(t!(1p)))
								};

							let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13];
							let actual: std::vec::Vec<_> =
								LookupForNewTile::new(
									Lookup::<4>::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
									new_tile,
									TsumoOrRon::Tsumo,
								).collect();

							assert!(
								actual.contains(&expected),
								"{ma} + {mb} + {mc} + {md} on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
							);
						}
					}
				}
			}
		}
	}
}
