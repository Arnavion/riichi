use generic_array::{
	ArrayLength,
	GenericArray,
	sequence::{Remove, Shorten},
	typenum::{
		Min, Minimum,
		Prod,
		Sum,
		U1, U2, U3, U4,
	},
};

use crate::{
	ArrayVec, ArrayVecIntoIter,
	KouWait,
	Number, NumberTile,
	ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ShunLowTileAndHasFiveRed, ShunWait,
	Tile, Tile27Set, Tile37CountedMultiSet, Tile37MultiSet, TsumoOrRon,
};

#[derive(Copy, Debug)]
struct Meld<M> {
	len: u8,
	ms: [core::mem::MaybeUninit<M>; 4],
}

// TODO(rustup): Clippy incorrectly suggests using `#[derive(Clone)]` but that does not compile since `MaybeUninit<T>: Clone` requires `T: Copy`.
#[expect(clippy::expl_impl_clone_on_copy)]
impl<M> Clone for Meld<M>
where
	M: Copy,
{
	fn clone(&self) -> Self {
		*self
	}
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
#[expect(clippy::eq_op)]
enum Honor {
	/// Ton
	WE = t!(E) as u8 - t!(E) as u8,
	/// Nan
	WS = t!(S) as u8 - t!(E) as u8,
	/// Shaa
	WW = t!(W) as u8 - t!(E) as u8,
	/// Pei
	WN = t!(N) as u8 - t!(E) as u8,
	/// Haku
	DW = t!(Wh) as u8 - t!(E) as u8,
	/// Hatsu
	DG = t!(G) as u8 - t!(E) as u8,
	/// Chun
	DR = t!(R) as u8 - t!(E) as u8,
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
	use {Some as Y, None as N};
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

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
#[expect(clippy::eq_op)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K1 = Number::One as u8 - Number::One as u8,
	/// Ankou 222 / Pair 22
	K2 = Number::Two as u8 - Number::One as u8,
	/// Ankou 333 / Pair 33
	K3 = Number::Three as u8 - Number::One as u8,
	/// Ankou 444 / Pair 44
	K4 = Number::Four as u8 - Number::One as u8,
	/// Ankou 555 / Pair 55
	K5 = Number::Five as u8 - Number::One as u8,
	/// Ankou 550 / Pair 50
	K0 = Number::FiveRed as u8 - Number::One as u8,
	/// Ankou 666 / Pair 66
	K6 = Number::Six as u8 - Number::One as u8,
	/// Ankou 777 / Pair 77
	K7 = Number::Seven as u8 - Number::One as u8,
	/// Ankou 888 / Pair 88
	K8 = Number::Eight as u8 - Number::One as u8,
	/// Ankou 999 / Pair 99
	K9 = Number::Nine as u8 - Number::One as u8,

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
	use {Some as Y, None as N};
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

pub(crate) struct Lookup<NM>(LookupInner, core::marker::PhantomData<NM>);

// Common implementation independent of `NM` to combat monomorphization bloat.
#[derive(Clone, Debug, Default)]
struct LookupInner {
	ji: Option<&'static (Option<Honor>, Meld<Honor>)>,
	i_sou: u8,
	sou: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	i_pin: u8,
	pin: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	man: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	pair_suit: PairSuit,
}

#[derive(Clone, Copy, Debug, Default)]
#[repr(u8)]
enum PairSuit {
	#[default]
	Man = tn!(1m) as u8,
	Pin = tn!(1p) as u8,
	Sou = tn!(1s) as u8,
	Ji = t!(E) as u8,
}

impl<NM> Lookup<NM>
where
	NM: core::ops::Mul<U3>,
	Prod<NM, U3>: core::ops::Add<U2>,
{
	pub(crate) fn new(ts: &Tile37CountedMultiSet<Sum<Prod<NM, U3>, U2>>) -> Self {
		Self(LookupInner::new(ts.as_ref()), Default::default())
	}
}

impl<NM> Clone for Lookup<NM> {
	fn clone(&self) -> Self {
		Self(self.0.clone(), self.1)
	}
}

impl<NM> core::fmt::Debug for Lookup<NM> {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_tuple("Lookup")
			.field(&self.0)
			.finish()
	}
}

impl<NM> Default for Lookup<NM> {
	fn default() -> Self {
		Self(Default::default(), Default::default())
	}
}

impl<NM> Iterator for Lookup<NM>
where
	NM: ArrayLength,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		let mut melds = GenericArray::uninit();
		let pair = unsafe { self.0.next_to(&mut melds)? };
		// SAFETY: The size of `melds` is correct based on the number of tiles in `ts`. So if `self.0.next_to()` returned `Some(_)`,
		// we know that `melds` must have been completely filled with melds.
		let melds = unsafe { GenericArray::assume_init(melds) };
		Some((melds, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<NM> ExactSizeIterator for Lookup<NM>
where
	Self: Iterator,
{
	fn len(&self) -> usize {
		self.0.len()
	}
}

impl<NM> core::iter::FusedIterator for Lookup<NM>
where
	Self: Iterator,
{}

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
	unsafe fn make_pair(
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

pub(crate) struct LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
{
	current: ArrayVecIntoIter<(GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandPair), Minimum<Sum<NM, U2>, U4>>,
	lookup: Lookup<Sum<NM, U1>>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<NM> LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
{
	pub(crate) fn new(lookup: Lookup<Sum<NM, U1>>, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Self {
		Self {
			current: Default::default(),
			lookup,
			new_tile,
			tsumo_or_ron,
		}
	}
}

impl<NM> Clone for LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
{
	fn clone(&self) -> Self {
		Self {
			current: self.current.clone(),
			lookup: self.lookup.clone(),
			new_tile: self.new_tile,
			tsumo_or_ron: self.tsumo_or_ron,
		}
	}
}

impl<NM> core::fmt::Debug for LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("LookupForNewTile")
			.field("current", &self.current)
			.field("lookup", &self.lookup)
			.field("new_tile", &self.new_tile)
			.field("tsumo_or_ron", &self.tsumo_or_ron)
			.finish()
	}
}

impl<NM> Default for LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
{
	fn default() -> Self {
		Self {
			current: Default::default(),
			lookup: Default::default(),
			new_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
		}
	}
}

impl<NM> Iterator for LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
	Lookup<Sum<NM, U1>>: Iterator<Item = (GenericArray<ScorableHandMeld, Sum<NM, U1>>, ScorableHandPair)>,
	GenericArray<ScorableHandMeld, Sum<NM, U1>>:
		Copy +
		Remove<ScorableHandMeld, Sum<NM, U1>, Output = GenericArray<ScorableHandMeld, NM>> +
		Shorten<ScorableHandMeld, Shorter = GenericArray<ScorableHandMeld, NM>>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		const ONES: Tile27Set = t27set![1m, 1p, 1s];
		const SEVENS: Tile27Set = t27set![7m, 7p, 7s];

		loop {
			let Some((ms, md, pair)) = self.current.next() else {
				let (ms, pair) = self.lookup.next()?;
				let mut current = ArrayVec::new();
				//  pair.0 | new_tile |   should match
				// ========+==========+==================
				//    5m   |    5m    | yes, pair is 55m
				//    5m   |    0m    | no,  pair is 55m
				//    0m   |    5m    | yes, pair is 50m
				//    0m   |    0m    | yes, pair is 50m
				if pair.0 == self.new_tile || pair.0.remove_red() == self.new_tile {
					let (ms, md) = Shorten::pop_back(ms);
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
							if tile != self.new_tile && tile.remove_red() != self.new_tile {
								return None;
							}
							ScorableHandFourthMeld::kou(tile, self.tsumo_or_ron, KouWait::Shanpon)
						},

						ScorableHandMeld::Anjun(tile) => {
							let (t1, t2, t3) = tile.shun();
							let wait =
								if Tile::from(t1) == self.new_tile {
									if SEVENS.contains(t1) { ShunWait::Penchan } else { ShunWait::RyanmenLow }
								}
								else if Tile::from(t2) == self.new_tile {
									ShunWait::Kanchan
								}
								else if Tile::from(t3) == self.new_tile {
									if ONES.contains(t1) { ShunWait::Penchan } else { ShunWait::RyanmenHigh }
								}
								else {
									return None;
								};
							ScorableHandFourthMeld::shun(tile, self.tsumo_or_ron, wait)
						},

						_ => unsafe { core::hint::unreachable_unchecked(); },
					};
					let (_, ms) = unsafe { Remove::remove_unchecked(ms, i) };
					Some((ms, md, pair))
				}));
				self.current = current.into_iter();
				continue;
			};
			break Some((ms, md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_len = self.current.len();
		let (lookup_lo, lookup_hi) = self.lookup.size_hint();
		(current_len + lookup_lo, lookup_hi.map(|lookup_hi| current_len + lookup_hi * (NM::USIZE + 2)))
	}
}

impl<NM> core::iter::FusedIterator for LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2>,
	Sum<NM, U2>: Min<U4, Output: ArrayLength>,
	Self: Iterator,
{}

// Used by `make_hand!` expansion.
pub use generic_array;

#[cfg(test)]
mod tests {
	extern crate std;

	use crate::Tile37MultiSet;
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		match m {
			ScorableHandMeld::Ankou(t) => [t, t, t],
			ScorableHandMeld::Anjun(t) => {
				let (t1, t2, t3) = t.shun();
				[t1, t2, t3].map(Into::into)
			},
			_ => unreachable!(),
		}
	}

	fn fourth_meld_to_tiles(m: ScorableHandFourthMeld) -> (Tile, Tile, Tile, Tile, Tile, TsumoOrRon) {
		let tsumo_or_ron = match m {
			ScorableHandFourthMeld::Ankan(..) |
			ScorableHandFourthMeld::Minkan(..) |
			ScorableHandFourthMeld::Ankou(..) |
			ScorableHandFourthMeld::Minkou(_, KouWait::Tanki) |
			ScorableHandFourthMeld::Anjun(..) |
			ScorableHandFourthMeld::Minjun(_, ShunWait::Tanki)
				=> TsumoOrRon::Tsumo,

			ScorableHandFourthMeld::Minkou(_, KouWait::Shanpon) |
			ScorableHandFourthMeld::Minjun(_, ShunWait::Kanchan | ShunWait::Penchan | ShunWait::RyanmenLow | ShunWait::RyanmenHigh)
				=> TsumoOrRon::Ron,
		};

		match m {
			m @ (
				ScorableHandFourthMeld::Ankan(..) |
				ScorableHandFourthMeld::Minkan(..) |
				ScorableHandFourthMeld::Ankou(_, KouWait::Tanki) |
				ScorableHandFourthMeld::Minkou(_, KouWait::Tanki) |
				ScorableHandFourthMeld::Anjun(_, ShunWait::Tanki) |
				ScorableHandFourthMeld::Minjun(_, ShunWait::Tanki)
			) => {
				let [t1, t2, t3] = meld_to_tiles(m.into());
				(t1, t2, t3, t!(1p), t!(1p), tsumo_or_ron)
			},

			ScorableHandFourthMeld::Ankou(tile, KouWait::Shanpon) |
			ScorableHandFourthMeld::Minkou(tile, KouWait::Shanpon) =>
				(tile, tile, t!(1p), t!(1p), tile, tsumo_or_ron),

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Kanchan) |
			ScorableHandFourthMeld::Minjun(tile, ShunWait::Kanchan) => {
				let (t1, t2, t3) = tile.shun();
				(t1.into(), t3.into(), t!(1p), t!(1p), t2.into(), tsumo_or_ron)
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Penchan) |
			ScorableHandFourthMeld::Minjun(tile, ShunWait::Penchan) => {
				let (t1, t2, t3) = tile.shun();
				if t1.number() == Number::One {
					(t1.into(), t2.into(), t!(1p), t!(1p), t3.into(), tsumo_or_ron)
				}
				else if t1.number() == Number::Seven {
					(t2.into(), t3.into(), t!(1p), t!(1p), t1.into(), tsumo_or_ron)
				}
				else {
					unreachable!();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenLow) |
			ScorableHandFourthMeld::Minjun(tile, ShunWait::RyanmenLow) => {
				let (t1, t2, t3) = tile.shun();
				(t2.into(), t3.into(), t!(1p), t!(1p), t1.into(), tsumo_or_ron)
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenHigh) |
			ScorableHandFourthMeld::Minjun(tile, ShunWait::RyanmenHigh) => {
				let (t1, t2, t3) = tile.shun();
				(t1.into(), t2.into(), t!(1p), t!(1p), t3.into(), tsumo_or_ron)
			},
		}
	}

	fn melds() -> [ScorableHandMeld; 16] {
		[
			make_scorable_hand!(@meld { ankou 1s 1s 1s }),
			make_scorable_hand!(@meld { ankou 2s 2s 2s }),
			make_scorable_hand!(@meld { ankou 3s 3s 3s }),
			make_scorable_hand!(@meld { ankou 4s 4s 4s }),
			make_scorable_hand!(@meld { ankou 5s 5s 5s }),
			make_scorable_hand!(@meld { ankou 6s 6s 6s }),
			make_scorable_hand!(@meld { ankou 7s 7s 7s }),
			make_scorable_hand!(@meld { ankou 8s 8s 8s }),
			make_scorable_hand!(@meld { ankou 9s 9s 9s }),
			make_scorable_hand!(@meld { anjun 1s 2s 3s }),
			make_scorable_hand!(@meld { anjun 2s 3s 4s }),
			make_scorable_hand!(@meld { anjun 3s 4s 5s }),
			make_scorable_hand!(@meld { anjun 4s 5s 6s }),
			make_scorable_hand!(@meld { anjun 5s 6s 7s }),
			make_scorable_hand!(@meld { anjun 6s 7s 8s }),
			make_scorable_hand!(@meld { anjun 7s 8s 9s }),
		]
	}

	fn melds_last() -> [ScorableHandFourthMeld; 30] {
		[
			make_scorable_hand!(@meldr4 { ankou 1s 1s 1s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 2s 2s 2s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 3s 3s 3s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 4s 4s 4s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 5s 5s 5s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 6s 6s 6s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 7s 7s 7s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 8s 8s 8s shanpon }),
			make_scorable_hand!(@meldr4 { ankou 9s 9s 9s shanpon }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s penchan }),
			make_scorable_hand!(@meldr4 { anjun 1s 2s 3s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 2s 3s 4s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 3s 4s 5s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 4s 5s 6s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 5s 6s 7s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_low }),
			make_scorable_hand!(@meldr4 { anjun 6s 7s 8s ryanmen_high }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s kanchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s penchan }),
			make_scorable_hand!(@meldr4 { anjun 7s 8s 9s ryanmen_high }),
		]
	}

	#[test]
	fn to_meld() {
		for ma in melds_last() {
			let (t1, t2, t3, t4, new_tile, tsumo_or_ron) = fourth_meld_to_tiles(ma);
			let ts = [t1, t2, t3, t4].into();
			let expected = ([].into(), ma, ScorableHandPair(t!(1p)));
			let actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()), new_tile, tsumo_or_ron).collect();
			assert_eq!(actual, [expected], "{ma:?} did not meld into {expected:?}, only into {actual:?}");
		}

		// 124 -> X
		assert!(Lookup::<U1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p].into()).unwrap()).next().is_none());
	}

	#[test]
	fn to_melds_2() {
		for ma in melds() {
			let ts = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			if used.try_extend(ts).is_err() {
				continue;
			}
			let [t1, t2, t3] = ts;

			for mb in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
				let (t4, t5, t6, t7, new_tile, tsumo_or_ron) = fourth_meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
					continue;
				}

				let mut expected = ArrayVec::<_, U2>::new();
				expected.push(([ma].into(), mb, ScorableHandPair(t!(1p)))).unwrap();
				if let Some(mb) = mb.to_tanki() {
					expected.push(([mb].into(), ScorableHandFourthMeld::tanki(ma), ScorableHandPair(t!(1p)))).unwrap();
				}

				let ts = [t1, t2, t3, t4, t5, t6, t7].into();
				let actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()), new_tile, tsumo_or_ron).collect();
				assert!(
					expected.iter().any(|expected| actual.contains(expected)),
					"{ma:?} + {mb:?} did not meld into any of {expected:?}, only into {actual:?}",
				);
			}
		}
	}

	#[test]
	fn to_melds_3() {
		for ma in melds() {
			let ts = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			if used.try_extend(ts).is_err() {
				continue;
			}
			let [t1, t2, t3] = ts;

			for mb in melds() {
				let ts = meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend(ts).is_err() {
					continue;
				}
				let [t4, t5, t6] = ts;

				for mc in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
					let (t7, t8, t9, t10, new_tile, tsumo_or_ron) = fourth_meld_to_tiles(mc);
					let mut used = used.clone();
					if used.try_extend([t7, t8, t9, t10, new_tile]).is_err() {
						continue;
					}

					let mut expected = ArrayVec::<_, U3>::new();
					{
						let ms = { let mut ms = [ma, mb]; ms.sort_unstable(); ms.into() };
						expected.push((ms, mc, ScorableHandPair(t!(1p)))).unwrap();
					}
					if let Some(mc) = mc.to_tanki() {
						let ms = { let mut ms = [ma, mc]; ms.sort_unstable(); ms.into() };
						expected.push((ms, ScorableHandFourthMeld::tanki(mb), ScorableHandPair(t!(1p)))).unwrap();
						let ms = { let mut ms = [mb, mc]; ms.sort_unstable(); ms.into() };
						expected.push((ms, ScorableHandFourthMeld::tanki(ma), ScorableHandPair(t!(1p)))).unwrap();
					}

					let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into();
					let mut actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()), new_tile, tsumo_or_ron).collect();
					for (ms, ..) in &mut actual { ms.sort_unstable(); }
					assert!(
						expected.iter().any(|expected| actual.contains(expected)),
						"{ma:?} + {mb:?} + {mc:?} did not meld into any of {expected:?}, only into {actual:?}",
					);
				}
			}
		}
	}

	#[test]
	fn to_melds_4() {
		for ma in melds() {
			let ts = meld_to_tiles(ma);
			let mut used = Tile37MultiSet::default();
			if used.try_extend(ts).is_err() {
				continue;
			}
			let [t1, t2, t3] = ts;

			for mb in melds() {
				let ts = meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend(ts).is_err() {
					continue;
				}
				let [t4, t5, t6] = ts;

				for mc in melds() {
					let ts = meld_to_tiles(mc);
					let mut used = used.clone();
					if used.try_extend(ts).is_err() {
						continue;
					}
					let [t7, t8, t9] = ts;

					for md in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
						let (t10, t11, t12, t13, new_tile, tsumo_or_ron) = fourth_meld_to_tiles(md);
						let mut used = used.clone();
						if used.try_extend([t10, t11, t12, t13, new_tile]).is_err() {
							continue;
						}

						let mut expected = ArrayVec::<_, U4>::new();
						{
							let ms = { let mut ms = [ma, mb, mc]; ms.sort_unstable(); ms.into() };
							expected.push((ms, md, ScorableHandPair(t!(1p)))).unwrap();
						}
						if let Some(md) = md.to_tanki() {
							let ms = { let mut ms = [ma, mb, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ScorableHandFourthMeld::tanki(mc), ScorableHandPair(t!(1p)))).unwrap();
							let ms = { let mut ms = [ma, mc, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ScorableHandFourthMeld::tanki(mb), ScorableHandPair(t!(1p)))).unwrap();
							let ms = { let mut ms = [mb, mc, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ScorableHandFourthMeld::tanki(ma), ScorableHandPair(t!(1p)))).unwrap();
						}

						let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into();
						let mut actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()), new_tile, tsumo_or_ron).collect();
						for (ms, ..) in &mut actual { ms.sort_unstable(); }
						assert!(
							expected.iter().any(|expected| actual.contains(expected)),
							"{ma:?} + {mb:?} + {mc:?} + {md:?} did not meld into any of {expected:?}, only into {actual:?}",
						);
					}
				}
			}
		}
	}
}
