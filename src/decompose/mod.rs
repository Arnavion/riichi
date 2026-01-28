use generic_array::{
	ArrayLength,
	GenericArray,
	typenum::{
		Prod,
		Sum,
		U0, U1, U2, U3,
	},
};

use crate::{
	ArrayVec, ArrayVecIntoIter,
	except,
	KouWait,
	Number, NumberSuit, NumberTile, NumberTileClassified,
	ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ShunLowNumber, ShunLowTileAndHasFiveRed, ShunWait,
	Tile, Tile27Set, TsumoOrRon,
};

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

#[derive(Copy, Debug)]
struct Meld<M> {
	len: u8,
	ms: [core::mem::MaybeUninit<M>; 4],
}

// TODO(rustup): Clippy incorrectly suggests using `#[derive(Clone)]` but that does not compile since `MaybeUninit<T>: Clone` requires `T: Copy`.
#[expect(clippy::expl_impl_clone_on_copy)]
impl<M> Clone for Meld<M> where M: Copy {
	fn clone(&self) -> Self {
		*self
	}
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K1 = Number::One as u8,
	/// Ankou 222 / Pair 22
	K2 = Number::Two as u8,
	/// Ankou 333 / Pair 33
	K3 = Number::Three as u8,
	/// Ankou 444 / Pair 44
	K4 = Number::Four as u8,
	/// Ankou 555 / Pair 55
	K5 = Number::Five as u8,
	/// Ankou 550 / Pair 50
	K0 = Number::FiveRed as u8,
	/// Ankou 666 / Pair 66
	K6 = Number::Six as u8,
	/// Ankou 777 / Pair 77
	K7 = Number::Seven as u8,
	/// Ankou 888 / Pair 88
	K8 = Number::Eight as u8,
	/// Ankou 999 / Pair 99
	K9 = Number::Nine as u8,

	/// Shun 123
	S0 = (ShunLowTileAndHasFiveRed::Man1 as u8) | (1 << 7),
	/// Shun 234
	S1 = (ShunLowTileAndHasFiveRed::Man2 as u8) | (1 << 7),
	/// Shun 345
	S2 = (ShunLowTileAndHasFiveRed::Man3 as u8) | (1 << 7),
	/// Shun 340
	S3 = (ShunLowTileAndHasFiveRed::Man3Red as u8) | (1 << 7),
	/// Shun 456
	S4 = (ShunLowTileAndHasFiveRed::Man4 as u8) | (1 << 7),
	/// Shun 406
	S5 = (ShunLowTileAndHasFiveRed::Man4Red as u8) | (1 << 7),
	/// Shun 567
	S6 = (ShunLowTileAndHasFiveRed::Man5 as u8) | (1 << 7),
	/// Shun 067
	S7 = (ShunLowTileAndHasFiveRed::Man5Red as u8) | (1 << 7),
	/// Shun 678
	S8 = (ShunLowTileAndHasFiveRed::Man6 as u8) | (1 << 7),
	/// Shun 789
	S9 = (ShunLowTileAndHasFiveRed::Man7 as u8) | (1 << 7),
}

impl NumberMeld {
	fn with_suit(self, suit: NumberSuit) -> ScorableHandMeld {
		let number = self as u8;
		if number & (1 << 7) == 0 {
			// Ankou
			let number = unsafe { core::mem::transmute::<u8, Number>(number) };
			let t = Tile::from(NumberTile::from(NumberTileClassified { suit, number }));
			ScorableHandMeld::Ankou(t)
		}
		else {
			// Anjun
			let number = number & !(1 << 7);
			let t = (suit as u8) * (tn!(1p) as u8 - tn!(1m) as u8) + (number - ShunLowNumber::One as u8) + tn!(1m) as u8;
			let t = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(t) };
			ScorableHandMeld::Anjun(t)
		}
	}
}

impl Meld<NumberMeld> {
	/// # Safety
	///
	/// `melds` must have enough elements to write all of `self`'s melds.
	unsafe fn write_to<'a>(self, mut melds: impl Iterator<Item = &'a mut core::mem::MaybeUninit<ScorableHandMeld>>, suit: NumberSuit) {
		let len = usize::from(self.len);
		unsafe { core::hint::assert_unchecked(len <= self.ms.len()); }
		for m in &self.ms[..len] {
			let m = unsafe { m.assume_init() };
			let slot = melds.next();
			let slot = unsafe { slot.unwrap_unchecked() };
			slot.write(m.with_suit(suit));
		}
	}
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
enum Honor {
	/// Ton
	WE = t!(E) as u8,
	/// Nan
	WS = t!(S) as u8,
	/// Shaa
	WW = t!(W) as u8,
	/// Pei
	WN = t!(N) as u8,
	/// Haku
	DW = t!(Wh) as u8,
	/// Hatsu
	DG = t!(G) as u8,
	/// Chun
	DR = t!(R) as u8,
}

impl From<Honor> for ScorableHandMeld {
	fn from(honor: Honor) -> Self {
		let t = unsafe { core::mem::transmute::<u8, Tile>(honor as u8) };
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

#[derive(Clone, Debug)]
pub(crate) struct Keys<NT>(KeysInner, core::marker::PhantomData<NT>);

// Common implementation independent of `NT` to combat monomorphization bloat.
#[derive(Clone, Debug, Default)]
struct KeysInner {
	counts: [u32; 4],
	totals: [u8; 4],
}

impl<NT> Keys<NT> {
	pub(crate) fn new(ts: GenericArray<Tile, NT>) -> Keys<NT> where NT: ArrayLength {
		let mut inner = KeysInner::default();
		for t in ts {
			inner.push(t);
		}
		Self(inner, Default::default())
	}

	pub(crate) fn push(self, t: Tile) -> Keys<Sum<NT, U1>> where NT: core::ops::Add<U1> {
		let mut inner = self.0;
		inner.push(t);
		Keys(inner, Default::default())
	}
}

impl Default for Keys<U0> {
	fn default() -> Self {
		Self(KeysInner::default(), Default::default())
	}
}

impl KeysInner {
	fn push(&mut self, t: Tile) {
		let i = 3 - (usize::from(t < t!(1p)) + usize::from(t < t!(1s)) + usize::from(t < t!(E)));
		let offset =
			((t as usize - t!(1m) as usize) >> 1)
			+ 3 - (usize::from(t < t!(0m)) + usize::from(t < t!(0p)) + usize::from(t < t!(0s)))
			- 10 * i;

		self.counts[i] += 0b1 << (offset * 3);
		self.totals[i] += 1;
	}
}

pub(crate) struct Lookup<NM>(LookupInner, core::marker::PhantomData<NM>);

// Common implementation independent of `NM` to combat monomorphization bloat.
#[derive(Clone, Debug)]
struct LookupInner {
	// The largest number slice will be 8 elements long, so u8 is sufficient to count.
	man: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	pin: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	i_pin: u8,
	sou: &'static [(Option<NumberMeld>, Meld<NumberMeld>)],
	i_sou: u8,
	ji: Option<&'static (u32, Option<Honor>, Meld<Honor>)>,
}

impl<NM> Lookup<NM>
where
	NM: core::ops::Mul<U3>,
	Prod<NM, U3>: core::ops::Add<U2>,
{
	pub(crate) fn new(keys: &Keys<Sum<Prod<NM, U3>, U2>>) -> Self {
		Self(LookupInner::new(&keys.0), Default::default())
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

impl<NM> Iterator for Lookup<NM> where NM: ArrayLength {
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		let mut melds = GenericArray::uninit();
		let pair = unsafe { self.0.next_to(&mut melds)? };
		// SAFETY: The size of `melds` is correct based on the number of keys in `keys`. So if `self.0.next_to()` returned `Some(_)`,
		// we know that `melds` must have been completely filled with melds.
		let melds = unsafe { GenericArray::assume_init(melds) };
		Some((melds, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.0.size_hint()
	}
}

impl LookupInner {
	fn new(keys: &KeysInner) -> Self {
		fn lookup_numbers(key: u32, len: u8) -> &'static [(Option<NumberMeld>, Meld<NumberMeld>)] {
			let map = match len {
				2 => numbers::TWOS,
				3 => numbers::THREES,
				5 => numbers::FIVES,
				6 => numbers::SIXES,
				8 => numbers::EIGHTS,
				9 => numbers::NINES,
				11 => numbers::ELEVENS,
				12 => numbers::TWELVES,
				14 => numbers::FOURTEENS,
				_ => numbers::ZEROS,
			};
			map.binary_search_by_key(&key, |(key, _, _)| *key).ok().map_or(&[], |i| {
				let (_, storage_start, storage_end) = map[i];
				let storage_start = usize::from(storage_start);
				let storage_end = usize::from(storage_end);
				unsafe { core::hint::assert_unchecked(storage_start < storage_end); }
				unsafe { core::hint::assert_unchecked(storage_end <= numbers::STORAGE.len()); }
				&numbers::STORAGE[storage_start..storage_end]
			})
		}

		fn lookup_honors(key: u32, len: u8) -> Option<&'static (u32, Option<Honor>, Meld<Honor>)> {
			let map = match len {
				2 => honors::TWOS,
				3 => honors::THREES,
				5 => honors::FIVES,
				6 => honors::SIXES,
				8 => honors::EIGHTS,
				9 => honors::NINES,
				11 => honors::ELEVENS,
				12 => honors::TWELVES,
				14 => honors::FOURTEENS,
				_ => honors::ZEROS,
			};
			map.binary_search_by_key(&key, |(key, _, _)| *key).ok().map(|i| &map[i])
		}

		let man = lookup_numbers(keys.counts[0], keys.totals[0]);
		let pin = lookup_numbers(keys.counts[1], keys.totals[1]);
		let sou = lookup_numbers(keys.counts[2], keys.totals[2]);
		let ji = lookup_honors(keys.counts[3], keys.totals[3]);

		// All elements of each slice have the same shape. Eg if the first element of `man` is `(Some(_), m2(..))`,
		// then the other elements of `man` will also be `(Some(_), m2(..))`. This means that if we find one combination of elements
		// that produces zero or more than two pairs, then every combination will also do that. So we can just terminate early.
		let num_pairs =
			man.first().map_or(0, |(pair, _)| usize::from(pair.is_some())) +
			pin.first().map_or(0, |(pair, _)| usize::from(pair.is_some())) +
			sou.first().map_or(0, |(pair, _)| usize::from(pair.is_some())) +
			ji.map_or(0, |(_, pair, _)| usize::from(pair.is_some()));
		let ji = if num_pairs == 1 { ji } else { None };

		Self {
			man,
			pin,
			i_pin: 0,
			sou,
			i_sou: 0,
			ji,
		}
	}

	/// # Safety
	///
	/// `melds` must have enough elements to write (number of tiles - 2) / 3 melds.
	unsafe fn next_to(&mut self, melds: &mut [core::mem::MaybeUninit<ScorableHandMeld>]) -> Option<ScorableHandPair> {
		let &(_, ji_pair, ji_melds) = self.ji?;

		let mut i_pin = usize::from(self.i_pin);
		let mut i_sou = usize::from(self.i_sou);

		if i_sou >= self.sou.len() {
			i_sou = 0;
			i_pin += 1;
		}
		let Some(&(sou_pair, sou_melds)) = self.sou.get(i_sou) else {
			self.ji = None;
			return None;
		};

		if i_pin >= self.pin.len() {
			i_pin = 0;
			self.man = self.man.get(1..).unwrap_or(&[]);
		}
		let Some(&(pin_pair, pin_melds)) = self.pin.get(i_pin) else {
			self.ji = None;
			return None;
		};

		let Some(&(man_pair, man_melds)) = self.man.first() else {
			self.ji = None;
			return None;
		};

		let pair = match ((man_pair, NumberSuit::Man), (pin_pair, NumberSuit::Pin), (sou_pair, NumberSuit::Sou), ji_pair) {
			((Some(n), suit), (None, _), (None, _), None) |
			((None, _), (Some(n), suit), (None, _), None) |
			((None, _), (None, _), (Some(n), suit), None) => {
				let number = unsafe { core::mem::transmute::<u8, Number>(n as u8) };
				Tile::from(NumberTile::from(NumberTileClassified { suit, number }))
			},

			((None, _), (None, _), (None, _), Some(t)) => unsafe { core::mem::transmute::<u8, Tile>(t as u8) },

			// One and only pair is guaranteed to exist at the end of `new()`.
			_ => unsafe { core::hint::unreachable_unchecked(); },
		};
		let pair = ScorableHandPair(pair);

		let mut melds = melds.iter_mut();
		// SAFETY: In order to have gotten here, we know that two of the given tiles correspond to a pair and the rest are in melds.
		// If there was not one pair, we would've returned a neutered iterator in `new()`.
		// If one or more of the tiles did not form a valid meld, the corresponding slice would've been empty and we would've returned when trying to fetch the slice element.
		//
		// So, as long as the caller upheld our safety requirement, we will fill the `melds` slice exactly.
		unsafe { man_melds.write_to(&mut melds, NumberSuit::Man); }
		unsafe { pin_melds.write_to(&mut melds, NumberSuit::Pin); }
		unsafe { sou_melds.write_to(&mut melds, NumberSuit::Sou); }
		unsafe { ji_melds.write_to(melds); }

		#[expect(clippy::cast_possible_truncation)]
		{
			self.i_pin = i_pin as u8;
			self.i_sou = (i_sou as u8) + 1;
		}

		Some(pair)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let max = self.man.len() * self.pin.len() * self.sou.len() * usize::from(self.ji.is_some());
		let processed =
			usize::from(self.i_pin) * self.sou.len() * usize::from(self.ji.is_some()) +
			usize::from(self.i_sou) * usize::from(self.ji.is_some());
		let remaining = max.saturating_sub(processed);
		(0, Some(remaining))
	}
}

pub(crate) struct LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2, Output: ArrayLength>,
{
	current: ArrayVecIntoIter<(GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandPair), Sum<NM, U2>>,
	lookup: Lookup<Sum<NM, U1>>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<NM> LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2, Output: ArrayLength>,
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
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2, Output: ArrayLength>,
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
	NM: ArrayLength + core::ops::Add<U1> + core::ops::Add<U2, Output: ArrayLength>,
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

impl<NM> Iterator for LookupForNewTile<NM>
where
	NM: ArrayLength + core::ops::Add<U1, Output: ArrayLength + core::ops::Sub<U1, Output = NM>> + core::ops::Add<U2, Output: ArrayLength>,
	Lookup<Sum<NM, U1>>: Iterator<Item = (GenericArray<ScorableHandMeld, Sum<NM, U1>>, ScorableHandPair)>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current.next() else {
				let (ms, pair) = self.lookup.next()?;
				let mut current = ArrayVec::new();
				//  pair.0 | new_tile |  should match
				// ========+==========+==================
				//    5m   |    5m    | yes, pair is 55m
				//    5m   |    0m    | no,  pair is 55m
				//    0m   |    5m    | yes, pair is 50m
				//    0m   |    0m    | yes, pair is 50m
				if pair.0 == self.new_tile || pair.0.remove_red() == self.new_tile {
					let md = ms[ms.len() - 1];
					let ms = unsafe { except(&ms, [ms.len() - 1].into()) };
					unsafe { current.push_unchecked((ms, md.into(), pair)); }
				}
				for (i, &md) in ms.iter().enumerate() {
					if let Some(md) = new_tile_in_meld(md, self.new_tile, self.tsumo_or_ron) {
						let ms = unsafe { except(&ms, [i].into()) };
						unsafe { current.push_unchecked((ms, md, pair)); }
					}
				}
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

fn new_tile_in_meld(m: ScorableHandMeld, new_tile: Tile, tsumo_or_ron: TsumoOrRon) -> Option<ScorableHandFourthMeld> {
	const ONES: Tile27Set = t27set! { 1m, 1p, 1s };
	const SEVENS: Tile27Set = t27set! { 7m, 7p, 7s };

	match m {
		ScorableHandMeld::Ankou(tile) => {
			//  tile | new_tile |  should match
			// ======+==========+==================
			//   5m  |    5m    | yes, kou is 555m
			//   5m  |    0m    | no,  kou is 555m
			//   0m  |    5m    | yes, kou is 550m
			//   0m  |    0m    | yes, kou is 550m
			(tile == new_tile || tile.remove_red() == new_tile).then(|| ScorableHandFourthMeld::kou(tile, tsumo_or_ron, KouWait::Shanpon))
		},

		ScorableHandMeld::Anjun(tile) => {
			let (t1, t2, t3) = tile.shun();
			if Tile::from(t1) == new_tile {
				if SEVENS.contains(t1) {
					Some(ScorableHandFourthMeld::shun(tile, tsumo_or_ron, ShunWait::Penchan))
				}
				else {
					Some(ScorableHandFourthMeld::shun(tile, tsumo_or_ron, ShunWait::RyanmenLow))
				}
			}
			else if Tile::from(t2) == new_tile {
				Some(ScorableHandFourthMeld::shun(tile, tsumo_or_ron, ShunWait::Kanchan))
			}
			else if Tile::from(t3) == new_tile {
				if ONES.contains(t1) {
					Some(ScorableHandFourthMeld::shun(tile, tsumo_or_ron, ShunWait::Penchan))
				}
				else {
					Some(ScorableHandFourthMeld::shun(tile, tsumo_or_ron, ShunWait::RyanmenHigh))
				}
			}
			else {
				None
			}
		},

		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

	use generic_array::typenum::U4;

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
				else {
					assert!(t1.number() == Number::Seven);
					(t2.into(), t3.into(), t!(1p), t!(1p), t1.into(), tsumo_or_ron)
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
			let actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Keys::new(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
			assert_eq!(actual, [expected], "{ma:?} did not meld into {expected:?}, only into {actual:?}");
		}

		// 124 -> X
		assert!(Lookup::<U1>::new(&Keys::new([t!(1s), t!(2s), t!(4s), t!(1p), t!(1p)].into())).next().is_none());
	}

	#[test]
	fn to_melds_2() {
		for ma in melds() {
			let ts = meld_to_tiles(ma);
			let mut used: Tile37MultiSet = Default::default();
			if used.try_extend(ts).is_err() {
				continue;
			}
			let [t1, t2, t3] = ts;

			for mb in melds().into_iter().map(ScorableHandFourthMeld::from).chain(melds_last()) {
				let (t4, t5, t6, t7, new_tile, tsumo_or_ron) = fourth_meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
					continue;
				}

				let mut expected = ArrayVec::<_, U2>::new();
				expected.push(([ma].into(), mb, ScorableHandPair(t!(1p)))).unwrap();
				if let Some(mb) = mb.to_tanki() {
					expected.push(([mb].into(), ma.into(), ScorableHandPair(t!(1p)))).unwrap();
				}

				let ts = [t1, t2, t3, t4, t5, t6, t7].into();
				let actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Keys::new(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
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
			let mut used: Tile37MultiSet = Default::default();
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

				for mc in melds().into_iter().map(ScorableHandFourthMeld::from).chain(melds_last()) {
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
						expected.push((ms, mb.into(), ScorableHandPair(t!(1p)))).unwrap();
						let ms = { let mut ms = [mb, mc]; ms.sort_unstable(); ms.into() };
						expected.push((ms, ma.into(), ScorableHandPair(t!(1p)))).unwrap();
					}

					let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into();
					let mut actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Keys::new(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
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
			let mut used: Tile37MultiSet = Default::default();
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

					for md in melds().into_iter().map(ScorableHandFourthMeld::from).chain(melds_last()) {
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
							expected.push((ms, mc.into(), ScorableHandPair(t!(1p)))).unwrap();
							let ms = { let mut ms = [ma, mc, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, mb.into(), ScorableHandPair(t!(1p)))).unwrap();
							let ms = { let mut ms = [mb, mc, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ma.into(), ScorableHandPair(t!(1p)))).unwrap();
						}

						let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into();
						let mut actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(&Keys::new(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
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
