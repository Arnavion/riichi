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
	Number, NumberSuit, NumberTile, NumberTileClassified,
	ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ShunLowNumber, ShunLowTileAndHasFiveRed,
	Tile, Tile27Set, TsumoOrRon,
};

#[allow(clippy::enum_glob_use)]
#[path = "honors.generated.rs"]
mod honors;

#[allow(clippy::enum_glob_use)]
#[path = "numbers.generated.rs"]
mod numbers;

#[derive(Clone, Copy, Debug)]
enum Meld<M> {
	M0,
	M1(M),
	M2(M, M),
	M3(M, M, M),
	M4(M, M, M, M),
}

#[derive(Clone, Copy, Debug)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K0 = 0x00,
	/// Ankou 222 / Pair 22
	K1 = 0x04,
	/// Ankou 333 / Pair 33
	K2 = 0x08,
	/// Ankou 444 / Pair 44
	K4 = 0x0C,
	/// Ankou 555 / Pair 55
	K6 = 0x10,
	/// Ankou 550 / Pair 50
	K7 = 0x12,
	/// Ankou 666 / Pair 66
	K8 = 0x14,
	/// Ankou 777 / Pair 77
	K9 = 0x18,
	/// Ankou 888 / Pair 88
	KA = 0x1C,
	/// Ankou 999 / Pair 99
	KB = 0x20,

	/// Shun 123
	S0 = 0x01,
	/// Shun 234
	S1 = 0x05,
	/// Shun 345
	S2 = 0x09,
	/// Shun 340
	S3 = 0x0B,
	/// Shun 456
	S4 = 0x0D,
	/// Shun 406
	S5 = 0x0F,
	/// Shun 567
	S6 = 0x11,
	/// Shun 067
	S7 = 0x13,
	/// Shun 678
	S8 = 0x15,
	/// Shun 789
	S9 = 0x19,
}

impl NumberMeld {
	fn with_suit(self, suit: NumberSuit) -> ScorableHandMeld {
		let number = self as u8;
		if number & 1 == 0 {
			// Ankou
			let number = number >> 1;
			let number = unsafe { core::mem::transmute::<u8, Number>(number) };
			let t = Tile::from(NumberTile::from(NumberTileClassified { suit, number }));
			ScorableHandMeld::Ankou(t)
		}
		else {
			// Anjun
			let number = number >> 1;
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
		match self {
			Self::M0 => (),

			Self::M1(m1) => {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m1.with_suit(suit));
			},

			Self::M2(m1, m2) => for m in [m1, m2] {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m.with_suit(suit));
			},

			Self::M3(m1, m2, m3) => for m in [m1, m2, m3] {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m.with_suit(suit));
			},

			Self::M4(m1, m2, m3, m4) => for m in [m1, m2, m3, m4] {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m.with_suit(suit));
			},
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
		match self {
			Self::M0 => (),

			Self::M1(m1) => {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m1.into());
			},

			Self::M2(m1, m2) => for m in [m1, m2] {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m.into());
			},

			Self::M3(m1, m2, m3) => for m in [m1, m2, m3] {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m.into());
			},

			Self::M4(m1, m2, m3, m4) => for m in [m1, m2, m3, m4] {
				let slot = melds.next();
				let slot = unsafe { slot.unwrap_unchecked() };
				slot.write(m.into());
			},
		}
	}
}

#[derive(Clone, Debug)]
pub(crate) struct Keys<NT> {
	man: u32,
	i_man: u8,
	pin: u32,
	i_pin: u8,
	sou: u32,
	i_sou: u8,
	ji: u32,
	i_ji: u8,
	_nt: core::marker::PhantomData<NT>,
}

impl<NT> Keys<NT> {
	pub(crate) fn push(mut self, t: Tile) -> Keys<Sum<NT, U1>> where NT: core::ops::Add<U1> {
		self.push_inner(t);
		Keys {
			man: self.man,
			i_man: self.i_man,
			pin: self.pin,
			i_pin: self.i_pin,
			sou: self.sou,
			i_sou: self.i_sou,
			ji: self.ji,
			i_ji: self.i_ji,
			_nt: Default::default(),
		}
	}

	pub(crate) fn push_all<N>(mut self, ts: GenericArray<Tile, N>) -> Keys<Sum<NT, N>> where NT: core::ops::Add<N>, N: ArrayLength {
		for t in ts {
			self.push_inner(t);
		}
		Keys {
			man: self.man,
			i_man: self.i_man,
			pin: self.pin,
			i_pin: self.i_pin,
			sou: self.sou,
			i_sou: self.i_sou,
			ji: self.ji,
			i_ji: self.i_ji,
			_nt: Default::default(),
		}
	}

	fn push_inner(&mut self, t: Tile) {
		let (inner, i_inner, offset) =
			if let Ok(t) = NumberTile::try_from(t) {
				let NumberTileClassified { suit, number } = t.into();
				let (inner, i_inner) = match suit {
					NumberSuit::Man => (&mut self.man, &mut self.i_man),
					NumberSuit::Pin => (&mut self.pin, &mut self.i_pin),
					NumberSuit::Sou => (&mut self.sou, &mut self.i_sou),
				};
				let offset = ((number as u8) >> 1) + u8::from(number >= Number::FiveRed);
				(inner, i_inner, offset)
			}
			else {
				(&mut self.ji, &mut self.i_ji, (t as u8 - t!(E) as u8) >> 1)
			};
		*inner += 0b1 << (offset * 3);
		*i_inner += 1;
	}
}

impl Default for Keys<U0> {
	fn default() -> Self {
		Self {
			man: 0,
			i_man: 0,
			pin: 0,
			i_pin: 0,
			sou: 0,
			i_sou: 0,
			ji: 0,
			i_ji: 0,
			_nt: Default::default(),
		}
	}
}

pub(crate) struct Lookup<NM>(LookupInner, core::marker::PhantomData<NM>);

// Common implementation independent of `NM` to combat monomorphization bloat.
#[derive(Clone, Debug)]
struct LookupInner {
	// The largest number slice will be 8 elements long, so u8 is sufficient to count.
	man: &'static [(Meld<NumberMeld>, Option<NumberMeld>)],
	pin: &'static [(Meld<NumberMeld>, Option<NumberMeld>)],
	i_pin: u8,
	sou: &'static [(Meld<NumberMeld>, Option<NumberMeld>)],
	i_sou: u8,
	ji: Option<&'static (u32, Meld<Honor>, Option<Honor>)>,
}

impl<NM> Lookup<NM>
where
	NM: core::ops::Mul<U3>,
	Prod<NM, U3>: core::ops::Add<U2>,
{
	#[expect(clippy::needless_pass_by_value)]
	pub(crate) fn new(keys: Keys<Sum<Prod<NM, U3>, U2>>) -> Self {
		Self(LookupInner::new(
			keys.man, keys.i_man,
			keys.pin, keys.i_pin,
			keys.sou, keys.i_sou,
			keys.ji, keys.i_ji,
		), Default::default())
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
		// SAFETY: The size of `melds` is correct based on the number of keys in `keys`, so as long as `self.0.next()` returned `Some(_)`,
		// we know that `melds` must have been completely filled with melds.
		let melds = unsafe { GenericArray::assume_init(melds) };
		Some((melds, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.0.size_hint()
	}
}

impl LookupInner {
	fn new(
		keys_man: u32, keys_man_len: u8,
		keys_pin: u32, keys_pin_len: u8,
		keys_sou: u32, keys_sou_len: u8,
		keys_ji: u32, keys_ji_len: u8,
	) -> Self {
		fn lookup_numbers(key: u32, len: u8) -> &'static [(Meld<NumberMeld>, Option<NumberMeld>)] {
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

		fn lookup_honors(key: u32, len: u8) -> Option<&'static (u32, Meld<Honor>, Option<Honor>)> {
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

		let man = lookup_numbers(keys_man, keys_man_len);
		let pin = lookup_numbers(keys_pin, keys_pin_len);
		let sou = lookup_numbers(keys_sou, keys_sou_len);
		let ji = lookup_honors(keys_ji, keys_ji_len);

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
		let &(_, ji_melds, ji_pair) = self.ji?;

		let mut i_pin = usize::from(self.i_pin);
		let mut i_sou = usize::from(self.i_sou);

		if i_sou >= self.sou.len() {
			i_sou = 0;
			i_pin += 1;
		}
		let Some(&(sou_melds, sou_pair)) = self.sou.get(i_sou) else {
			self.ji = None;
			return None;
		};

		if i_pin >= self.pin.len() {
			i_pin = 0;
			self.man = self.man.get(1..).unwrap_or(&[]);
		}
		let Some(&(pin_melds, pin_pair)) = self.pin.get(i_pin) else {
			self.ji = None;
			return None;
		};

		let Some(&(man_melds, man_pair)) = self.man.first() else {
			self.ji = None;
			return None;
		};

		let pair = match ((man_pair, NumberSuit::Man), (pin_pair, NumberSuit::Pin), (sou_pair, NumberSuit::Sou), ji_pair) {
			((Some(n), suit), (None, _), (None, _), None) |
			((None, _), (Some(n), suit), (None, _), None) |
			((None, _), (None, _), (Some(n), suit), None) => {
				let number = unsafe { core::mem::transmute::<u8, Number>(n as u8 >> 1) };
				Tile::from(NumberTile::from(NumberTileClassified { suit, number }))
			},

			((None, _), (None, _), (None, _), Some(t)) => unsafe { core::mem::transmute::<u8, Tile>(t as u8) },

			// All elements of each slice have the same shape. Eg if the first element of `man` is `M2(..), Some(_)`,
			// then the other elements of `man` will also be `M2(..), Some(_)`. This means that if we find one combination of elements
			// that produces zero or more than two pairs, then every combination will also do that. So we can just terminate early.
			_ => {
				self.ji = None;
				return None;
			},
		};
		let pair = ScorableHandPair(pair);

		let mut melds = melds.iter_mut();
		// SAFETY: In order to have gotten here, we know that two of the given tiles correspond to a pair and the rest are in melds.
		// If there was not one pair, we would've returned when determining the value of `pair`.
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
					unsafe { current.push_unchecked((ms, ScorableHandFourthMeld::Tanki(md), pair)); }
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
		ScorableHandMeld::Ankou(tile) =>
			//  tile | new_tile |  should match
			// ======+==========+==================
			//   5m  |    5m    | yes, kou is 555m
			//   5m  |    0m    | no,  kou is 555m
			//   0m  |    5m    | yes, kou is 550m
			//   0m  |    0m    | yes, kou is 550m
			(tile == new_tile || tile.remove_red() == new_tile).then_some(ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron }),

		ScorableHandMeld::Anjun(tile) => {
			let (t1, t2, t3) = tile.shun();
			if Tile::from(t1) == new_tile {
				if SEVENS.contains(t1) {
					Some(ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron })
				}
				else {
					Some(ScorableHandFourthMeld::RyanmenLow { tile, tsumo_or_ron })
				}
			}
			else if Tile::from(t2) == new_tile {
				Some(ScorableHandFourthMeld::Kanchan { tile, tsumo_or_ron })
			}
			else if Tile::from(t3) == new_tile {
				if ONES.contains(t1) {
					Some(ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron })
				}
				else {
					Some(ScorableHandFourthMeld::RyanmenHigh { tile, tsumo_or_ron })
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
		match m {
			ScorableHandFourthMeld::Tanki(m) => {
				let [t1, t2, t3] = meld_to_tiles(m);
				(t1, t2, t3, t!(1p), t!(1p), TsumoOrRon::Tsumo)
			},

			ScorableHandFourthMeld::Shanpon { tile, tsumo_or_ron } => (tile, tile, t!(1p), t!(1p), tile, tsumo_or_ron),

			ScorableHandFourthMeld::Kanchan { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				(t1.into(), t3.into(), t!(1p), t!(1p), t2.into(), tsumo_or_ron)
			},

			ScorableHandFourthMeld::Penchan { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				if t1.number() == Number::One {
					(t1.into(), t2.into(), t!(1p), t!(1p), t3.into(), tsumo_or_ron)
				}
				else {
					assert!(t1.number() == Number::Seven);
					(t2.into(), t3.into(), t!(1p), t!(1p), t1.into(), tsumo_or_ron)
				}
			},

			ScorableHandFourthMeld::RyanmenLow { tile, tsumo_or_ron } => {
				let (t1, t2, t3) = tile.shun();
				(t2.into(), t3.into(), t!(1p), t!(1p), t1.into(), tsumo_or_ron)
			},

			ScorableHandFourthMeld::RyanmenHigh { tile, tsumo_or_ron } => {
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
			let actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(Keys::default().push_all(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
			assert_eq!(actual, [expected], "{ma:?} did not meld into {expected:?}, only into {actual:?}");
		}

		// 124 -> X
		assert!(Lookup::<U1>::new(Keys::default().push_all([t!(1s), t!(2s), t!(4s), t!(1p), t!(1p)].into())).next().is_none());
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

			for mb in melds().into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last()) {
				let (t4, t5, t6, t7, new_tile, tsumo_or_ron) = fourth_meld_to_tiles(mb);
				let mut used = used.clone();
				if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
					continue;
				}

				let mut expected = ArrayVec::<_, U2>::new();
				expected.push(([ma].into(), mb, ScorableHandPair(t!(1p)))).unwrap();
				if let ScorableHandFourthMeld::Tanki(mb) = mb {
					expected.push(([mb].into(), ScorableHandFourthMeld::Tanki(ma), ScorableHandPair(t!(1p)))).unwrap();
				}

				let ts = [t1, t2, t3, t4, t5, t6, t7].into();
				let actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(Keys::default().push_all(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
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

				for mc in melds().into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last()) {
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
					if let ScorableHandFourthMeld::Tanki(mc) = mc {
						let ms = { let mut ms = [ma, mc]; ms.sort_unstable(); ms.into() };
						expected.push((ms, ScorableHandFourthMeld::Tanki(mb), ScorableHandPair(t!(1p)))).unwrap();
						let ms = { let mut ms = [mb, mc]; ms.sort_unstable(); ms.into() };
						expected.push((ms, ScorableHandFourthMeld::Tanki(ma), ScorableHandPair(t!(1p)))).unwrap();
					}

					let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into();
					let mut actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(Keys::default().push_all(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
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

					for md in melds().into_iter().map(ScorableHandFourthMeld::Tanki).chain(melds_last()) {
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
						if let ScorableHandFourthMeld::Tanki(md) = md {
							let ms = { let mut ms = [ma, mb, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ScorableHandFourthMeld::Tanki(mc), ScorableHandPair(t!(1p)))).unwrap();
							let ms = { let mut ms = [ma, mc, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ScorableHandFourthMeld::Tanki(mb), ScorableHandPair(t!(1p)))).unwrap();
							let ms = { let mut ms = [mb, mc, md]; ms.sort_unstable(); ms.into() };
							expected.push((ms, ScorableHandFourthMeld::Tanki(ma), ScorableHandPair(t!(1p)))).unwrap();
						}

						let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into();
						let mut actual: std::vec::Vec<_> = LookupForNewTile::new(Lookup::new(Keys::default().push_all(ts).push(new_tile)), new_tile, tsumo_or_ron).collect();
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
