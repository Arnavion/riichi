use generic_array::{
	ArrayLength,
	GenericArray,
	sequence::{GenericSequence as _, Remove, Shorten},
	typenum::{
		Prod,
		Sum,
		U1, U2, U3, U4, U14,
	},
};

use crate::{
	KouWait,
	NumberTile,
	ScorableHandFourthMeld, ScorableHandMeld, ScorableHandPair, ScorableHandRegularPair, ScorableHandRegularPairTag, ShunLowTileAndHasFiveRed, ShunWait,
	Tile, Tile27Set, Tile34MultiSet, Tile34Set, Tile37CountedMultiSet, Tile37MultiSet, Tile37Set, Tile37SetIntoIter, TsumoOrRon,
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
#[expect(
	clippy::eq_op,
	unused, // Constructed via `transmute`
)]
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

#[derive(Clone, Copy, Debug)]
struct LookupHonors {
	pair: Option<Honor>,
	// Every third bit corresponds to an honor tile offset.
	//
	// Micro-optimization: Extracting and packing the bits into a u8 generates worse assembly.
	ankous: u32,
}

impl LookupHonors {
	fn new(key: u32) -> Option<Self> {
		let b0 = key & 0o1111111;
		let b1 = (key >> 1) & 0o1111111;
		let b2 = (key >> 2) & 0o1111111;

		let eq1 = !b1 & b0;
		let eq4 = b2;
		if eq1 | eq4 != 0 {
			return None;
		}

		let eq2 = b1 & !b0;
		let pair =
			if let Some(offset) = eq2.lowest_one() {
				if !eq2.is_power_of_two() {
					return None;
				}

				#[expect(clippy::cast_possible_truncation)]
				let h = ((offset / 3) as u8) << 1;
				Some(unsafe { core::mem::transmute::<u8, Honor>(h) })
			}
			else {
				None
			};

		let ankous = b1 & b0;

		Some(Self { pair, ankous })
	}

	fn waits(key: u32) -> u32 {
		let b0 = key & 0o1111111;
		let b1 = (key >> 1) & 0o1111111;
		let b2 = (key >> 2) & 0o1111111;
		let eq1 = !b1 & b0;
		let eq2 = b1 & !b0;
		let eq4 = b2;

		// If there is even a single tile with count 4, then the hand is not in tenpai so there are no waits.
		// Otherwise, the wait is either a tile with count 1 (that could become a pair) or a tile with count 2 (that could become a kou).
		let waits =
			if eq4 != 0 {
				return 0;
			}
			else if eq2.count_ones() <= 2 && eq1 == 0 {
				eq2
			}
			else if eq1.is_power_of_two() && eq2 == 0 {
				eq1
			}
			else {
				return 0;
			};

		cfg_select! {
			all(target_arch = "x86_64", target_feature = "bmi2") =>
				unsafe { core::arch::x86_64::_pext_u32(waits, 0o1111111) },

			_ => {{
				const fn step(x: u32, mask: u32, shift: u8) -> u32 {
					(x & !mask) | ((x & mask) >> shift)
				}

				//                        00g_00f_00e_00d_00c_00b_00a
				//                     -> 0hg_000_0fe_000_0dc_000_0ba
				let waits = step(waits, 0b000_001_000_001_000_001_000, 2);
				//                     -> 000_000_gfe_000_000_00d_cba
				let waits = step(waits, 0b011_000_000_000_011_000_000, 4);
				//                     -> 000_000_000_000_00g_fed_cba
				let waits = step(waits, 0b000_001_111_000_000_000_000, 8);
				waits
			}},
		}
	}

	/// # Safety
	///
	/// `melds` must have enough elements to write all of `self`'s melds.
	unsafe fn write_melds_to<'a>(self, mut melds: impl Iterator<Item = &'a mut core::mem::MaybeUninit<ScorableHandMeld>>) {
		let mut ankous = self.ankous;
		while let Some(offset) = ankous.lowest_one() {
			ankous &= !(0b1 << offset);
			#[expect(clippy::cast_possible_truncation)]
			let t = t!(E) as u8 + (((offset / 3) as u8) << 1);
			let t = unsafe { core::mem::transmute::<u8, Tile>(t) };
			let m = ScorableHandMeld::Ankou(t);
			let slot = melds.next();
			let slot = unsafe { slot.unwrap_unchecked() };
			slot.write(m);
		}
	}
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
#[expect(clippy::eq_op)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K1 = t!(1m) as u8 - t!(1m) as u8,
	/// Ankou 222 / Pair 22
	K2 = t!(2m) as u8 - t!(1m) as u8,
	/// Ankou 333 / Pair 33
	K3 = t!(3m) as u8 - t!(1m) as u8,
	/// Ankou 444 / Pair 44
	K4 = t!(4m) as u8 - t!(1m) as u8,
	/// Ankou 555 / Pair 55
	K5 = t!(5m) as u8 - t!(1m) as u8,
	/// Ankou 666 / Pair 66
	K6 = t!(6m) as u8 - t!(1m) as u8,
	/// Ankou 777 / Pair 77
	K7 = t!(7m) as u8 - t!(1m) as u8,
	/// Ankou 888 / Pair 88
	K8 = t!(8m) as u8 - t!(1m) as u8,
	/// Ankou 999 / Pair 99
	K9 = t!(9m) as u8 - t!(1m) as u8,

	/// Shun 123
	S1 = (t!(1m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 234
	S2 = (t!(2m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 345
	S3 = (t!(3m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 456
	S4 = (t!(4m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 567
	S5 = (t!(5m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 678
	S6 = (t!(6m) as u8 - t!(1m) as u8) | (1 << 7),
	/// Shun 789
	S7 = (t!(7m) as u8 - t!(1m) as u8) | (1 << 7),
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

mod numbers;

pub(crate) struct Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	ji: Option<LookupHonors>,
	decomposition_ptr: GenericArray<*const (Option<NumberMeld>, Meld<NumberMeld>), Sum<NM, U1>>,
	decomposition_len: GenericArray<u8, Sum<NM, U1>>,
	decomposition_base: GenericArray<NumberTile, Sum<NM, U1>>,
	decomposition_i: GenericArray<u8, Sum<NM, U1>>,
	reds: [u8; 3],
}

impl<NM> Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength> + core::ops::Mul<U3, Output: core::ops::Add<U2>>,
{
	pub(crate) fn new(ts: &Tile37CountedMultiSet<Sum<Prod<NM, U3>, U2>>) -> Self {
		// Common implementation independent of `NM` to combat monomorphization bloat.
		fn inner(
			ts: &Tile37MultiSet,
			decomposition_ptr: &mut [*const (Option<NumberMeld>, Meld<NumberMeld>)],
			decomposition_len: &mut [u8],
			decomposition_base: &mut [NumberTile],
			reds: &mut [u8; 3],
		) -> Option<LookupHonors> {
			unsafe { core::hint::assert_unchecked(decomposition_ptr.len() == decomposition_len.len()); }
			unsafe { core::hint::assert_unchecked(decomposition_ptr.len() == decomposition_base.len()); }

			*reds = t![0m, 0p, 0s].map(|t| ts.get(t));

			let ts = Tile34MultiSet::from(ts.clone());
			let man = ts.man();
			let pin = ts.pin();
			let sou = ts.sou();
			let ji = ts.ji();

			let mut slots = decomposition_ptr.iter_mut().zip(decomposition_len).zip(decomposition_base).rev();

			// If any lookup failed, then the hand as a whole cannot be decomposed, so we can just terminate early.
			let ji = LookupHonors::new(ji.0)?;
			let mut has_pair = ji.pair.is_some();
			for ((key, len), base) in [(man, tn!(1m)), (pin, tn!(1p)), (sou, tn!(1s))] {
				if len % 3 == 1 {
					return None;
				}
				for (start, decomposition) in numbers::lookup(key) {
					// All elements of each slice have the same shape. Eg if the first element is `(Some(_), m2(..))`,
					// then the other elements will also be `(Some(_), m2(..))`. This means that if we find one combination of elements
					// that produces zero or more than two pairs, then every combination will also do that, so we can just terminate early.
					let (pair, _) = decomposition.first()?;
					if pair.is_some() && core::mem::replace(&mut has_pair, true) {
						return None;
					}

					// More decompositions than slots means this hand as a whole cannot have a valid decomposition.
					let ((slot_ptr, slot_len), slot_base) = slots.next()?;

					*slot_ptr = decomposition.as_ptr();

					#[expect(clippy::cast_possible_truncation)]
					{
						*slot_len = decomposition.len() as u8;
					}

					let base = base as u8 + (start << 1);
					let base = unsafe { core::mem::transmute::<u8, NumberTile>(base) };
					*slot_base = base;
				}
			}

			has_pair.then_some(ji)
		}

		let ts = ts.as_ref();
		let mut result = Self::default();
		result.ji = inner(ts, &mut result.decomposition_ptr, &mut result.decomposition_len, &mut result.decomposition_base, &mut result.reds);
		result
	}
}

impl<NM> Clone for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn clone(&self) -> Self {
		Self {
			ji: self.ji,
			decomposition_ptr: self.decomposition_ptr.clone(),
			decomposition_len: self.decomposition_len.clone(),
			decomposition_base: self.decomposition_base.clone(),
			decomposition_i: self.decomposition_i.clone(),
			reds: self.reds,
		}
	}
}

impl<NM> core::fmt::Debug for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("Lookup")
			.field("ji", &self.ji)
			.field("decomposition_ptr", &self.decomposition_ptr)
			.field("decomposition_len", &self.decomposition_len)
			.field("decomposition_base", &self.decomposition_base)
			.field("decomposition_i", &self.decomposition_i)
			.field("reds", &self.reds)
			.finish()
	}
}

impl<NM> Default for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn default() -> Self {
		Self {
			ji: Default::default(),
			decomposition_ptr: GenericArray::repeat(numbers::EMPTY.as_ptr()),
			#[expect(clippy::cast_possible_truncation)]
			decomposition_len: GenericArray::repeat(numbers::EMPTY.len() as u8),
			decomposition_base: GenericArray::repeat(tn!(1m)),
			decomposition_i: Default::default(),
			reds: Default::default(),
		}
	}
}

impl<NM> Iterator for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength> + ArrayLength,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandPair);

	fn next(&mut self) -> Option<Self::Item> {
		// Common implementation independent of `NM` to combat monomorphization bloat.
		fn inner(
			ji: &mut Option<LookupHonors>,
			decomposition_ptr: &[*const (Option<NumberMeld>, Meld<NumberMeld>)],
			decomposition_i: &mut [u8],
			decomposition_base: &[NumberTile],
			decomposition_len: &[u8],
			melds: &mut [core::mem::MaybeUninit<ScorableHandMeld>],
		) -> Option<ScorableHandPair> {
			let ji_ = (*ji)?;

			// SAFETY: In order to have gotten here, we know that two of the given tiles correspond to a pair and the rest are in melds.
			// If there was not one pair, we would've returned a neutered iterator in `new()`.
			// If one or more of the suits did not form a valid decomposition, the corresponding slice would've been empty and we would've returned a neutered iterator in `new()`.
			//
			// So we will fill the `melds` slice exactly.
			let mut pair = ji_.pair.map(|h| {
				let t = t!(E) as u8 + h as u8;
				unsafe { core::mem::transmute::<u8, Tile>(t) }
			});

			let mut melds = melds.iter_mut();

			for ((&ptr, &i), &base) in decomposition_ptr.iter().zip(&*decomposition_i).zip(decomposition_base).rev() {
				let (decomposition_pair, decomposition_melds) = unsafe { &*(ptr.add(usize::from(i))) };

				unsafe { decomposition_melds.write_to(&mut melds, base); }
				pair = pair.or_else(|| decomposition_pair.map(|n| {
					let t = base as u8 + n as u8;
					unsafe { core::mem::transmute::<u8, Tile>(t) }
				}));
			}
			unsafe { ji_.write_melds_to(melds); }

			let pair = unsafe { pair.unwrap_unchecked() };
			let pair = ScorableHandPair(pair);

			cfg_select! {
				all(target_arch = "riscv64", target_feature = "v") => unsafe {
					let to_increment: isize;

					core::arch::asm!(
						"vsetvli zero, {nm_plus_one}, e8, m1, ta, ma",
						// let decomposition_i /* : v8:v8 */ = core::simd::Simd::from_array(self.decomposition_i);
						"vle8.v v8, ({decomposition_i})",
						// let decomposition_len /* : v9:v9 */ = core::simd::Simd::from_array(self.decomposition_len);
						"vle8.v v9, ({decomposition_len})",
						// let decomposition_i_plus_one /* : v10:v10 */ = decomposition_i + core::simd::Simd::splat(1);
						"vadd.vi v10, v8, 1",
						// let to_increment /* : v1:v1 */ = core::simd::cmp::SimdPartialOrd::simd_lt(decomposition_i_plus_one, decomposition_len);
						"vmsltu.vv v1, v10, v9",
						// if let Some(to_increment) = to_increment.first_set() {
						"vfirst.m {to_increment}, v1",
						"bltz {to_increment}, 1f",
						//     let to_increment = 0b1_u64 << to_increment;
						//     let to_reset /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment - 1);
						"vmsbf.m v0, v1",
						//     let decomposition_i /* : v8:v8 */ = core::simd::Select::select(to_reset, core::simd::Simd::splat(0), decomposition_i);
						"vmerge.vim v8, v8, 0, v0",
						//     let to_increment /* : v0:v0 */ = core::simd::Mask::<i8, { NM + 1 }>::from_bitmask(to_increment);
						"vmsof.m v0, v1",
						//     let decomposition_i /* : v8:v8 */ = core::simd::Select::select(to_increment, decomposition_i_plus_one, decomposition_i);
						"vmerge.vvm v8, v8, v10, v0",
						//     decomposition_i.copy_to_slice(&mut self.decomposition_i);
						"vse8.v v8, ({decomposition_i})",
						// }
						"1:",

						nm_plus_one = in(reg) decomposition_i.len(),
						decomposition_i = in(reg) decomposition_i.as_mut_ptr(),
						decomposition_len = in(reg) decomposition_len.as_ptr(),
						to_increment = out(reg) to_increment,
						out("v0") _,
						out("v1") _,
						out("v8") _,
						out("v9") _,
						out("v10") _,
						options(nostack),
					);

					if to_increment < 0 {
						*ji = None;
					}
				},

				_ => {
					for (i, &len) in decomposition_i.iter_mut().zip(decomposition_len) {
						if *i + 1 < len {
							*i += 1;
							return Some(pair);
						}
						*i = 0;
					}

					*ji = None;
				},
			}

			Some(pair)
		}

		let mut melds = GenericArray::uninit();
		let pair = inner(&mut self.ji, &self.decomposition_ptr, &mut self.decomposition_i, &self.decomposition_base, &self.decomposition_len, &mut melds)?;
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
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{
	fn len(&self) -> usize {
		// This function is small enough that monomorphizing it for the unrolled fold is better.
		if self.ji.is_some() {
			self.decomposition_len.iter()
				.zip(&self.decomposition_i)
				.rfold(1, |acc, (&len, &i)| acc * usize::from(len) - usize::from(i))
		}
		else {
			0
		}
	}
}

impl<NM> core::iter::FusedIterator for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{}

unsafe impl<NM> Send for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{}

unsafe impl<NM> Sync for Lookup<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{}

pub(crate) struct LookupForNewTile<NM>
where
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
{
	current: FourthMelds<NM>,
	lookup: Lookup<Sum<NM, U1>>,
	new_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
}

impl<NM> LookupForNewTile<NM>
where
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
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
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
	FourthMelds<NM>: Iterator<Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair)>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let Some((ms, md, pair)) = self.current.next() else {
				let (ms, pair) = self.lookup.next()?;
				self.current = FourthMelds::new(ms, pair, self.new_tile, self.tsumo_or_ron, self.lookup.reds);
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
	NM: core::ops::Add<U1, Output: core::ops::Add<U1, Output: ArrayLength> + ArrayLength>,
	Self: Iterator,
{}

pub fn lookup_tenpai<NT>(ts: Tile37CountedMultiSet<NT>) -> Tile37Set
where
	NT: core::ops::Rem<U3, Output = U1>,
{
	fn inner(ts: &Tile37MultiSet) -> Tile37Set {
		let ts34 = Tile34MultiSet::from(ts.clone());
		let man = ts34.man();
		let pin = ts34.pin();
		let sou = ts34.sou();
		let ji = ts34.ji();

		// Either one suit has 3n + 1 tiles, or two suits have 3n + 2 tiles for this hand to have a chance of being in tenpai.
		// Any other case is guaranteed to not be in tenpai.
		//
		// - If one suit has 3n + 1 tiles, then the other three suits must have 3n tiles for the sum to be 3n + 1.
		//   In this case, the new tile must be in that suit and the pair will be from that suit.
		// - If two suits have 3n + 2 tiles then the other two suits must have 3n tiles for the sum to be 3n + 1.
		//   In this case, the new tile can be in either of the two suits and will convert that suit to 3n tiles, while the other suit will produce the pair.
		//
		// | 3n + 0 | 3n + 1 | 3n + 2 | May be in tenpai | Number of suits with | Suits looking
		// |        |        |        |                  |  more than 3n tiles  | for new tiles
		// +========+========+========+==================+======================+===============
		// |    3   |    1   |    0   | Valid            | 1                    | 3n + 1
		// |    2   |    0   |    2   | Valid            | 2                    | 3n + 2
		// |    1   |    2   |    1   | Invalid          | 3                    |
		// |    0   |    4   |    0   | Invalid          | 4                    |
		// |    0   |    1   |    3   | Invalid          | 4                    |
		// +--------+--------+--------+------------------+----------------------+---------------
		// |    4   |    0   |    0   | Impossible       |                      |
		// |    3   |    0   |    1   | Impossible       |                      |
		// |    2   |    2   |    0   | Impossible       |                      |
		// |    2   |    1   |    1   | Impossible       |                      |
		// |    1   |    3   |    0   | Impossible       |                      |
		// |    1   |    1   |    2   | Impossible       |                      |
		// |    1   |    0   |    3   | Impossible       |                      |
		// |    0   |    3   |    1   | Impossible       |                      |
		// |    0   |    2   |    2   | Impossible       |                      |
		// |    0   |    0   |    4   | Impossible       |                      |
		//
		// Thus the "Invalid" cases can be simplified into "more than two suits have more than 3n tiles".
		let has_excess =
			[man.1, pin.1, sou.1, ji.1].into_iter()
			.enumerate()
			.fold(0, |acc, (i, len)| acc | if len % 3 > 0 { 0b1_u8 << i } else { 0 });
		let num_suits_with_excess = has_excess.count_ones();
		if num_suits_with_excess > 2 {
			return Default::default();
		}

		// If a suit has 3n tiles, it must already be valid, otherwise the hand as a whole is invalid.
		// This is an early check before building up the `SuitState`s for suits with excess.
		if has_excess & 0b0001 == 0b0000 && !numbers::is_valid(man) {
			return Default::default();
		}
		if has_excess & 0b0010 == 0b0000 && !numbers::is_valid(pin) {
			return Default::default();
		}
		if has_excess & 0b0100 == 0b0000 && !numbers::is_valid(sou) {
			return Default::default();
		}
		let ji_state =
			if has_excess & 0b1000 == 0b0000 {
				let ji_state = LookupHonors::new(ji.0);
				if ji_state.is_none() {
					return Default::default();
				}
				ji_state
			}
			else {
				LookupHonors::new(ji.0)
			};
		// Micro-optimization: `SuitState::default()` is created for suits that don't have excess, and returns an invalid `SuitState`
		// that cannot become valid with any tile. But it's not actually used anyway, since the code below only calls `.waits()` if the suit had excess.
		// The `::default()` is just there to make the `if-else` arms have the same type.
		// The alternative would be to return `None` / `Some(SuitState::new(...))` but that generates worse assembly.
		let man_state =
			if has_excess & 0b0001 == 0b0000 {
				Default::default()
			}
			else {
				numbers::SuitState::new(man)
			};
		let pin_state =
			if has_excess & 0b0010 == 0b0000 {
				Default::default()
			}
			else {
				numbers::SuitState::new(pin)
			};
		let sou_state =
			if has_excess & 0b0100 == 0b0000 {
				Default::default()
			}
			else {
				numbers::SuitState::new(sou)
			};

		// All suits valid => wait is in any suit with excess
		// One invalid suit => wait is in that suit
		// More than one invalid suit => not in tenpai
		let invalid =
			(
				u8::from(!man_state.is_valid()) |
				(u8::from(!pin_state.is_valid()) << 1) |
				(u8::from(!sou_state.is_valid()) << 2) |
				(u8::from(has_excess & 0b1000 != 0b0000 && ji_state.is_none()) << 3)
			) & has_excess;
		let may_wait_in =
			if invalid == 0 {
				has_excess
			}
			else if invalid.is_power_of_two() {
				invalid
			}
			else {
				return Default::default();
			};

		let mut valid = 0_u64;
		if may_wait_in & 0b0001 != 0b0000 {
			valid |= u64::from(man_state.waits());
		}
		if may_wait_in & 0b0010 != 0b0000 {
			valid |= u64::from(pin_state.waits()) << 9;
		}
		if may_wait_in & 0b0100 != 0b0000 {
			valid |= u64::from(sou_state.waits()) << 18;
		}
		if may_wait_in & 0b1000 != 0b0000 {
			valid |= u64::from(LookupHonors::waits(ji.0)) << 27;
		}

		let result = Tile34Set { present: valid };

		let mut result = result.stretch_red_fives();

		// `LookupHonors::waits` and `SuitState::waits` exclude tiles that already have four copies in `ts`,
		// but this does not account for fives, for which the presence of three regular fives means a fourth five must be excluded,
		// and the presence of a red five means a second red five must be excluded. So we handle fives manually.
		let fives_invalid =
			ts.to_suits()[..3].iter()
			.enumerate()
			.fold(0_u64, |acc, (i, &counts)| {
				#[expect(clippy::cast_possible_truncation)]
				let i = i as u8;
				// counts[12+:2] == 0b11 => regular fives can't be inserted => result[10 * suit + 4] = 0b1
				// counts[15] == 0b1 => red fives can't be inserted => result[10 * suit + 5] = 0b1
				// result[10 * suit + 4+:2] = (counts[12] & counts[13]) | (counts[15] << 1);
				let counts = counts >> (Tile::offset(t!(5m)) * 3);
				let result = (counts & (counts >> 1) & 0b1) | ((counts >> 2) & 0b10);
				let result = result << (i * 10 + Tile::offset(t!(5m)));
				acc | u64::from(result)
			});
		result.present &= !fives_invalid;

		result
	}

	let ts = Tile37MultiSet::from(ts);
	inner(&ts)
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LookupForTenhou {
	current_a: FourthMelds<U3>,
	current_b: Option<(GenericArray<ScorableHandMeld, U4>, ScorableHandPair, Tile37SetIntoIter)>,
	lookup: Lookup<U4>,
	tiles: Tile37Set,
}

impl LookupForTenhou {
	pub(crate) fn new(ts: &Tile37CountedMultiSet<U14>) -> Self {
		let lookup = Lookup::new(ts);
		let tiles = Tile37Set::from(ts.as_ref());
		Self {
			current_a: Default::default(),
			current_b: None,
			lookup,
			tiles,
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
				self.current_a = FourthMelds::new(*ms, *pair, new_tile, TsumoOrRon::Tsumo, self.lookup.reds);
				continue;
			};
			break Some((ms.into(), md, pair));
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let current_a_len = self.current_a.len();
		(current_a_len, None)
	}
}

impl core::iter::FusedIterator for LookupForTenhou {}

struct FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	ms: GenericArray<ScorableHandMeld, Sum<NM, U1>>,
	pair: ScorableHandPair,
	// Bit `0` is set if the pair contains the winning tile. Bit `i + 1` is set if `ms[i]` contains the winning tile.
	has_winning_tile: u8,
	winning_tile: Tile,
	tsumo_or_ron: TsumoOrRon,
	reds: [u8; 3],
}

impl<NM> FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn new(
		ms: GenericArray<ScorableHandMeld, Sum<NM, U1>>,
		pair: ScorableHandPair,
		winning_tile: Tile,
		tsumo_or_ron: TsumoOrRon,
		reds: [u8; 3],
	) -> Self {
		let new_tile = winning_tile.remove_red();

		let has_winning_tile =
			ms.iter()
			.enumerate()
			.fold(u8::from(pair.0 as u8 == new_tile as u8), |acc, (i, &m)| {
				let [d, t] = m.parts();
				// Micro-optimization:
				//
				// This is equivalent to:
				//
				//     let present = match m {
				//         ScorableHandMeld::Ankou(t) => t == new_tile,
				//         ScorableHandMeld::Anjun(t1) => { let (t2, t3) = t1.shun_rest(); [Tile::from(t1), Tile::from(t2), Tile::from(t3)].contains(&new_tile),
				//         _ => unsafe { core::hint::unreachable_unchecked(); },
				//     };
				//
				// ... but that generates branches and does extra work in `shun_rest` for producing a red five.
				//
				// `ms` comes from lookup which is guaranteed to only have ankous and anjuns, and guaranteed to not have `FiveRed`s in either of those.
				// So we can do better with arithmetic on the discriminant and tile. Given `diff = new_tile.wrapping_sub(t)`:
				// - Ankou (0b010): expect t == new_tile => diff == 0
				// - Anjun (0b100): expect [t, t + 2, t + 4].contains(&new_tile) => diff <= 4
				let diff = (new_tile as u8).wrapping_sub(t);
				let max_diff = d & 0b100;
				let present = diff <= max_diff;
				acc | (u8::from(present) << (i + 1))
			});

		Self {
			ms,
			pair,
			has_winning_tile,
			winning_tile,
			tsumo_or_ron,
			reds,
		}
	}
}

impl<NM> Clone for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn clone(&self) -> Self {
		Self {
			ms: self.ms.clone(),
			pair: self.pair,
			has_winning_tile: self.has_winning_tile,
			winning_tile: self.winning_tile,
			tsumo_or_ron: self.tsumo_or_ron,
			reds: self.reds,
		}
	}
}

impl<NM> core::fmt::Debug for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("FourthMelds")
			.field("ms", &self.ms)
			.field("pair", &self.pair)
			.field("has_winning_tile", &self.has_winning_tile)
			.field("winning_tile", &self.winning_tile)
			.field("tsumo_or_ron", &self.tsumo_or_ron)
			.field("reds", &self.reds)
			.finish()
	}
}

impl<NM> Default for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
{
	fn default() -> Self {
		Self {
			ms: GenericArray::repeat(ScorableHandMeld::Ankou(t!(1m))),
			pair: ScorableHandPair(t!(1m)),
			has_winning_tile: 0,
			winning_tile: t!(1m),
			tsumo_or_ron: TsumoOrRon::Tsumo,
			reds: [0; _],
		}
	}
}

impl<NM> Iterator for FourthMelds<NM>
where
	NM:
		ArrayLength +
		core::ops::Add<U1, Output: ArrayLength>,
	GenericArray<ScorableHandMeld, Sum<NM, U1>>:
		Copy +
		Remove<ScorableHandMeld, Sum<NM, U1>, Output = GenericArray<ScorableHandMeld, NM>> +
		Shorten<ScorableHandMeld, Shorter = GenericArray<ScorableHandMeld, NM>>,
{
	type Item = (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair);

	fn next(&mut self) -> Option<Self::Item> {
		const ONES: Tile27Set = t27set![1m, 1p, 1s];
		const SEVENS: Tile27Set = t27set![7m, 7p, 7s];

		let i = self.has_winning_tile.lowest_one()?;
		self.has_winning_tile &= !(0b1 << i);

		let new_tile = self.winning_tile.remove_red();

		let (mut ms, mut md, mut pair) =
			if let Some(i) = i.checked_sub(1) {
				let i = i as usize;
				unsafe { core::hint::assert_unchecked(i < self.ms.len()); }
				let md = match self.ms[i] {
					ScorableHandMeld::Ankou(t) => ScorableHandFourthMeld::kou(t, self.tsumo_or_ron, KouWait::Shanpon),
					ScorableHandMeld::Anjun(t) => {
						let (t1, t2, t3) = t.shun();
						let wait =
							if Tile::from(t1) == new_tile {
								if SEVENS.contains(t1.into()) { ShunWait::Penchan } else { ShunWait::RyanmenLow }
							}
							else if Tile::from(t2) == new_tile {
								ShunWait::Kanchan
							}
							else if Tile::from(t3) == new_tile {
								if ONES.contains(t1.into()) { ShunWait::Penchan } else { ShunWait::RyanmenHigh }
							}
							else {
								unsafe { core::hint::unreachable_unchecked(); }
							};
						ScorableHandFourthMeld::shun(t, self.tsumo_or_ron, wait)
					},

					_ => unsafe { core::hint::unreachable_unchecked(); },
				};
				let (_, ms) = unsafe { Remove::remove_unchecked(self.ms, i) };
				let pair = ScorableHandRegularPair { tag: ScorableHandRegularPairTag::Antoi, inner: self.pair };
				(ms, md, pair)
			}
			else {
				let (ms, md) = Shorten::pop_back(self.ms);
				let pair_tag = match self.tsumo_or_ron {
					TsumoOrRon::Tsumo => ScorableHandRegularPairTag::Antoi,
					TsumoOrRon::Ron => ScorableHandRegularPairTag::Mintoi,
				};
				let pair = ScorableHandRegularPair { tag: pair_tag, inner: self.pair };
				(ms, ScorableHandFourthMeld::tanki(md), pair)
			};

		if self.reds != [0; _] {
			for (red, num_red) in t![0m, 0p, 0s].into_iter().zip(self.reds) {
				if num_red == 0 {
					continue;
				}

				let restored =
					if red == self.winning_tile {
						if md.is_tanki() {
							restore_red_to_kou(&mut pair.inner.0, red)
						}
						else {
							restore_red_to_fourth_meld(&mut md, red, None)
						}
					}
					else {
						restore_red_to_kou(&mut pair.inner.0, red) ||
						restore_red_to_fourth_meld(&mut md, red, Some(self.winning_tile)) ||
						ms.iter_mut().rev().any(|m| restore_red_to_meld(m, red))
					};
				debug_assert!(restored);
			}
		}

		Some((ms, md, pair))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<NM> ExactSizeIterator for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{
	fn len(&self) -> usize {
		self.has_winning_tile.count_ones() as usize
	}
}

impl<NM> core::iter::FusedIterator for FourthMelds<NM>
where
	NM: core::ops::Add<U1, Output: ArrayLength>,
	Self: Iterator,
{}

fn restore_red_to_meld(m: &mut ScorableHandMeld, red: Tile) -> bool {
	match m {
		ScorableHandMeld::Ankou(t) => restore_red_to_kou(t, red),
		ScorableHandMeld::Anjun(t) => restore_red_to_shun(t, red),
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn restore_red_to_fourth_meld(m: &mut ScorableHandFourthMeld, red: Tile, unless: Option<Tile>) -> bool {
	match m {
		ScorableHandFourthMeld::Ankou(t, _) |
		ScorableHandFourthMeld::Minkou(t, _) => restore_red_to_kou(t, red),
		ScorableHandFourthMeld::Anjun(t, _) |
		ScorableHandFourthMeld::Minjun(t, _) =>
			if Some(red.remove_red()) == unless {
				false
			}
			else {
				restore_red_to_shun(t, red)
			},
		_ => unsafe { core::hint::unreachable_unchecked(); },
	}
}

fn restore_red_to_kou(representative: &mut Tile, red: Tile) -> bool {
	if *representative == red.remove_red() {
		*representative = red;
		true
	}
	else {
		false
	}
}

fn restore_red_to_shun(representative: &mut ShunLowTileAndHasFiveRed, red: Tile) -> bool {
	if ((*representative as u8)..=(*representative as u8 + 5)).contains(&(red as u8)) {
		let t = (*representative as u8) | 0b1;
		*representative = unsafe { core::mem::transmute::<u8, ShunLowTileAndHasFiveRed>(t) };
		true
	}
	else {
		false
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

	use generic_array::{
		sequence::{Lengthen, Shorten},
	};

	use crate::{ArrayVec, CmpIgnoreRed as _, Number};
	use super::*;

	fn meld_to_tiles(m: ScorableHandMeld) -> [Tile; 3] {
		let mut result = ArrayVec::<_, U3>::new();
		m.for_each_tile(|t| result.push(t).unwrap());
		GenericArray::try_from(result).unwrap().into()
	}

	fn fourth_meld_and_pair_to_tiles(m: ScorableHandFourthMeld, ScorableHandPair(p_t): ScorableHandPair) -> ArrayVec<([Tile; 4], Tile), U2> {
		let mut result = ArrayVec::new();

		match m {
			m @ (
				ScorableHandFourthMeld::Ankou(_, KouWait::Tanki) |
				ScorableHandFourthMeld::Anjun(_, ShunWait::Tanki)
			) => {
				let [t1, t2, t3] = meld_to_tiles(m.into());
				result.push(([t1, t2, t3, p_t], p_t)).unwrap();
			},

			ScorableHandFourthMeld::Ankou(tile, KouWait::Shanpon) => {
				let t = tile.remove_red();
				result.push(([t, t, p_t, p_t], tile)).unwrap();
				if t != tile {
					result.push(([t, tile, p_t, p_t], t)).unwrap();
				}
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Kanchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t3, p_t, p_t], t2)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::Penchan) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = NumberTile::from(t1);
				if t1.number() == Number::One {
					result.push(([t1.into(), t2.into(), p_t, p_t], t3.into())).unwrap();
				}
				else if t1.number() == Number::Seven {
					result.push(([t2.into(), t3.into(), p_t, p_t], t1.into())).unwrap();
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
				result.push(([t2, t3, p_t, p_t], t1)).unwrap();
			},

			ScorableHandFourthMeld::Anjun(tile, ShunWait::RyanmenHigh) => {
				let (t1, t2, t3) = tile.shun();
				let t1 = t1.into();
				let t2 = t2.into();
				let t3 = t3.into();
				result.push(([t1, t2, p_t, p_t], t3)).unwrap();
			},

			_ => unreachable!(),
		}

		result
	}

	fn pairs() -> [ScorableHandPair; 3] {
		t![1p, 1s, 9s].map(ScorableHandPair)
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

	fn eq_ignore_red<NM>(
		(mut ms1, mut md1, p1): (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair),
		(mut ms2, mut md2, p2): (GenericArray<ScorableHandMeld, NM>, ScorableHandFourthMeld, ScorableHandRegularPair),
	) -> bool
	where
		NM: ArrayLength,
		GenericArray<ScorableHandMeld, NM>:
			Copy +
			IntoIterator<Item = ScorableHandMeld> +
			Lengthen<ScorableHandMeld, Longer: core::ops::DerefMut<Target = [ScorableHandMeld]>>,
	{
		fn count_reds_meld(count: &mut usize, m: ScorableHandMeld) {
			match m {
				ScorableHandMeld::Ankan(t!(0s)) |
				ScorableHandMeld::Minkan(t!(0s)) |
				ScorableHandMeld::Ankou(t!(0s)) |
				ScorableHandMeld::Minkou(t!(0s)) => *count += 1,
				ScorableHandMeld::Anjun(t) |
				ScorableHandMeld::Minjun(t) => match t {
					ShunLowTileAndHasFiveRed::Sou3Red |
					ShunLowTileAndHasFiveRed::Sou4Red |
					ShunLowTileAndHasFiveRed::Sou5Red => *count += 1,
					_ => (),
				},
				_ => (),
			}
		}

		fn count_reds_pair(count: &mut usize, p: ScorableHandRegularPair) {
			if p.inner.0 == t!(0s) {
				*count += 1;
			}
		}

		fn remove_red(m: &mut ScorableHandMeld) {
			match m {
				ScorableHandMeld::Ankan(t) |
				ScorableHandMeld::Minkan(t) |
				ScorableHandMeld::Ankou(t) |
				ScorableHandMeld::Minkou(t) => *t = t.remove_red(),
				ScorableHandMeld::Anjun(t) |
				ScorableHandMeld::Minjun(t) => *t = t.remove_red().into(),
			}
		}

		fn remove_red_fourth(m: &mut ScorableHandFourthMeld) {
			match m {
				ScorableHandFourthMeld::Ankan(t, _) |
				ScorableHandFourthMeld::Minkan(t, _) |
				ScorableHandFourthMeld::Ankou(t, _) |
				ScorableHandFourthMeld::Minkou(t, _) => *t = t.remove_red(),
				ScorableHandFourthMeld::Anjun(t, _) |
				ScorableHandFourthMeld::Minjun(t, _) => *t = t.remove_red().into(),
			}
		}

		let mut num_red1 = 0;
		for m in ms1 {
			count_reds_meld(&mut num_red1, m);
		}
		count_reds_meld(&mut num_red1, md1.into());
		count_reds_pair(&mut num_red1, p1);

		let mut num_red2 = 0;
		for m in ms2 {
			count_reds_meld(&mut num_red2, m);
		}
		count_reds_meld(&mut num_red2, md2.into());
		count_reds_pair(&mut num_red2, p2);

		for m in &mut ms1 {
			remove_red(m);
		}
		if let Some(mut md1_) = md1.to_tanki() {
			remove_red(&mut md1_);
			append_and_sort(&mut ms1, &mut md1_);
			md1 = ScorableHandFourthMeld::tanki(md1_);
		}
		else {
			ms1.sort_unstable();
			remove_red_fourth(&mut md1);
		}

		for m in &mut ms2 {
			remove_red(m);
		}
		if let Some(mut md2_) = md2.to_tanki() {
			remove_red(&mut md2_);
			append_and_sort(&mut ms2, &mut md2_);
			md2 = ScorableHandFourthMeld::tanki(md2_);
		}
		else {
			ms2.sort_unstable();
			remove_red_fourth(&mut md2);
		}

		ms1 == ms2 && md1 == md2 && p1.tag == p2.tag && p1.inner.0.eq_ignore_red(&p2.inner.0) && num_red1 == num_red2
	}

	fn append_and_sort<T, N>(arr: &mut GenericArray<T, N>, element: &mut T)
	where
		T: Copy + Ord,
		N: ArrayLength,
		GenericArray<T, N>:
			Copy +
			Lengthen<T, Longer:
				core::ops::DerefMut<Target = [T]> +
				Shorten<T, Shorter = GenericArray<T, N>>,
			>,
	{
		let mut arr_ = arr.append(*element);
		arr_.sort_unstable();
		let (arr_, last) = arr_.pop_back();
		*arr = arr_;
		*element = last;
	}

	#[test]
	fn to_meld() {
		for p in pairs() {
			for ma in melds_last() {
				for (ts @ [t1, t2, t3, t4], new_tile) in fourth_meld_and_pair_to_tiles(ma, p) {
					let mut used = Tile37MultiSet::default();
					if used.try_extend([t1, t2, t3, t4, new_tile]).is_err() {
						continue;
					}

					let expected = ([].into(), ma, ScorableHandRegularPair::antoi(p.0));
					let actual: std::vec::Vec<_> =
						LookupForNewTile::new(
							Lookup::new(&Tile37CountedMultiSet::new((&ts).into()).unwrap().insert(new_tile).unwrap()),
							new_tile,
							TsumoOrRon::Tsumo,
						).collect();

					assert!(
						actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
						"({ma}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
					);
				}
			}
		}

		// 124 -> X
		assert!(Lookup::<U1>::new(&Tile37CountedMultiSet::new(&t![1s, 2s, 4s, 1p, 1p].into()).unwrap()).next().is_none());
	}

	#[test]
	fn to_melds_2() {
		for p in pairs() {
			for ma in melds() {
				let ts @ [t1, t2, t3] = meld_to_tiles(ma);
				let mut used = Tile37MultiSet::default();
				used.try_extend(ts).unwrap();

				for mb in melds().into_iter().map(ScorableHandFourthMeld::tanki).chain(melds_last()) {
					for ([t4, t5, t6, t7], new_tile) in fourth_meld_and_pair_to_tiles(mb, p) {
						let mut used = used.clone();
						if used.try_extend([t4, t5, t6, t7, new_tile]).is_err() {
							continue;
						}

						let expected =
							if let Some(mb) = mb.to_tanki() {
								let mut ms = [ma, mb];
								ms.sort_unstable();
								let [m3, m4] = ms;
								([m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
							}
							else {
								([ma].into(), mb, ScorableHandRegularPair::antoi(p.0))
							};

						let ts = [t1, t2, t3, t4, t5, t6, t7].into();
						let actual: std::vec::Vec<_> =
							LookupForNewTile::new(
								Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
								new_tile,
								TsumoOrRon::Tsumo,
							).collect();

						assert!(
							actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
							"({ma}, {mb}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
						);
					}
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_3() {
		for p in pairs() {
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
						for ([t7, t8, t9, t10], new_tile) in fourth_meld_and_pair_to_tiles(mc, p) {
							let mut used = used.clone();
							if used.try_extend([t7, t8, t9, t10, new_tile]).is_err() {
								continue;
							}

							let expected =
								if let Some(mc) = mc.to_tanki() {
									let mut ms = [ma, mb, mc];
									ms.sort_unstable();
									let [m2, m3, m4] = ms;
									([m2, m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
								}
								else {
									([ma, mb].into(), mc, ScorableHandRegularPair::antoi(p.0))
								};

							let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10].into();
							let actual: std::vec::Vec<_> =
								LookupForNewTile::new(
									Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
									new_tile,
									TsumoOrRon::Tsumo,
								).collect();

							assert!(
								actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
								"({ma}, {mb}, {mc}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
							);
						}
					}
				}
			}
		}
	}

	#[cfg(not(miri))] // Takes too long
	#[test]
	fn to_melds_4() {
		for p in pairs() {
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
							for ([t10, t11, t12, t13], new_tile) in fourth_meld_and_pair_to_tiles(md, p) {
								let mut used = used.clone();
								if used.try_extend([t10, t11, t12, t13, new_tile]).is_err() {
									continue;
								}

								let expected =
									if let Some(md) = md.to_tanki() {
										let mut ms = [ma, mb, mc, md];
										ms.sort_unstable();
										let [m1, m2, m3, m4] = ms;
										([m1, m2, m3].into(), ScorableHandFourthMeld::tanki(m4), ScorableHandRegularPair::antoi(p.0))
									}
									else {
										([ma, mb, mc].into(), md, ScorableHandRegularPair::antoi(p.0))
									};

								let ts = [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13].into();
								let actual: std::vec::Vec<_> =
									LookupForNewTile::new(
										Lookup::new(&Tile37CountedMultiSet::new(&ts).unwrap().insert(new_tile).unwrap()),
										new_tile,
										TsumoOrRon::Tsumo,
									).collect();

								assert!(
									actual.iter().any(|&actual| eq_ignore_red(actual, expected)),
									"({ma}, {mb}, {mc}, {md}, {p}) on {new_tile} did not meld into any of {expected:?}, only into {actual:?}",
								);
							}
						}
					}
				}
			}
		}
	}
}
