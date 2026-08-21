use super::{Element, Maps, SmallInt};

// A particular decomposition consists of zero or one pair and zero or more melds.
// To save lookup space, the lookup key maps to these decompositions in three steps.
//
// The decompositions are stored consecutively in `STORAGE` such that any key maps to consecutive entries in `STORAGE`.
// Thus a particular key maps to the index of the first entry and the length (number of entries).
//
// The index of the first entry and the length are compressed into a `u16` with the following scheme:
//
// 0b0_##_#_####_####_#### : Index relative to STORAGE[0], len = 1.
// 0b1_00_#_####_####_#### : Index relative to STORAGE[STORAGE_MULTIPLE_VALUES_START], len = 2
// 0b1_01_#_####_####_#### : Index relative to STORAGE[STORAGE_MULTIPLE_VALUES_START], len = 3
// 0b1_10_#_####_####_#### : Index relative to STORAGE[STORAGE_MULTIPLE_VALUES_START], len = 4
// 0b1_11_#_####_####_#### : len = 0
//
// (`STORAGE_MULTIPLE_VALUES_START` is a constant that is the index of the first entry in `STORAGE` corresponding to keys with multiple decompositions.
// All entries before it have only one decomposition. This Huffman-esque encoding is because len = 1 decompositions are the most common, specifically there are 0x4ECF of them.)
//
// This `u16` encoded value is then stored in a two-layer directory. The outer layer `LAYER1` is keyed by the upper 27 bits of the lookup key
// and contains the index of the inner layer in `LAYER2`. The inner layer is keyed by the lower 5 bits of the lookup key, ie the inner layer has a fixed size of 32 encoded values.
//
// Only decompositions containing contiguous tiles are stored. For example, decompositions for 111, 333 and 111222333 are stored,
// but not for 111333, since the decompositions of 111333 can be obtained from the cross product of the decompositions of 111 and 333.
//
// Note that the lookup key is a formed by changing the tile counts of the original `Tile34MultiSet` from base 8 to base 5.
// Eg `t34multiset![1m, 2m, 2m, 3m, 3m, 3m]` has manzu tile count `0b011_010_001 = 0b011 * 8^2 + 0b010 * 8^1 + 0b001 * 8^0`.
// For looking up the decomposition here, the key would be converted to `0b011 * 5^2 + 0b010 * 5^1 + 0b001 * 5^0` first.

pub(crate) fn run(path: &std::path::Path) -> std::io::Result<()> {
	use std::io::Write;

	const BLOCK_LEN: usize = 32;
	// Canonical value for len = 0
	const INVALID: u16 = 0xFFFF;

	let maps = Maps::<Number>::new(&ALL_MELDS, &ALL_PAIRS);

	let mut storage = vec![];
	storage.extend(maps.twos.into_iter().map(|(key, p)| (key, vec![(Some(p), vec![])])));
	storage.extend(maps.threes.into_iter().map(|(key, m)| (key, vec![(None, vec![m])])));
	storage.extend(maps.fives.into_iter().map(|(key, values)| (key, values.into_iter().map(|(p, m)| (Some(p), vec![m])).collect())));
	storage.extend(maps.sixes.into_iter().map(|(key, values)| (key, values.into_iter().map(|ms| (None, ms.into())).collect())));
	storage.extend(maps.eights.into_iter().map(|(key, values)| (key, values.into_iter().map(|(p, ms)| (Some(p), ms.into())).collect())));
	storage.extend(maps.nines.into_iter().map(|(key, values)| (key, values.into_iter().map(|ms| (None, ms.into())).collect())));
	storage.extend(maps.elevens.into_iter().map(|(key, values)| (key, values.into_iter().map(|(p, ms)| (Some(p), ms.into())).collect())));
	storage.extend(maps.twelves.into_iter().map(|(key, values)| (key, values.into_iter().map(|ms| (None, ms.into())).collect())));
	storage.extend(maps.fourteens.into_iter().map(|(key, values)| (key, values.into_iter().map(|(p, ms)| (Some(p), ms.into())).collect())));
	// Remove keys which have a zero count between two non-zero counts.
	storage.retain(|(key, _)| {
		let mut key = *key;
		if key == 0 {
			return false;
		}
		key >>= (key.trailing_zeros() / 3) * 3;
		while key & 0b111 != 0 {
			key >>= 3;
		}
		key == 0
	});
	storage.sort_unstable_by_key(|(key, _)| *key);
	// Move all entries with `values.len() == 1` to the start of `storage`.
	storage.sort_by_key(|(_, values)| values.len() > 1);
	let storage_multiple_values_start = storage.iter().take_while(|(_, values)| values.len() == 1).count();
	assert!(storage_multiple_values_start <= 0x8000, "encoding scheme requires 0x8000 or fewer length-1 entries but there are 0x{storage_multiple_values_start:04X} of them");

	let mut f = vec![];

	let mut lut = vec![INVALID; 5_usize.pow(9)];
	let mut storage_i = 0;
	write!(f, "const STORAGE:&[(Option<NumberMeld>,Meld<NumberMeld>)]=&[")?;
	for (i, (key, values)) in storage.into_iter().enumerate() {
		assert!(values.is_sorted(), "{values:?}");
		assert!(values.array_windows().all(|[m1, m2]| m1 != m2), "{values:?}");

		let len = values.len();
		let storage_value =
			if len == 1 {
				#[expect(clippy::cast_possible_truncation)]
				{
					storage_i as u16
				}
			}
			else {
				assert!((2..=4).contains(&len));
				let storage_i = storage_i - storage_multiple_values_start;
				assert!(storage_i <= 0x1FFF, "encoding scheme requires 0x1FFF or fewer length-2+ entries but this is the 0x{storage_i:04X}th entry");
				#[expect(clippy::cast_possible_truncation)]
				{
					0x8000 | ((len as u16 - 2) << 13) | (storage_i as u16)
				}
			};
		storage_i += len;
		let key = (0..9).rev().fold(0_usize, |acc, offset| acc * 5 + ((key >> (offset * 3)) & 0b111) as usize);
		let previous = std::mem::replace(&mut lut[key], storage_value);
		assert_eq!(previous, INVALID, "two entries mapped to the same key 0x{key:08X}: 0x{previous:04X} and 0x{storage_value:04X}");

		if i > 0 {
			write!(f, ",")?;
		}
		for (i, (p, ms)) in values.into_iter().enumerate() {
			if i > 0 {
				write!(f, ",")?;
			}
			if let Some(p) = p {
				write!(f, "(O({p}),")?;
			}
			else {
				write!(f, "(X,")?;
			}

			if ms.is_empty() {
				write!(f, "M0)")?;
			}
			else {
				write!(f, "m{}(", ms.len())?;
				for (i, m) in ms.into_iter().enumerate() {
					if i > 0 {
						write!(f, ",")?;
					}
					write!(f, "{m}")?;
				}
				write!(f, "))")?;
			}
		}
	}
	write!(f, "];")?;

	write!(f, "const STORAGE_MULTIPLE_VALUES_START:usize={};", SmallInt(storage_multiple_values_start))?;

	// The first named block is full of invalid entries.
	let empty_block = [INVALID; BLOCK_LEN];
	let mut layer2 = vec![empty_block];
	let mut layer1: Vec<_> =
		lut
		.chunks(BLOCK_LEN)
		.map(|chunk| {
			let mut block = empty_block;
			block[..chunk.len()].copy_from_slice(chunk);
			if block == empty_block {
				// This block is also full of invalid entries. Dedupe it against the first block.
				0
			}
			else {
				#[expect(clippy::cast_possible_truncation)]
				let id = layer2.len() as u16;
				layer2.push(block);
				id
			}
		})
		.collect();
	// Any block not found in the outer layer is assumed to be the completely-invalid block.
	// So we can save space in the outer layer by removing explicitly defined completely-invalid blocks from the end.
	while let Some(0) = layer1.last() {
		layer1.pop();
	}

	write!(f, "const LAYER1:&[u16]=&[")?;
	for (i, id) in layer1.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "{}", SmallInt(id.into()))?;
	}
	write!(f, "];")?;

	write!(f, "const LAYER2:&[[u16;{}]]=&[", SmallInt(BLOCK_LEN))?;
	for (i, block) in layer2.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "[")?;
		for (i, value) in block.into_iter().enumerate() {
			if i > 0 {
				write!(f, ",")?;
			}
			if value == INVALID {
				write!(f, "I")?;
			}
			else {
				write!(f, "{}", SmallInt(value.into()))?;
			}
		}
		write!(f, "]")?;
	}
	write!(f, "];")?;

	// len = 0 value. This is given a special small name since it occurs very frequently.
	write!(f, "const I:u16=0xFFFF;")?;

	std::fs::write(path, f)?;

	Ok(())
}

#[derive(Clone, Copy, Debug)]
enum Number {
	One,
	Two,
	Three,
	Four,
	Five,
	Six,
	Seven,
	Eight,
	Nine,
}

impl Element for Number {
	type Meld = NumberMeld;
	type Pair = NumberMeld;

	fn elements_of_meld(m: Self::Meld) -> [Self; 3] {
		match m {
			NumberMeld::K1 => [Number::One; 3],
			NumberMeld::K2 => [Number::Two; 3],
			NumberMeld::K3 => [Number::Three; 3],
			NumberMeld::K4 => [Number::Four; 3],
			NumberMeld::K5 => [Number::Five; 3],
			NumberMeld::K6 => [Number::Six; 3],
			NumberMeld::K7 => [Number::Seven; 3],
			NumberMeld::K8 => [Number::Eight; 3],
			NumberMeld::K9 => [Number::Nine; 3],
			NumberMeld::S1 => [Number::One, Number::Two, Number::Three],
			NumberMeld::S2 => [Number::Two, Number::Three, Number::Four],
			NumberMeld::S3 => [Number::Three, Number::Four, Number::Five],
			NumberMeld::S4 => [Number::Four, Number::Five, Number::Six],
			NumberMeld::S5 => [Number::Five, Number::Six, Number::Seven],
			NumberMeld::S6 => [Number::Six, Number::Seven, Number::Eight],
			NumberMeld::S7 => [Number::Seven, Number::Eight, Number::Nine],
		}
	}

	fn elements_of_pair(p: Self::Pair) -> [Self; 2] {
		match p {
			NumberMeld::K1 => [Number::One; 2],
			NumberMeld::K2 => [Number::Two; 2],
			NumberMeld::K3 => [Number::Three; 2],
			NumberMeld::K4 => [Number::Four; 2],
			NumberMeld::K5 => [Number::Five; 2],
			NumberMeld::K6 => [Number::Six; 2],
			NumberMeld::K7 => [Number::Seven; 2],
			NumberMeld::K8 => [Number::Eight; 2],
			NumberMeld::K9 => [Number::Nine; 2],
			_ => unreachable!(),
		}
	}

	fn offset(self) -> u8 {
		match self {
			Self::One => 0,
			Self::Two => 1,
			Self::Three => 2,
			Self::Four => 3,
			Self::Five => 4,
			Self::Six => 5,
			Self::Seven => 6,
			Self::Eight => 7,
			Self::Nine => 8,
		}
	}
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
enum NumberMeld {
	/// Ankou 111 / Pair 11
	K1 = 0,
	/// Ankou 222 / Pair 22
	K2 = 2,
	/// Ankou 333 / Pair 33
	K3 = 4,
	/// Ankou 444 / Pair 44
	K4 = 6,
	/// Ankou 555 / Pair 55
	K5 = 8,
	/// Ankou 666 / Pair 66
	K6 = 10,
	/// Ankou 777 / Pair 77
	K7 = 12,
	/// Ankou 888 / Pair 88
	K8 = 14,
	/// Ankou 999 / Pair 99
	K9 = 16,

	/// Shun 123
	S1 = 1,
	/// Shun 234
	S2 = 3,
	/// Shun 345
	S3 = 5,
	/// Shun 456
	S4 = 7,
	/// Shun 567
	S5 = 9,
	/// Shun 678
	S6 = 11,
	/// Shun 789
	S7 = 13,
}

impl std::fmt::Display for NumberMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Debug::fmt(self, f)
	}
}

const ALL_MELDS: [NumberMeld; 16] = [
	NumberMeld::K1,
	NumberMeld::S1,
	NumberMeld::K2,
	NumberMeld::S2,
	NumberMeld::K3,
	NumberMeld::S3,
	NumberMeld::K4,
	NumberMeld::S4,
	NumberMeld::K5,
	NumberMeld::S5,
	NumberMeld::K6,
	NumberMeld::S6,
	NumberMeld::K7,
	NumberMeld::S7,
	NumberMeld::K8,
	NumberMeld::K9,
];

const ALL_PAIRS: [Option<NumberMeld>; 10] = [
	None,
	Some(NumberMeld::K1),
	Some(NumberMeld::K2),
	Some(NumberMeld::K3),
	Some(NumberMeld::K4),
	Some(NumberMeld::K5),
	Some(NumberMeld::K6),
	Some(NumberMeld::K7),
	Some(NumberMeld::K8),
	Some(NumberMeld::K9),
];
