use super::{Element, Maps, SmallInt};

pub(crate) fn run(path: &std::path::Path) -> std::io::Result<()> {
	use std::io::Write;

	let maps = Maps::<Number>::new(&ALL_MELDS, &ALL_PAIRS);

	let mut f = std::fs::File::create(path)?;

	write!(f, "use{{Some as Y,None as N}};")?;
	write!(f, "use super::{{Meld,Meld::*,NumberMeld,NumberMeld::*}};")?;
	write!(f, "type R=(u32,u16,u16);")?;
	write!(f, "pub const STORAGE:&[(Meld<NumberMeld>,Option<NumberMeld>)]=&[")?;

	write!(f, "(M0,N)")?;

	let mut storage_i = 1;

	let twos: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.twos.into_iter()
		.map(|(key, p)| {
			let storage_start = storage_i;
			let storage_len = 1;
			storage_i += storage_len;
			write!(f, ",(M0,Y({p}))")?;
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let twos = twos?;

	let threes: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.threes.into_iter()
		.map(|(key, m1)| {
			let storage_start = storage_i;
			let storage_len = 1;
			storage_i += storage_len;
			write!(f, ",(M1({m1}),N)")?;
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let threes = threes?;

	let fives: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.fives.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for (m1, p) in values {
				write!(f, ",(M1({m1}),Y({p}))")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let fives = fives?;

	let sixes: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.sixes.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for [m1, m2] in values {
				write!(f, ",(M2({m1},{m2}),N)")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let sixes = sixes?;

	let eights: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.eights.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for ([m1, m2], p) in values {
				write!(f, ",(M2({m1},{m2}),Y({p}))")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let eights = eights?;

	let nines: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.nines.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for [m1, m2, m3] in values {
				write!(f, ",(M3({m1},{m2},{m3}),N)")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let nines = nines?;

	let elevens: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.elevens.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for ([m1, m2, m3], p) in values {
				write!(f, ",(M3({m1},{m2},{m3}),Y({p}))")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let elevens = elevens?;

	let twelves: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.twelves.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for [m1, m2, m3, m4] in values {
				write!(f, ",(M4({m1},{m2},{m3},{m4}),N)")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let twelves = twelves?;

	let fourteens: std::io::Result<std::collections::BTreeMap<_, _>> =
		maps.fourteens.into_iter()
		.map(|(key, values)| {
			let storage_start = storage_i;
			let storage_len = values.len();
			storage_i += storage_len;
			for ([m1, m2, m3, m4], p) in values {
				write!(f, ",(M4({m1},{m2},{m3},{m4}),Y({p}))")?;
			}
			Ok((key, (storage_start, storage_start + storage_len)))
		})
		.collect();
	let fourteens = fourteens?;

	write!(f, "];")?;

	write!(f, "pub const ZEROS:&[R]=&[(0,0,1)];")?;

	write!(f, "pub const TWOS:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in twos.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const THREES:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in threes.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const FIVES:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in fives.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const SIXES:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in sixes.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const EIGHTS:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in eights.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const NINES:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in nines.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const ELEVENS:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in elevens.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const TWELVES:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in twelves.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	write!(f, "pub const FOURTEENS:&[R]=&[")?;
	for (i, (key, (storage_start, storage_end))) in fourteens.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},{},{})", SmallInt(key as usize), SmallInt(storage_start), SmallInt(storage_end))?;
	}
	write!(f, "];")?;

	Ok(())
}

#[derive(Clone, Copy, Debug)]
enum Number {
	One,
	Two,
	Three,
	Four,
	Five,
	FiveRed,
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
			NumberMeld::K0 => [Number::One; 3],
			NumberMeld::K1 => [Number::Two; 3],
			NumberMeld::K2 => [Number::Three; 3],
			NumberMeld::K4 => [Number::Four; 3],
			NumberMeld::K6 => [Number::Five; 3],
			NumberMeld::K7 => [Number::Five, Number::Five, Number::FiveRed],
			NumberMeld::K8 => [Number::Six; 3],
			NumberMeld::K9 => [Number::Seven; 3],
			NumberMeld::KA => [Number::Eight; 3],
			NumberMeld::KB => [Number::Nine; 3],
			NumberMeld::S0 => [Number::One, Number::Two, Number::Three],
			NumberMeld::S1 => [Number::Two, Number::Three, Number::Four],
			NumberMeld::S2 => [Number::Three, Number::Four, Number::Five],
			NumberMeld::S3 => [Number::Three, Number::Four, Number::FiveRed],
			NumberMeld::S4 => [Number::Four, Number::Five, Number::Six],
			NumberMeld::S5 => [Number::Four, Number::FiveRed, Number::Six],
			NumberMeld::S6 => [Number::Five, Number::Six, Number::Seven],
			NumberMeld::S7 => [Number::FiveRed, Number::Six, Number::Seven],
			NumberMeld::S8 => [Number::Six, Number::Seven, Number::Eight],
			NumberMeld::S9 => [Number::Seven, Number::Eight, Number::Nine],
		}
	}

	fn elements_of_pair(p: Self::Pair) -> [Self; 2] {
		match p {
			NumberMeld::K0 => [Number::One; 2],
			NumberMeld::K1 => [Number::Two; 2],
			NumberMeld::K2 => [Number::Three; 2],
			NumberMeld::K4 => [Number::Four; 2],
			NumberMeld::K6 => [Number::Five; 2],
			NumberMeld::K7 => [Number::Five, Number::FiveRed],
			NumberMeld::K8 => [Number::Six; 2],
			NumberMeld::K9 => [Number::Seven; 2],
			NumberMeld::KA => [Number::Eight; 2],
			NumberMeld::KB => [Number::Nine; 2],
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
			Self::FiveRed => 5,
			Self::Six => 6,
			Self::Seven => 7,
			Self::Eight => 8,
			Self::Nine => 9,
		}
	}

	fn max(self) -> u32 {
		match self {
			Self::One |
			Self::Two |
			Self::Three |
			Self::Four |
			Self::Six |
			Self::Seven |
			Self::Eight |
			Self::Nine => 4,
			Self::Five => 3,
			Self::FiveRed => 1,
		}
	}
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

impl std::fmt::Display for NumberMeld {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Debug::fmt(self, f)
	}
}

impl PartialEq for NumberMeld {
	fn eq(&self, other: &Self) -> bool {
		matches!(self.cmp(other), std::cmp::Ordering::Equal)
	}
}

impl Eq for NumberMeld {}

impl PartialOrd for NumberMeld {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for NumberMeld {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		(*self as u8 & !0b10).cmp(&(*other as u8 & !0b10))
	}
}

const ALL_MELDS: [NumberMeld; 20] = [
	NumberMeld::K0,
	NumberMeld::K1,
	NumberMeld::K2,
	NumberMeld::K4,
	NumberMeld::K6,
	NumberMeld::K7,
	NumberMeld::K8,
	NumberMeld::K9,
	NumberMeld::KA,
	NumberMeld::KB,
	NumberMeld::S0,
	NumberMeld::S1,
	NumberMeld::S2,
	NumberMeld::S3,
	NumberMeld::S4,
	NumberMeld::S5,
	NumberMeld::S6,
	NumberMeld::S7,
	NumberMeld::S8,
	NumberMeld::S9,
];

const ALL_PAIRS: [Option<NumberMeld>; 11] = [
	None,
	Some(NumberMeld::K0),
	Some(NumberMeld::K1),
	Some(NumberMeld::K2),
	Some(NumberMeld::K4),
	Some(NumberMeld::K6),
	Some(NumberMeld::K7),
	Some(NumberMeld::K8),
	Some(NumberMeld::K9),
	Some(NumberMeld::KA),
	Some(NumberMeld::KB),
];
