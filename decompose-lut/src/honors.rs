use super::{Element, Maps, SmallInt};

pub(crate) fn run(path: &std::path::Path) -> std::io::Result<()> {
	use std::io::Write;

	let maps = Maps::<Honor>::new(&ALL_MELDS, &ALL_PAIRS);

	let mut f = std::fs::File::create(path)?;

	write!(f, "use{{Some as Y,None as N}};")?;
	write!(f, "use super::{{Meld,Meld::*,Honor,Honor::*}};")?;

	write!(f, "type R=(u32,Meld<Honor>,Option<Honor>);")?;

	write!(f, "pub const ZEROS:&[R]=&[(0,M0,N)];")?;

	write!(f, "pub const TWOS:&[R]=&[")?;
	for (i, (key, p)) in maps.twos.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M0,Y({p}))", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const THREES:&[R]=&[")?;
	for (i, (key, m1)) in maps.threes.into_iter().enumerate() {
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M1({m1}),N)", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const FIVES:&[R]=&[")?;
	for (i, (key, mut values)) in maps.fives.into_iter().enumerate() {
		let (m1, p) = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M1({m1}),Y({p}))", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const SIXES:&[R]=&[")?;
	for (i, (key, mut values)) in maps.sixes.into_iter().enumerate() {
		let [m1, m2] = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M2({m1},{m2}),N)", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const EIGHTS:&[R]=&[")?;
	for (i, (key, mut values)) in maps.eights.into_iter().enumerate() {
		let ([m1, m2], p) = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M2({m1},{m2}),Y({p}))", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const NINES:&[R]=&[")?;
	for (i, (key, mut values)) in maps.nines.into_iter().enumerate() {
		let [m1, m2, m3] = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M3({m1},{m2},{m3}),N)", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const ELEVENS:&[R]=&[")?;
	for (i, (key, mut values)) in maps.elevens.into_iter().enumerate() {
		let ([m1, m2, m3], p) = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M3({m1},{m2},{m3}),Y({p}))", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const TWELVES:&[R]=&[")?;
	for (i, (key, mut values)) in maps.twelves.into_iter().enumerate() {
		let [m1, m2, m3, m4] = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M4({m1},{m2},{m3},{m4}),N)", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	write!(f, "pub const FOURTEENS:&[R]=&[")?;
	for (i, (key, mut values)) in maps.fourteens.into_iter().enumerate() {
		let ([m1, m2, m3, m4], p) = values.pop_first().unwrap();
		assert!(values.is_empty());
		if i > 0 {
			write!(f, ",")?;
		}
		write!(f, "({},M4({m1},{m2},{m3},{m4}),Y({p}))", SmallInt(key as usize))?;
	}
	write!(f, "];")?;

	Ok(())
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
enum Honor {
	/// Ton
	WE = 0,
	/// Nan
	WS = 1,
	/// Shaa
	WW = 2,
	/// Pei
	WN = 3,
	/// Haku
	DW = 4,
	/// Hatsu
	DG = 5,
	/// Chun
	DR = 6,
}

impl std::fmt::Display for Honor {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Debug::fmt(self, f)
	}
}

impl Element for Honor {
	type Meld = Self;
	type Pair = Self;

	fn elements_of_meld(m: Self::Meld) -> [Self; 3] {
		[m; 3]
	}

	fn elements_of_pair(p: Self::Pair) -> [Self; 2] {
		[p; 2]
	}

	fn offset(self) -> u8 {
		self as u8
	}

	fn max(self) -> u32 {
		4
	}
}

const ALL_MELDS: [Honor; 7] = [
	Honor::WE,
	Honor::WS,
	Honor::WW,
	Honor::WN,
	Honor::DW,
	Honor::DG,
	Honor::DR,
];

const ALL_PAIRS: [Option<Honor>; 8] = [
	None,
	Some(Honor::WE),
	Some(Honor::WS),
	Some(Honor::WW),
	Some(Honor::WN),
	Some(Honor::DW),
	Some(Honor::DG),
	Some(Honor::DR),
];
