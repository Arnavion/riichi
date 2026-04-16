mod honors;

mod numbers;

fn main() {
	let mut args = std::env::args_os();
	let _ = args.next().unwrap();

	let honors_path = args.next().unwrap();

	let numbers_path = args.next().unwrap();

	honors::run(honors_path.as_ref()).unwrap();

	numbers::run(numbers_path.as_ref()).unwrap();
}

trait Element: Copy + std::fmt::Debug {
	type Meld: Copy + std::fmt::Debug + Ord;
	type Pair: Copy + std::fmt::Debug + Ord;

	fn elements_of_meld(m: Self::Meld) -> [Self; 3];
	fn elements_of_pair(p: Self::Pair) -> [Self; 2];
	fn offset(self) -> u8;
	fn max(self) -> u32;
}

struct Key<TElement> {
	inner: u32,
	_element: std::marker::PhantomData<TElement>,
}

impl<TElement> Key<TElement> where TElement: Element {
	fn push_meld(&mut self, m: TElement::Meld) -> bool {
		for element in TElement::elements_of_meld(m) {
			if !self.push_element(element) {
				return false;
			}
		}
		true
	}

	fn push_pair(&mut self, p: Option<TElement::Pair>) -> bool {
		let Some(p) = p else { return true; };
		for element in TElement::elements_of_pair(p) {
			if !self.push_element(element) {
				return false;
			}
		}
		true
	}

	fn push_element(&mut self, element: TElement) -> bool {
		let offset = element.offset() * 3;
		let count = (self.inner >> offset) & 0b111;
		let max = element.max();
		if count == max {
			return false;
		}

		self.inner += 0b1 << offset;
		true
	}
}

impl<TElement> Clone for Key<TElement> {
	fn clone(&self) -> Self {
		Self {
			inner: self.inner,
			_element: Default::default(),
		}
	}
}

impl<TElement> Default for Key<TElement> {
	fn default() -> Self {
		Self {
			inner: 0,
			_element: Default::default(),
		}
	}
}

#[derive(Debug)]
struct Maps<TElement> where TElement: Element {
	twos: std::collections::BTreeMap<u32, TElement::Pair>,
	threes: std::collections::BTreeMap<u32, TElement::Meld>,
	fives: std::collections::BTreeMap<u32, Vec<(TElement::Pair, TElement::Meld)>>,
	sixes: std::collections::BTreeMap<u32, Vec<[TElement::Meld; 2]>>,
	eights: std::collections::BTreeMap<u32, Vec<(TElement::Pair, [TElement::Meld; 2])>>,
	nines: std::collections::BTreeMap<u32, Vec<[TElement::Meld; 3]>>,
	elevens: std::collections::BTreeMap<u32, Vec<(TElement::Pair, [TElement::Meld; 3])>>,
	twelves: std::collections::BTreeMap<u32, Vec<[TElement::Meld; 4]>>,
	fourteens: std::collections::BTreeMap<u32, Vec<(TElement::Pair, [TElement::Meld; 4])>>,
}

impl<TElement> Maps<TElement> where TElement: Element {
	fn new(all_melds: &[TElement::Meld], all_pairs: &[Option<TElement::Pair>]) -> Self {
		let mut result = Self {
			twos: Default::default(),
			threes: Default::default(),
			fives: Default::default(),
			sixes: Default::default(),
			eights: Default::default(),
			nines: Default::default(),
			elevens: Default::default(),
			twelves: Default::default(),
			fourteens: Default::default(),
		};

		for &p in all_pairs {
			let Some(p) = p else { continue; };

			let mut key = Key::<TElement>::default();
			if !key.push_pair(Some(p)) { continue; }

			result.twos.insert(key.inner, p);
		}

		for &p in all_pairs {
			let mut key = Key::<TElement>::default();

			if !key.push_pair(p) { continue; }

			for &m1 in all_melds {
				let mut key = key.clone();
				if !key.push_meld(m1) { continue; }

				if let Some(p) = p {
					result.fives.entry(key.inner).or_default().push((p, m1));
				}
				else {
					result.threes.insert(key.inner, m1);
				}
			}
		}

		for &p in all_pairs {
			let mut key = Key::<TElement>::default();

			if !key.push_pair(p) { continue; }

			for (i, &m1) in all_melds.iter().enumerate() {
				let mut key = key.clone();
				if !key.push_meld(m1) { continue; }

				for &m2 in all_melds.iter().skip(i) {
					let mut key = key.clone();
					if !key.push_meld(m2) { continue; }

					if let Some(p) = p {
						result.eights.entry(key.inner).or_default().push((p, [m1, m2]));
					}
					else {
						result.sixes.entry(key.inner).or_default().push([m1, m2]);
					}
				}
			}
		}

		for &p in all_pairs {
			let mut key = Key::<TElement>::default();

			if !key.push_pair(p) { continue; }

			for (i, &m1) in all_melds.iter().enumerate() {
				let mut key = key.clone();
				if !key.push_meld(m1) { continue; }

				for (i, &m2) in all_melds.iter().enumerate().skip(i) {
					let mut key = key.clone();
					if !key.push_meld(m2) { continue; }

					for &m3 in all_melds.iter().skip(i) {
						let mut key = key.clone();
						if !key.push_meld(m3) { continue; }

						if let Some(p) = p {
							result.elevens.entry(key.inner).or_default().push((p, [m1, m2, m3]));
						}
						else {
							result.nines.entry(key.inner).or_default().push([m1, m2, m3]);
						}
					}
				}
			}
		}

		for &p in all_pairs {
			let mut key = Key::<TElement>::default();

			if !key.push_pair(p) { continue; }

			for (i, &m1) in all_melds.iter().enumerate() {
				let mut key = key.clone();
				if !key.push_meld(m1) { continue; }

				for (i, &m2) in all_melds.iter().enumerate().skip(i) {
					let mut key = key.clone();
					if !key.push_meld(m2) { continue; }

					for (i, &m3) in all_melds.iter().enumerate().skip(i) {
						let mut key = key.clone();
						if !key.push_meld(m3) { continue; }

						for &m4 in all_melds.iter().skip(i) {
							let mut key = key.clone();
							if !key.push_meld(m4) { continue; }

							if let Some(p) = p {
								result.fourteens.entry(key.inner).or_default().push((p, [m1, m2, m3, m4]));
							}
							else {
								result.twelves.entry(key.inner).or_default().push([m1, m2, m3, m4]);
							}
						}
					}
				}
			}
		}

		result
	}
}

struct SmallInt(usize);

impl std::fmt::Display for SmallInt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let dec = format!("{}", self.0);
		let hex = format!("0x{:x}", self.0);
		let s = if dec.len() < hex.len() { dec } else { hex };
		f.write_str(&s)
	}
}
