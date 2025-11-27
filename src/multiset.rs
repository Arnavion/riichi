#[derive(Clone, Debug)]
pub(crate) struct MultiSet<T> {
	inner: std::collections::BTreeMap<T, std::num::NonZero<usize>>,
	len: usize,
}

impl<T> MultiSet<T> {
	pub(crate) fn new() -> Self {
		Self {
			inner: Default::default(),
			len: 0,
		}
	}

	pub(crate) const fn len(&self) -> usize {
		self.len
	}

	pub(crate) fn counts(&self) -> impl Iterator<Item = std::num::NonZero<usize>> {
		self.inner.values().copied()
	}
}

impl<T> MultiSet<T> where T: Ord {
	pub(crate) fn insert(&mut self, element: T) {
		match self.inner.entry(element) {
			std::collections::btree_map::Entry::Vacant(entry) => {
				entry.insert(std::num::NonZero::new(1).unwrap());
				self.len += 1;
			},
			std::collections::btree_map::Entry::Occupied(entry) => {
				let count = entry.into_mut();
				*count = count.checked_add(1).unwrap();
			},
		}
	}

	pub(crate) fn get(&self, element: &T) -> usize {
		self.inner.get(element).copied().map(std::num::NonZero::get).unwrap_or_default()
	}
}

impl<T> Default for MultiSet<T> {
	fn default() -> Self {
		Self::new()
	}
}

impl<A> FromIterator<A> for MultiSet<A> where A: Ord {
	fn from_iter<T>(iter: T) -> Self where T: IntoIterator<Item = A> {
		let mut result: Self = Default::default();
		for element in iter {
			result.insert(element);
		}
		result
	}
}
