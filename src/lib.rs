use std::borrow::{Borrow};
use std::collections::hash_map::Keys;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::future::Future;
use std::hash::Hash;

use async_recursion::async_recursion;

#[cfg(debug_assertions)]
#[macro_export]
macro_rules! bad_exit {
    () => {
		panic!("Bad exit");
	};
}

#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! bad_exit {
    () => {
		std::process::exit(1)
	};
}


#[macro_export]
macro_rules! default_error {
    ($result: expr, $($arg: tt)*) => {
        error!("Faced the following error while {}:\n\t{:#?}", format!($($arg)*), $result)
    };
}


#[macro_export]
macro_rules! unwrap_result_or_default_error {
    ($result: expr, $($arg: tt)*) => {
        match $result {
            Ok(x) => x,
            Err(e) => {
                default_error!(e, $($arg)*);
                bad_exit!();
            }
        }
    };
}


#[macro_export]
macro_rules! unwrap_result_or_msg {
    ($result: expr, $($arg: tt)*) => {
        match $result {
            Ok(x) => x,
            Err(e) => {
                error!($($arg)*);
                bad_exit!();
            }
        }
    };
}

#[macro_export]
macro_rules! unwrap_option_or_msg {
    ($option: expr, $($arg: tt)*) => {
        match $option {
            Some(x) => x,
            None => {
                error!($($arg)*);
                bad_exit!();
            }
        }
    };
}


pub struct NestedMapKeys<'a, K: Eq + Hash, V> {
	keys: Keys<'a, K, MapOrItem<K, V>>
}


impl<'a, K: Eq + Hash, V> Iterator for NestedMapKeys<'a, K, V> {
	type Item = &'a K;

	fn next(&mut self) -> Option<Self::Item> {
		self.keys.next()
	}
}


enum MapOrItem<K: Eq + Hash, V> {
	Item(V),
	Map(NestedMap<K, V>)
}


impl<K: Eq + Hash + Clone, V: Clone> Clone for MapOrItem<K, V> {
	fn clone(&self) -> Self {
		match self {
			Self::Item(x) => Self::Item(x.clone()),
			Self::Map(x) => Self::Map(x.clone())
		}
	}
}


#[derive(Default)]
pub struct NestedMap<K: Eq + Hash, V> {
	map: HashMap<K, MapOrItem<K, V>>
}


impl<K: Eq + Hash + Debug> NestedMap<K, ()> {
	fn debug_fmt(&self, f: &mut Formatter<'_>, from: &String) -> std::fmt::Result {
		for (key, value) in &self.map {
			writeln!(f, "\t{:?} -> {:?}", from, key)?;
			if let MapOrItem::Map(map) = value {
				map.debug_fmt(f, &format!("{:?}", key))?;
			}
		}
		Ok(())
	}
}


impl<K: Eq + Hash> NestedMap<K, ()> {
	pub fn insert_key<I, T>(&mut self, keys: T) -> bool
		where
			I: Iterator<Item=K>,
			T: IntoIterator<Item=K, IntoIter=I>
	{
		self.insert_item(keys, ())
	}
}


impl<K: Eq + Hash + Debug> Debug for NestedMap<K, ()> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "digraph NestedMap {{")?;
		self.debug_fmt(f, &"root".to_string())?;
		writeln!(f, "}}")
	}
}


impl<K: Eq + Hash + Clone, V: Clone> Clone for NestedMap<K, V> {
	fn clone(&self) -> Self {
		Self {
			map: self.map.clone()
		}
	}
}


enum TraversalResult<'a, K: Eq + Hash, V> {
	/// The item found sits at exactly where the path specifies
	CompleteItem(&'a V),
	/// Traversal could not continue as we reached an item before the path was exhausted
	IncompleteItem(&'a V),
	/// Traversal ended on a map
	Map(&'a NestedMap<K, V>),
	/// Traversal ended because no items matched the path anymore
	Failed
}


enum MutTraversalResult<'a, K: Eq + Hash, V> {
	/// The item found sits at exactly where the path specifies
	CompleteItem(&'a mut V),
	/// Traversal could not continue as we reached an item before the path was exhausted
	IncompleteItem(&'a mut V),
	/// Traversal ended on a map
	Map(&'a mut NestedMap<K, V>),
	/// Traversal ended because no items matched the path anymore
	Failed
}


pub enum TopLevelGetResult<'a, K: Eq + Hash, V> {
	Item(&'a V),
	Map(&'a NestedMap<K, V>),
	Failed
}


pub enum KeyListError {
	NotAMap,
	NotFound
}


impl<K: Eq + Hash, V> NestedMap<K, V> {
	pub fn new() -> Self {
		Self {
			map: HashMap::new()
		}
	}

	pub fn list_keys<'a, I, T>(&'a self, keys: T) -> Result<NestedMapKeys<'a, K, V>, KeyListError>
		where
			I: Iterator<Item=K>,
			T: IntoIterator<Item=K, IntoIter=I>
	{
		match self.traverse(keys.into_iter()) {
			TraversalResult::Map(map) => Ok(NestedMapKeys{ keys: map.map.keys() }),
			TraversalResult::CompleteItem(_) => Err(KeyListError::NotAMap),
			_ => Err(KeyListError::NotFound)
		}
	}

	pub fn insert_item<I, T>(&mut self, keys: T, item: V) -> bool
		where
			I: Iterator<Item=K>,
			T: IntoIterator<Item=K, IntoIter=I>
	{
		let mut iter = keys.into_iter();
		let current_key = match iter.next() {
			Some(x) => x,
			None => return false
		};
		self.recursive_insert(iter, MapOrItem::Item(item), current_key)
	}

	pub fn insert_map<I, T>(&mut self, keys: T, map: Self) -> bool
		where
			I: Iterator<Item=K>,
			T: IntoIterator<Item=K, IntoIter=I>
	{
		let mut iter = keys.into_iter();
		let current_key = match iter.next() {
			Some(x) => x,
			None => return false
		};
		self.recursive_insert(iter, MapOrItem::Map(map), current_key)
	}

	pub fn delete_item<I, T>(&mut self, keys: T) -> Option<V>
		where
			I: Iterator<Item=K>,
			T: IntoIterator<Item=K, IntoIter=I>
	{
		let mut iter = keys.into_iter();
		let current_key = match iter.next() {
			Some(x) => x,
			None => return None
		};
		match self.recursive_delete(iter, false, current_key) {
			Some(MapOrItem::Item(x)) => Some(x),
			None => None,
			_ => unreachable!()
		}
	}

	pub fn delete_map<I, T>(&mut self, keys: T) -> Option<Self>
		where
			I: Iterator<Item=K>,
			T: IntoIterator<Item=K, IntoIter=I>
	{
		let mut iter = keys.into_iter();
		let current_key = match iter.next() {
			Some(x) => x,
			None => return None
		};
		match self.recursive_delete(iter, false, current_key) {
			Some(MapOrItem::Map(x)) => Some(x),
			None => None,
			_ => unreachable!()
		}
	}

	fn recursive_insert<I: Iterator<Item=K>>(&mut self, mut keys: I, item: MapOrItem<K, V>, current_key: K) -> bool {
		match self.map.get_mut(&current_key) {
			Some(MapOrItem::Map(map)) => {
				match keys.next() {
					Some(next_key) => map.recursive_insert(keys, item, next_key),
					None => false
				}
			}
			Some(_) => false,
			None => {
				self.map.insert(
					current_key,
					match keys.next() {
						Some(next_key) => {
							let mut map = NestedMap::new();
							map.recursive_insert(keys, item, next_key);
							MapOrItem::Map(map)
						}
						None => item
					}
				);
				true
			}
		}
	}

	fn recursive_delete<I: Iterator<Item=K>>(&mut self, mut keys: I, is_map: bool, current_key: K) -> Option<MapOrItem<K, V>> {
		if let Some(value) = self.map.remove(&current_key) {
			if matches!(value, MapOrItem::Map(_)) != is_map {
				self.map.insert(current_key, value);
				return None
			}
			return Some(value)
		}
		match self.map.get_mut(&current_key) {
			Some(MapOrItem::Map(map)) => {
				let next_key = keys.next()?;
				map.recursive_delete(keys, is_map, next_key)
			}
			_ => None
		}
	}

	fn traverse<Item, I>(&self, mut keys: I) -> TraversalResult<K, V>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
	{
		let mut last_map = self;

		loop {
			let key = match keys.next() {
				None => return TraversalResult::Map(last_map),
				Some(x) => x,
			};
			match last_map.map.get(key.borrow()) {
				None => return TraversalResult::Failed,
				Some(map_or_item) => match map_or_item {
					MapOrItem::Item(v) => return if keys.next().is_some() {
						TraversalResult::IncompleteItem(v)
					} else {
						TraversalResult::CompleteItem(v)
					},
					MapOrItem::Map(map) => last_map = map
				}
			}
		}
	}

	fn traverse_mut<Item, I>(&mut self, mut keys: I) -> MutTraversalResult<K, V>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
	{
		let mut last_map = self;

		loop {
			let key = match keys.next() {
				None => return MutTraversalResult::Map(last_map),
				Some(x) => x,
			};
			match last_map.map.get_mut(key.borrow()) {
				None => return MutTraversalResult::Failed,
				Some(map_or_item) => match map_or_item {
					MapOrItem::Item(v) => return if keys.next().is_some() {
						MutTraversalResult::IncompleteItem(v)
					} else {
						MutTraversalResult::CompleteItem(v)
					},
					MapOrItem::Map(map) => last_map = map
				}
			}
		}
	}

	pub fn top_level_get(&self, key: &K) -> TopLevelGetResult<K, V> {
		match self.map.get(key) {
			None => TopLevelGetResult::Failed,
			Some(MapOrItem::Map(map)) => TopLevelGetResult::Map(map),
			Some(MapOrItem::Item(v)) => TopLevelGetResult::Item(v)
		}
	}

	pub fn get_item<Item, I, T>(&self, keys: T) -> Option<&V>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		match self.traverse(keys.into_iter()) {
			TraversalResult::CompleteItem(x) => Some(x),
			_ => None
		}
	}
	pub fn get_item_mut<Item, I, T>(&mut self, keys: T) -> Option<&mut V>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		match self.traverse_mut(keys.into_iter()) {
			MutTraversalResult::CompleteItem(x) => Some(x),
			_ => None
		}
	}
	pub fn partial_get_item<Item, I, T>(&self, keys: T) -> Option<&V>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		match self.traverse(keys.into_iter()) {
			TraversalResult::CompleteItem(x) => Some(x),
			TraversalResult::IncompleteItem(x) => Some(x),
			_ => None
		}
	}
	pub fn partial_get_item_mut<Item, I, T>(&mut self, keys: T) -> Option<&mut V>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		match self.traverse_mut(keys.into_iter()) {
			MutTraversalResult::CompleteItem(x) => Some(x),
			MutTraversalResult::IncompleteItem(x) => Some(x),
			_ => None
		}
	}
	pub fn get_map<Item, I, T>(&self, keys: T) -> Option<&Self>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		match self.traverse(keys.into_iter()) {
			TraversalResult::Map(x) => Some(x),
			_ => None
		}
	}
	pub fn get_map_mut<Item, I, T>(&mut self, keys: T) -> Option<&mut Self>
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		match self.traverse_mut(keys.into_iter()) {
			MutTraversalResult::Map(x) => Some(x),
			_ => None
		}
	}
	pub fn contains<Item, I, T>(&self, keys: T) -> bool
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		self.get_item(keys).is_some()
	}
	pub fn partial_contains<Item, I, T>(&self, keys: T) -> bool
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		self.partial_get_item(keys).is_some()
	}
	pub fn contains_map<Item, I, T>(&self, keys: T) -> bool
		where
			Item: Borrow<K>,
			I: Iterator<Item=Item>,
			T: IntoIterator<Item=Item, IntoIter=I>
	{
		self.get_map(keys).is_some()
	}

	pub fn for_each<KF, VF, NewK, NewV>(self, key_fn: &KF, value_fn: &VF) -> NestedMap<NewK, NewV>
		where
			NewK: Eq + Hash,
			KF: Fn(K) -> NewK,
			VF: Fn(V) -> NewV
	{
		let mut new = NestedMap::new();

		for (key, value) in self.map {
			let key = key_fn(key);
			match value {
				MapOrItem::Item(v) => new.map.insert(key, MapOrItem::Item(value_fn(v))),
				MapOrItem::Map(map) => new.map.insert(key, MapOrItem::Map(map.for_each(key_fn, value_fn)))
			};
		}

		new
	}

	#[async_recursion]
	pub async fn async_for_each<FutK, FutV, KF, VF, NewK, NewV>(self, key_fn: &KF, value_fn: &VF) -> NestedMap<NewK, NewV>
		where
			NewK: Eq + Hash + Send,
			NewV: Send,
			FutK: Future<Output=NewK> + Send,
			FutV: Future<Output=NewV> + Send,
			KF: Fn(K) -> FutK + Sync,
			VF: Fn(V) -> FutV + Sync,
			K: Send + Sync + 'static,
			V: Send + Sync + 'static
	{
		let mut new = NestedMap::new();

		for (key, value) in self.map {
			let key = key_fn(key).await;
			match value {
				MapOrItem::Item(v) => new.map.insert(key, MapOrItem::Item(value_fn(v).await)),
				MapOrItem::Map(map) => new.map.insert(key, MapOrItem::Map(map.async_for_each(key_fn, value_fn).await))
			};
		}

		new
	}
}


impl<K: Eq + Hash, V> From<HashMap<K, V>> for NestedMap<K, V> {
	fn from(map: HashMap<K, V>) -> Self {
		NestedMap {
			map: map.into_iter().map(|(k, v)| (k, MapOrItem::Item(v))).collect()
		}
	}
}

pub type NestedSet<K> = NestedMap<K, ()>;
