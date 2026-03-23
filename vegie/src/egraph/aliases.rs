pub use egg::{Id, Symbol};
use std::sync::{Mutex, OnceLock};
use indexmap::IndexSet;

pub type Map<K, V> = rustc_hash::FxHashMap<K, V>;
pub type Set<K> = rustc_hash::FxHashSet<K>;

pub type EClass = Id;
pub type Operator = Id;

/// Utilities for generating identifiers bound to unique names.
pub struct SymbolIds;
static VOCABULARY: OnceLock<Mutex<IndexSet<Symbol>>> = OnceLock::new();
impl SymbolIds {
  pub fn from_symbol(symbol: &Symbol) -> Id {
    let mut v = VOCABULARY.get_or_init(|| Mutex::new(Default::default())).lock().unwrap();
    let (index, _wasnt_present) = v.insert_full(*symbol);
    Id::from(index)
  }
  pub fn to_symbol(id: Id) -> Option<Symbol> {
    let v = VOCABULARY.get_or_init(|| Mutex::new(Default::default())).lock().unwrap();
    v.get_index(id.into()).cloned()
  }
  pub fn from_string(string: &str) -> Id {
    SymbolIds::from_symbol(&Symbol::new(string))
  }
  pub fn to_string(id: Id) -> Option<&'static str> {
    SymbolIds::to_symbol(id).map(|s| s.as_str())
  }
}
