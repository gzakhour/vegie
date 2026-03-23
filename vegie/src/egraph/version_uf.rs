use std::ops::{Deref, DerefMut};
use egg::{Id};

use crate::egraph::version_tree::{*};
use crate::egraph::aliases::{*};

#[derive(Debug, Clone)]
pub struct VersionedUnionFind<A> {
  version_tree: VersionTree,
  pub universe: Vec<A>,
  parents: Vec<Map<Id, Id>>,
}

impl<A> Default for VersionedUnionFind<A> {
  fn default() -> Self {
    VersionedUnionFind {
      version_tree: VersionTree::new(),
      universe: Vec::new(),
      parents: vec![Map::default()],
    }
  }
}

impl<A> VersionedUnionFind<A> {

  #[inline]
  pub fn versioning(&self) -> &VersionTree {
    &self.version_tree
  }

  pub fn branchout(&mut self, v: Version) -> Version {
    assert!(self.version_tree.exists(v), "Cannot branchout from removed version: version {v}",);
    let new_v = self.version_tree.branchout(v);
    let max_v = self.parents.len();
    let is_new_version = new_v >= max_v;
    if is_new_version {
      self.parents.push(Default::default());
    } /*else {
      // here version was removed before: parents are already empty
      } */
    new_v
  }

  pub fn twin(&mut self, v: Version) -> Version {
    assert!(v != VersionTree::ROOT_VERSION, "Cannot create a twin of the root version");
    assert!(
      self.version_tree.exists(v),
      "Cannot create a twin of a removed version: version {v}",
    );
    let parent = self.version_tree.superversion(v);
    let twin = self.version_tree.branchout(parent);
    if twin >= self.parents.len() {
      self.parents.push(self.parents[v].clone());
    } else {
      self.parents[twin] = self.parents[v].clone();
    }
    twin
  }

  pub fn project<'a>(&'a self, v: Version) -> Projection<&'a Self> {
    assert!(self.version_tree.exists(v), "Cannot project removed version: version {v}",);
    Projection { source: self, version: v }
  }

  pub fn project_mut<'a>(&'a mut self, v: Version) -> Projection<&'a mut Self> {
    assert!(self.version_tree.exists(v), "Cannot project removed version: version {v}",);
    Projection { source: self, version: v }
  }

  pub fn remove_version(&mut self, v: Version) {
    assert!(v != VersionTree::ROOT_VERSION, "Cannot remove the root version");
    assert!(self.version_tree.exists(v), "Cannot remove already removed version: version {v}",);
    self.clear_version(v);
    self.version_tree.remove(v);
  }

  pub fn rebase(&mut self, v: Version) {
    assert!(v != VersionTree::ROOT_VERSION, "Cannot rebase the root version");
    assert!(self.version_tree.exists(v), "Cannot rebase removed version: version {v}",);
    let mut parents: Map<Id, Id> = Default::default();
    let mut path = self.version_tree.path(v);
    while let Some(ancestor) = path.pop() {
      parents.extend(self.parents[ancestor].clone());
    }
    self.parents[v] = parents;
    self.version_tree.rebase(v, VersionTree::ROOT_VERSION);
  }

  pub fn get_parent_and_version(&self, x: Id, v: Version) -> (Id, Version) {
    let mut checkout = v;
    let parent = loop {
      match self.parents[checkout].get(&x) {
        Some(&parent) => break parent,
        None => checkout = self.version_tree.superversion(checkout),
      }
    };
    (parent, checkout)
  }

  #[inline]
  pub fn clear_version(&mut self, v: Version) {
    self.for_each_subversion(v, |this, sv| this.clear_version(sv));
    self.parents[v].clear();
  }

  #[inline]
  pub fn add_edge(&mut self, parent: Id, version: Version, child: Id) {
    self.parents[version].insert(child, parent);
  }

  #[inline(always)]
  pub fn for_each_subversion<F, B>(&mut self, superversion: Version, callback: F) where F: Fn(&mut Self, Version) -> B {
    for i in 0..self.versioning().subversions(superversion).len() {
      let subversion = self.versioning().subversions(superversion)[i];
      callback(self, subversion);
    }
  }
}

pub struct Projection<S: std::ops::Deref> {
  source: S,
  version: Version,
}

impl<A, S: Deref<Target = VersionedUnionFind<A>>> Projection<S> {
  #[inline]
  pub fn get_parent_and_version(&self, x: Id) -> (Id, Version) {
    self.source.get_parent_and_version(x, self.version)
  }

  #[inline]
  pub fn universe(&self) -> impl std::iter::Iterator<Item = Id> {
    (0 .. self.source.universe.len()).map(|i| i.into())
  }

  #[inline]
  pub fn get_element(&self, x: Id) -> &A {
    &self.source.universe[Into::<usize>::into(x)]
  }

  #[inline]
  pub fn get_parent(&self, x: Id) -> Id {
    self.get_parent_and_version(x).0
  }

  pub fn find(&mut self, mut x: Id) -> Id {
    loop {
      let parent = self.get_parent(x);
      if parent == x { return x }
      x = parent;
    }
  }
}

impl<A, S: DerefMut<Target = VersionedUnionFind<A>>> Projection<S> {

  pub fn union(&mut self, x: Id, y: Id) -> Id {
    let xc = self.find_mut(x);
    let yc = self.find_mut(y);
    if xc == yc {
        return xc;
    }
    self.union_canonical(xc, yc)
  }


  #[inline(always)]
  pub fn propagate<F: Fn(Projection<&mut VersionedUnionFind<A>>) -> B, B>(&mut self, callback: F) {
    self.source.for_each_subversion(self.version, |this, sv| callback(this.project_mut(sv)));
  }

  pub fn new_element(&mut self, element: A) -> Id {
    let id = Id::from(self.source.universe.len());
    self.source.universe.push(element);
    self.source.parents[VersionTree::ROOT_VERSION].insert(id, id);
    id
  }

  pub fn find_mut(&mut self, x: Id) -> Id {
    let mut current = x;
    let (mut parent, mut checkout) = self.get_parent_and_version(current);
    let mut compress: bool = true;
    while current != parent {
      let child = current;
      let previous_checkout = checkout;
      current = parent;
      (parent, checkout) = self.get_parent_and_version(current);
      if compress && (current != parent || previous_checkout != self.version) {
        self.source.add_edge(parent, self.version, child); // compression
      }
      compress = !compress;
    }
    if checkout != self.version {
      self.source.add_edge(current, self.version, current);
    }
    current
  }

  pub fn union_canonical(&mut self, xc: Id, yc: Id) -> Id {
    self.propagate(|mut sp| sp.union(xc, yc));
    let (parent, child) = (xc, yc);
    self.source.add_edge(parent, self.version, child);
    parent
  }
}
