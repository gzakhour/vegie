
use crate::egraph::aliases::{*};
use crate::egraph::version_tree::{*};
use crate::egraph::version_uf::{*};
use crate::egraph::bitset::{*};
use crate::egraph::ematching::{*};

use std::ops::{Deref, DerefMut};
use std::time::{Instant, Duration};
use std::collections::{HashMap};

use egg::{Id, Pattern, Subst, StopReason, SearchMatches};

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct ENode {
  pub op: Operator,
  pub args: Vec<EClass>,
}

impl ENode {
  /// #### Return
  /// A new [ENode] representing the uninterpreted function `operator` applied
  /// to no arguments.
  pub fn constant(operator: Operator) -> ENode {
    ENode { op: operator, args: Vec::new() }
  }

  /// #### Return
  /// A new [ENode] representing the uninterpreted function `operator` applied
  /// to the arguments `arguments`.
  pub fn application(operator: Operator, arguments: Vec<EClass>) -> ENode {
    ENode { op: operator, args: arguments }
  }
}

#[derive(Clone)]
pub struct VersionedEGraph {
  unionfind: VersionedUnionFind<ENode>,
  enodes_by_op: Vec<Map<ENode, EClass>>,
  // ---- CACHES ---------------------------------------------------------------------------------
  // The following fields do not increase expressiveness, but speed up certain operations.
  // On the other hand, they increase memory consumption and maintainance cost for operations.
  // ---------------------------------------------------------------------------------------------
  enodes_by_version: Vec<BitSet>,
  dependants: Vec<Map<EClass, Set<EClass>>>, // TODO use SparseMap?
  worklist: Vec<Vec<EClass>>,
  dirty_versions: BitSet,
  eclasses_by_version: Map<Version, Map<EClass, Vec<EClass>>>,
  max_ematching_caches: usize,
}

impl Default for VersionedEGraph {
  fn default() -> Self {
    VersionedEGraph {
      unionfind: VersionedUnionFind::default(),
      enodes_by_op: vec![],
      enodes_by_version: vec![Default::default()],
      dependants: vec![Default::default()],
      worklist: vec![Vec::new()],
      dirty_versions: Default::default(),
      eclasses_by_version: Default::default(),
      max_ematching_caches: 0,
    }
  }
}

impl VersionedEGraph {

  #[inline(always)]
  pub fn versioning(&self) -> &VersionTree {
    self.unionfind.versioning()
  }

  pub fn branchout(&mut self, v: Version) -> Version {
    assert!(self.versioning().exists(v), "Cannot branchout from removed version: version {v}");
    self.project_mut(v).rebuild();

    let new_v = self.unionfind.branchout(v);
    let max_v = self.dependants.len();
    let is_new_version = new_v >= max_v;

    // TODO it should be possible to reduce cloning here by traversing
    //    superversions to retrieve versioned information
    if is_new_version {
      self.worklist.push(Default::default());
      self.dependants.push(Default::default());
      self.enodes_by_version.push(self.enodes_by_version[v].clone());
    } else {
      // here version was removed before: worklist and dependants are already empty
      // self.worklist[new_v] = Default::default();
      // self.dependants[new_v] = Default::default();
      self.enodes_by_version[new_v] = self.enodes_by_version[v].clone();
    }
    self.project_mut(new_v).inherit_ematching_cache();
    new_v
  }

  pub fn twin(&mut self, v: Version) -> Version {
    assert!(self.versioning().exists(v), "Cannot branchout from removed version: version {v}");
    self.project_mut(v).rebuild();

    let new_v = self.unionfind.twin(v);
    let max_v = self.dependants.len();
    let is_new_version = new_v >= max_v;
    if is_new_version {
      self.worklist.push(self.worklist[v].clone());
      self.dependants.push(self.dependants[v].clone());
      self.enodes_by_version.push(self.enodes_by_version[v].clone());
    } else {
      self.worklist[new_v] = self.worklist[v].clone();
      self.dependants[new_v] = self.dependants[v].clone();
      self.enodes_by_version[new_v] = self.enodes_by_version[v].clone();
    }
    if self.max_ematching_caches > 0 {
      self.eclasses_by_version.insert(new_v, self.eclasses_by_version[&v].clone());
    }
    new_v
  }

  pub fn project<'a>(&'a self, v: Version) -> Projection<&'a Self> {
    assert!(self.versioning().exists(v), "Cannot project removed version: version {v}");
    Projection { source: self, version: v }
  }

  pub fn project_mut<'a>(&'a mut self, v: Version) -> Projection<&'a mut Self> {
    assert!(self.versioning().exists(v), "Cannot project removed version: version {v}");
    Projection { source: self, version: v }
  }

  pub fn remove_version(&mut self, v: Version) {
    assert!(v != VersionTree::ROOT_VERSION, "Cannot remove the root version");
    assert!(self.versioning().exists(v), "Cannot remove already removed version: version {v}");
    self.clear_version(v);
    self.unionfind.remove_version(v);
  }

  pub fn get_parent_and_version(&self, x: EClass, v: Version) -> (EClass, Version) {
    self.unionfind.get_parent_and_version(x, v)
  }

  pub fn clear_version(&mut self, v: Version) {
    self.for_each_subversion(v, |this, sv| this.clear_version(sv));
    self.worklist[v].clear();
    self.dependants[v].clear();
    self.enodes_by_version[v].clear();
    self.eclasses_by_version.remove(&v);
  }

  #[inline(always)]
  pub fn for_each_subversion<F, B>(&mut self, superversion: Version, callback: F) where F: Fn(&mut Self, Version) -> B {
    for i in 0..self.versioning().subversions(superversion).len() {
      let subversion = self.versioning().subversions(superversion)[i];
      callback(self, subversion);
    }
  }
}

pub struct Projection<S: Deref<Target = VersionedEGraph>> {
  source: S,
  version: Version,
}

impl<S> Projection<S> where S: Deref<Target = VersionedEGraph> {
  #[inline]
  pub fn is_clean(&self) -> bool {
    !self.source.dirty_versions.contains(self.version)
  }

  pub fn universe(&self) -> impl std::iter::Iterator<Item = EClass> {
    (0 .. self.source.unionfind.universe.len())
      .filter(|xc| self.source.enodes_by_version[self.version].contains(*xc))
      .map(|xc| xc.into())
  }

  #[inline]
  pub fn get_enode(&self, x: EClass) -> &ENode {
    &self.source.unionfind.universe[Into::<usize>::into(x)]
  }

  pub fn get_class(&self, xn: &ENode) -> Option<&EClass> {
    self.source
      .enodes_by_op
      .get(Into::<usize>::into(xn.op))
      .and_then(|xns| xns.get(xn))
      .filter(|&xc| self.source.enodes_by_version[self.version].contains(Into::<usize>::into(*xc)))
  }

  #[inline]
  pub fn get_parent(&self, x: EClass) -> EClass {
    self.source.unionfind.project(self.version).get_parent(x)
  }

  #[inline]
  pub fn find(&self, x: EClass) -> EClass {
    self.source.unionfind.project(self.version).find(x)
  }

  pub fn canonicalize(&self, xn: ENode) -> ENode {
    let mut xn = xn.clone();
    for i in 0..xn.args.len() {
      xn.args[i] = self.find(xn.args[i])
    }
    xn
  }

}


impl<S> Projection<S> where S: DerefMut<Target = VersionedEGraph> {
  #[inline(always)]
  pub fn propagate<O, F: Fn(Projection<&mut VersionedEGraph>) -> O>(&mut self, callback: F) {
      self.source.for_each_subversion(self.version, |this, sv| callback(this.project_mut(sv)));
  }

  #[inline(always)]
  pub fn restore_congruence<I: std::iter::IntoIterator<Item = EClass>>(&mut self, dependants: I) {
    for stale in dependants {
      let stale_n = self.get_enode(stale);
      let fresh_n = self.canonicalize_mut(stale_n.clone());
      let fresh = self.add_canonical(fresh_n);
      self.union(fresh, stale);
    }
  }

  pub fn add_to_all_descendants(&mut self, xc: EClass) {
    self.propagate(|mut sv| {
      if sv.source.enodes_by_version[sv.version].add(Into::<usize>::into(xc)) {
        sv.add_to_all_descendants(xc);
      }
    });
  }

  pub fn add(&mut self, xn: ENode) -> EClass {
    let xn = self.canonicalize_mut(xn);
    self.add_canonical(xn)
  }

  pub fn union(&mut self, x: EClass, y: EClass) -> EClass {
    let xc = self.find_mut(x);
    let yc = self.find_mut(y);
    if xc == yc {
      return xc;
    }
    self.union_canonical(xc, yc)
  }

  pub fn canonicalize_mut(&mut self, mut xn: ENode) -> ENode {
    for i in 0..xn.args.len() {
      xn.args[i] = self.find_mut(xn.args[i])
    }
    xn
  }

  pub fn add_canonical(&mut self, xn: ENode) -> EClass {
    let xc: EClass = match self.source.enodes_by_op.get(Into::<usize>::into(xn.op)).and_then(|xns| xns.get(&xn)) {
      Some(&x) => self.find_mut(x),
      None => {
        let x = self.source.unionfind.project_mut(self.version).new_element(xn.clone());
        let op_i = Into::<usize>::into(xn.op);
        if op_i >= self.source.enodes_by_op.len() {
          self.source.enodes_by_op.resize_with(op_i + 1, Default::default);
        }
        self.source.enodes_by_op[op_i].insert(xn.clone(), x);
        x
      },
    };
    if !self.source.enodes_by_version[self.version].contains(Into::<usize>::into(xc)) {
      self.source.enodes_by_version[self.version].add(Into::<usize>::into(xc));
      for i in 0..self.get_enode(xc).args.len() {
        let argi = self.get_enode(xc).args[i];
        self.source.dependants[self.version].entry(argi).or_default().insert(xc);
      }
      self.source
        .eclasses_by_version
        .get_mut(&self.version)
        .map(|xcs| xcs.insert(xc, vec![xc]));
    }
    // NOTE propagation uses `add_canonical` because the user should be able
    // to use the class of `xn` in all subversions. However, `xn` may have
    // different canonicalizations in the subversions, so we restore
    // congruence for it. Failing Test:
    // [crate::pub structures::egraph::versioned::testing::version_inheritance_of_uncanonical_enodes]
    self.propagate(|mut sv| {
      let xcc = sv.add(xn.clone());
      sv.union(xc, xcc);
    });
    // TODO optimize this: there shouldn't be a need to traverse the version
    //    tree twice (once in propagate, once here)
    self.add_to_all_descendants(xc);
    xc
  }

  pub fn find_mut(&mut self, x: EClass) -> EClass {
    self.source.unionfind.project_mut(self.version).find_mut(x)
  }

  pub fn union_canonical(&mut self, xc: EClass, yc: EClass) -> EClass {
    // NOTE propagation uses `union` because `xc` and `yc` are assumed to be
    // canonical in this version, but may not be canonical in subversions
    self.propagate(|mut sv| sv.union(xc, yc));

    // NOTE order by increasing id (age), which is a partial ordering on
    // depth (?). This avoids infinite loops during rebuilding.
    // Failing Test: [crate::egraph::testing::recursive_eclasses]
    // TODO consider ordering by self.dependants.len() to reduce repairs.
    let mut parent = xc;
    let mut child = yc;
    if parent > child {
      std::mem::swap(&mut parent, &mut child);
    }
    self.source.unionfind.add_edge(parent, self.version, child);

    self.source.worklist[self.version].push(child);
    self.source.dirty_versions.add(self.version);
    if let Some(eclasses) = self.source.eclasses_by_version.get_mut(&self.version) {
      let mut child_classes = eclasses.remove(&child);
      let parent_classes = eclasses.entry(parent).or_insert_with(|| vec![parent]);
      match child_classes {
        None => parent_classes.push(child),
        Some(ref mut child_classes) => parent_classes.append(child_classes),
      }
    }

    parent
  }

  pub fn rebuild(&mut self) {
    // NOTE rebuilding does not need to be propagated to:
    // - superversions: (i) before a version is created, its superversion is
    //   already rebuilt; (ii) after a version is created, all unions in the
    //   superversion are propagated to the subversion, updating its
    //   worklist the same way
    // - subversions: congruence in this version is independent from
    //   congruence in the subversions
    // TODO for performances, consider not updating the worklist when
    // propagating unions to the subversions, and instead rebuilding all
    // superversions when rebuilding a version (probably not easy, since
    // propagating unions could add different eclasses to the worklist in
    // different subversions)

    // NOTE if the worklist is empty, there is nothing to do: this
    // short-circuit is needed to avoid re-optimizing the cache
    if self.source.worklist[self.version].is_empty() {
      return;
    }

    // NOTE While not necessary, propagating rebuilding to subversions
    // allows us to remove the dependants of a repaired EClass from the
    // current version, speeding up future rebuilds. Notably, congruence may
    // not be restored for subversions at the end of rebuild. Failing test:
    // [crate::pub structures::egraph::versioned::testing::version_inheritance_of_rebuilding]
    self.propagate(|mut sv| sv.rebuild());

    // NOTE every EClass only ever appears in the worklist once for a
    // version, because it can only ever be the child in a union once

    // Restore congruence in this version...
    while let Some(child) = self.source.worklist[self.version].pop() {
      self.repair(child);
    }
    self.rebuild_ematching_cache();
    self.source.dirty_versions.remove(self.version);
  }
}

impl<S> Projection<S> where S: DerefMut<Target = VersionedEGraph> {
  pub fn repair(&mut self, dependency: EClass) {
    // ... for the dependants stored in this version
    if let Some(dependants) = self.source.dependants[self.version].remove(&dependency) {
      self.restore_congruence(dependants);
    }
    // ... for the dependants stored in the superversions
    let mut checkout = self.version;
    while checkout != VersionTree::ROOT_VERSION {
      checkout = self.source.versioning().superversion(checkout);

      // NOTE the dependants in the superversions cannot be removed,
      // as they may be needed for their own rebuilding
      if let Some(dependants) = self.source.dependants[checkout].get(&dependency).cloned() {
        self.restore_congruence(dependants);
      }
    }
  }
}




// JUST EMATCHING STUFF



#[derive(Default)]
pub struct RunnerConfig {
  pub timeout: Option<Duration>,
  pub node_limit: Option<usize>,
  pub iter_limit: Option<usize>,
}


impl VersionedEGraph {
  pub fn with_ematching_caches(n: usize) -> Self {
    let mut egraph = Self { max_ematching_caches: n, ..Default::default() };
    egraph.project_mut(VersionTree::ROOT_VERSION).init_ematching_cache();
    egraph
  }
}

impl<S> Projection<S> where S: DerefMut<Target = VersionedEGraph> {
  #[inline(always)]
  fn has_cache(&self) -> bool {
    self.source.eclasses_by_version.contains_key(&self.version)
  }

  fn new_ematching_cache(&self) -> Map<EClass, Vec<EClass>> {
    let mut cache: Map<EClass, Vec<EClass>> = Default::default();
    // NOTE already sorted by operator (the index of the vector)
    let mut seen: Set<EClass> = Default::default(); // TODO is there a better way to deduplicate?
    for ops in self.source.enodes_by_op.iter() {
      for (xn, xc) in ops {
        if self.source.enodes_by_version[self.version].contains((*xc).into()) {
          let xn = self.canonicalize(xn.clone());
          let xc = self.get_class(&xn).unwrap();
          if !seen.insert(*xc) {
            continue;
          }
          let xcc = self.find(*xc);
          cache.entry(xcc).or_default().push(*xc);
        }
      }
      seen.clear();
    }
    cache
  }

  fn reserve_new_cache(&mut self) -> bool {
    if self.has_cache() {
      return true;
    }
    let success = if self.source.max_ematching_caches > 0 {
      if self.source.eclasses_by_version.len() >= self.source.max_ematching_caches {
        // Random Version
        // let v = *self.source.eclasses_by_version.iter().next().unwrap().0;
        // self.source.eclasses_by_version.remove(&v);

        // Latest Version
        let v = *self.source.eclasses_by_version.keys().max().unwrap();
        self.source.eclasses_by_version.remove(&v);
      }
      true
    } else {
      false
    };
    success
  }

  fn init_ematching_cache(&mut self) {
    if self.reserve_new_cache() {
      let cache = self.new_ematching_cache();
      self.source.eclasses_by_version.insert(self.version, cache);
    }
  }

  fn inherit_ematching_cache(&mut self) {
    if self.reserve_new_cache() {
      let parent = self.source.versioning().superversion(self.version);
      let cache = match self.source.eclasses_by_version.get(&parent) {
        Some(inherit) => inherit.clone(),
        None => self.new_ematching_cache(),
      };
      self.source.eclasses_by_version.insert(self.version, cache);
    }
  }

  fn rebuild_ematching_cache(&mut self) {
    // Restore the cache of equivalent canonicalized enodes, sorted by operator
    if let Some(mut eclasses) = self.source.eclasses_by_version.remove(&self.version) {
      let mut seen = Set::default(); // TODO is there a better way to deduplicate?
      for (&_xc, xns) in eclasses.iter_mut() {
        for xnc in xns.iter_mut() {
          self.rebuild_ematching_entry(xnc);
        }
        xns.sort_unstable_by_key(|c| self.source.unionfind.project(VersionTree::ROOT_VERSION).get_element(*c).op);
        xns.retain(|c| seen.insert(*c));
        seen.clear();
      }
      self.source.eclasses_by_version.insert(self.version, eclasses);
    }
  }

  fn rebuild_ematching_entry(&mut self, xnc: &mut EClass) {
    let xn = &self.source.unionfind.universe[Into::<usize>::into(*xnc)];
    let xn0 = self.canonicalize(xn.clone());
    *xnc = *self.get_class(&xn0).unwrap();
  }
}

impl<S> MachineRequirements for Projection<S> where S: Deref<Target = VersionedEGraph> {
  fn canonicals(&self) -> impl std::iter::Iterator<Item = &Id> {
    self.source
      .eclasses_by_version
      .get(&self.version)
      .expect("max ematching caches to be greater than 0")
      .keys()
  }

  fn for_each_matching_node<Err>(
    &self,
    eclass: EClass,
    enode: &ENode,
    mut f: impl FnMut(&ENode) -> Result<(), Err>,
  ) -> Result<(), Err> {
    let classes = &self.source.eclasses_by_version[&self.version][&eclass];
    if classes.len() < 50 {
      classes
        .iter()
        .map(|c| &self.source.unionfind.universe[Into::<usize>::into(*c)])
        .filter(|n| egg::Language::matches(enode, n))
        .try_for_each(f)
    } else {
      let start = classes.partition_point(|c| self.source.unionfind.universe[Into::<usize>::into(*c)].op < enode.op);
      classes[start..]
        .iter()
        .map(|c| &self.source.unionfind.universe[Into::<usize>::into(*c)])
        .take_while(|&n| n.op == enode.op)
        .filter(|n| n.args.len() == enode.args.len())
        .try_for_each(&mut f)
    }
  }
}


impl<S> Projection<S> where S: DerefMut<Target = VersionedEGraph> {

  pub fn run(&mut self, config: &RunnerConfig, rules: &[(String, Pattern<ENode>, Pattern<ENode>)]) -> Option<StopReason> {
     fn check_time(
      result: &mut Result<(), StopReason>,
      start_time: Instant,
      config: &RunnerConfig,
    ) {
      if let Some(timeout) = config.timeout {
        let elapsed = start_time.elapsed();
        if elapsed > timeout {
          *result = Err(StopReason::TimeLimit(elapsed.as_secs_f64()));
        }
      }
    }
    fn check_nodes<S: Deref<Target=VersionedEGraph>>(
      result: &mut Result<(), StopReason>,
      egraph: &Projection<S>,
      config: &RunnerConfig,
    ) {
      if let Some(node_limit) = config.node_limit {
        let size = egraph.universe().count();
        if size > node_limit {
          *result = Err(StopReason::NodeLimit(size));
        }
      }
    }
    fn check_iters(
      result: &mut Result<(), StopReason>,
      iterations: usize,
      config: &RunnerConfig,
    ) {
      if let Some(iter_limit) = config.iter_limit {
        if iterations > iter_limit {
          *result = Err(StopReason::IterationLimit(iterations));
        }
      }
    }
  
    let rules = rules.iter().collect::<Vec<_>>();
    let mut iterations: usize = 0;
    let mut result: Result<(), StopReason> = Ok(());
    let start_time: Instant = Instant::now();
    loop {
      self.rebuild();
  
      if result.is_ok() {
        check_time(&mut result, start_time, config);
        check_nodes(&mut result, self, config);
        check_iters(&mut result, iterations, config);
      }
      if let Err(stop_reason) = result {
        return Some(stop_reason);
      }
  
      let mut matches: Vec<Vec<SearchMatches<ENode>>> = Vec::new();
      for (_, lhs, _) in rules.iter() {
        matches.push(self.search_pattern(lhs));
        check_time(&mut result, start_time, config);
        if let Err(timeout) = result {
          return Some(timeout);
        }
      }
  
      let mut applications: HashMap<&String, usize> = HashMap::new();
      for ((name, _, rhs), matched) in rules.iter().zip(matches) {
        let new_applications = self.apply_matches(rhs, &matched).len();
        if new_applications > 0 {
          *applications.entry(name).or_default() += new_applications;
        }
        check_time(&mut result, start_time, config);
        if let Err(timeout) = result {
          return Some(timeout);
        }
      }
  
      if applications.is_empty() {
        result = Err(StopReason::Saturated)
      }
      iterations += 1;
    }
  }
  
  fn write_pattern(
    &mut self,
    applier: &Pattern<ENode>,
    eclass: Id,
    subst: &Subst,
  ) -> Vec<Id> {
    let mut result =
      CanBind::bind(applier, self, eclass, &subst)
        .into_iter()
        .collect::<Vec<_>>();
    if result.is_empty() {
      result.push(eclass);
    }
    result
  }

  fn apply_matches(&mut self, rhs: &Pattern<ENode>, matches: &[SearchMatches<ENode>]) -> Vec<Id> {
    let mut added = vec![];
    for mat in matches {
      for subst in &mat.substs {
        let ids = self.write_pattern(rhs, mat.eclass, subst)
          .into_iter()
          .filter_map(|id| {
            if id != mat.eclass {
              Some(self.union(id, mat.eclass))
            } else {
              None
            }
          });
        added.extend(ids)
      }
    }
    added
  }

}


impl<S> Projection<S> where S: Deref<Target = VersionedEGraph> {
  fn search_pattern<'a>(&self, searcher: &'a Pattern<ENode>) -> Vec<SearchMatches<'a, ENode>> {
    CanEMatch::ematch(searcher, self)
  }
}
