use std::collections::{BTreeMap, BTreeSet};

use crate::lang::ast::{Id, VarId, IdentId, TheoremId};
use crate::lang::ast::{Expr, Pattern};
use crate::lang::ctx::{Ctx, TypeInfo};
use crate::lang::ematch::{Bindings,SearchPattern};

pub type Version = usize;

pub const ROOT_VERSION: Version = 0;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct ENodeId(pub usize);

impl Id for ENodeId {
  fn as_usize(&self) -> usize { self.0 }
  fn from(n: usize) -> Self { Self(n) }
}



pub struct HashCons<T: Ord + Clone, I: Id> {
  memo: BTreeMap<T, I>,
  values: Vec<T>,
}

impl<T: Ord + Clone, I: Id + Clone + Copy> HashCons<T,I> {
  fn new() -> Self {//{{{
    HashCons { memo: BTreeMap::new(), values: vec![] }
  }//}}}

  fn add(&mut self, t: T) -> I {//{{{
    if let Some(id) = self.memo.get(&t) {
      *id
    } else {
      let id = self.memo.len();
      self.memo.insert(t.clone(), Id::from(id));
      self.values.push(t.clone());
      Id::from(id)
    }
  }//}}}

  pub fn get(&self, id: &I) -> &T {//{{{
    &self.values[Id::as_usize(id)]
  }//}}}

  fn contains(&self, t: &T) -> bool {//{{{
    self.memo.contains_key(t)
  }//}}}
}


#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Debug)]
pub enum ENode {
  Var(VarId),
  App(IdentId, Vec<ENodeId>),
  Case(ENodeId, Vec<(Pattern, Expr)>),
}

pub struct VTree {
  pub parent: Vec<Version>,
  pub children: Vec<Vec<Version>>,
}

impl VTree {

  fn new() -> Self {//{{{
    Self { parent: vec![ ROOT_VERSION ], children: vec![ vec![] ] }
  }//}}}

  fn fork(&mut self, v: Version) -> Version {//{{{
    let new = self.parent.len();
    self.parent.push(v);
    self.children.push(vec![]);
    self.children[v].push(new);
    return new;
  }//}}}

  pub fn all_between(&self, v0: Version, mut v1: Version) -> Vec<Version> {//{{{
    let mut result = vec![];
    loop {
      result.push(v1);
      if v1 == v0 { result.reverse(); return result; }
      if v1 == ROOT_VERSION { panic!(); }
      v1 = self.parent[v1];
    }
  }//}}}

  pub fn all_versions(&self) -> impl Iterator<Item=Version> {{{
    0 .. self.parent.len()
  }}}

  pub fn all_descendents(&self, v: Version) -> Vec<Version> {{{
    let mut result = vec![ v ];
    for v in &self.children[v] {
      result.append(&mut self.all_descendents(*v));
    }
    result
  }}}

  pub fn is_ancestor(&self, earlier: Version, later: Version) -> bool {{{
    if earlier == later { return true; }
    if later == ROOT_VERSION { return false; }
    if earlier == self.parent[later] { return true; }
    self.is_ancestor(earlier, self.parent[later])
  }}}

  pub fn dump(&self) {{{
    for v in self.all_versions() {
      println!("{v}: {:?}", self.children[v]);
    }
  }}}

  pub fn len(&self) -> usize {{{
    return self.parent.len()
  }}}

}


pub struct VUF {
  parent: Vec<BTreeMap<ENodeId, ENodeId>>,
  pub tree: VTree,
}

impl VUF {

  fn new() -> Self {//{{{
    Self { parent: vec![ BTreeMap::new() ], tree: VTree::new() }
  }//}}}

  fn fork(&mut self, v: Version) -> Version {//{{{
    let v = self.tree.fork(v);
    self.parent.push(BTreeMap::new());
    return v;
  }//}}}

  fn add(&mut self, e: ENodeId) {//{{{
    self.parent[ROOT_VERSION].entry(e).or_insert(e);
  }//}}}

  fn closest_valid_parent(&self, e: ENodeId, v: Version) -> ENodeId {//{{{
    if v == ROOT_VERSION {
      *self.parent[v].get(&e).unwrap()
    } else {
      self.parent[v].get(&e).copied().unwrap_or_else(|| self.closest_valid_parent(e, self.tree.parent[v]))
    }
  }//}}}

  fn find(&mut self, e: ENodeId, v: Version) -> ENodeId {//{{{
    let parent = self.closest_valid_parent(e, v);
    let root = if parent != e { self.find(parent, v) } else { parent };
    self.parent[v].insert(e, root);
    return root
  }//}}}

  fn query(&self, e: ENodeId, v: Version) -> ENodeId {//{{{
    let parent = self.closest_valid_parent(e, v);
    if parent != e { self.query(parent, v) } else { parent }
  }//}}}

  fn union(&mut self, e1: ENodeId, e2: ENodeId, v: Version) -> ENodeId {//{{{
    let e1 = self.find(e1, v);
    let e2 = self.find(e2, v);
    for i in 0 .. self.tree.children[v].len() {
      self.union(e1, e2, self.tree.children[v][i]);
    }
    self.parent[v].insert(e1, e2);
    return e2;
  }//}}}

}



#[derive(Ord,PartialOrd,Eq,PartialEq,Clone,Debug)]
pub enum ProofEdge {
  Rewrite(TheoremId, bool, BTreeMap<u8, ENodeId>),
  Congr(Vec<(ENodeId,ENodeId)>),

  // Constructors Datatypes
  Injective(u8, ENodeId, ENodeId),
  Absurd(ENodeId, ENodeId),

  // Case Analysis
  Hyp(IdentId, bool),
  CaseSimpl(usize, bool),

  // "Good Software Engineering"
  Definition(IdentId, bool),
}

impl ProofEdge {
  pub fn inverse(&self) -> ProofEdge {//{{{
    use ProofEdge::*;
    match self {
      Definition(ident, b) => Definition(*ident, !b),
      Rewrite(t, b, es) => Rewrite(*t, !b, es.clone()),
      Congr(args) => Congr(args.clone()),
      Injective(n, a, b) => Injective(*n, *b, *a),
      Absurd(a, b) => Absurd(*b, *a),
      Hyp(h, c) => Hyp(*h, !c),
      CaseSimpl(n, b) => CaseSimpl(*n, !b),
    }
  }//}}}
}


pub struct VEGraph {
  pub hashcons: HashCons<ENode, ENodeId>,
  pub vuf: VUF,
  parents: Vec<Vec<ENodeId>>,

  pub enodes_per_versions: Vec<BTreeSet<ENodeId>>,
  pub enodes_per_eclass: Vec<BTreeMap<ENodeId, Vec<ENodeId>>>,

  pub var_enodes: Vec<BTreeMap<ENodeId, Vec<ENodeId>>>,
  pub app_enodes: Vec<BTreeMap<ENodeId, BTreeMap<IdentId, Vec<ENodeId>>>>,
  pub case_enodes: Vec<BTreeMap<ENodeId, Vec<ENodeId>>>,

  pub proof_graph: BTreeMap<ENodeId, BTreeSet<(Version, ProofEdge, ENodeId)>>,
  pub version_hyp: Vec<IdentId>,
  pub hyp_eq: BTreeMap<IdentId, (ENodeId, ENodeId)>,
}

impl VEGraph {
  pub fn new() -> Self {//{{{
    Self {
      vuf: VUF::new(),
      hashcons: HashCons::new(),
      parents: vec![],

      enodes_per_versions: vec![ BTreeSet::new() ],

      var_enodes: vec![ BTreeMap::new() ],
      app_enodes: vec![ BTreeMap::new() ],
      case_enodes: vec![ BTreeMap::new() ],

      enodes_per_eclass: vec![ BTreeMap::new() ],

      proof_graph: BTreeMap::new(),
      version_hyp: vec![ IdentId(0) ], // will never be called at ROOT_VERSION
      hyp_eq: BTreeMap::new(),
    }
  }//}}}

  fn canonicalize(&mut self, e: ENode, v: Version) -> ENode {//{{{
    match e {
      ENode::Var(_) => e.clone(),
      ENode::App(f, args) => ENode::App(f, args.into_iter().map(|a| self.find(a, v)).collect()),
      ENode::Case(scrutinee, arms) => {
        let scrutinee = self.find(scrutinee, v);
        ENode::Case(scrutinee, arms.clone())
      }
    }
  }//}}}

  pub fn add_enode(&mut self, enode: ENode, v: Version) -> ENodeId {//{{{
    for vc in self.vuf.tree.children[v].clone() {
      self.add_enode(enode.clone(), vc);
    }
    let id = if self.hashcons.contains(&enode) {
      self.hashcons.add(enode.clone())
    } else {
      let id = self.hashcons.add(enode.clone());
      self.vuf.add(id);
      self.parents.push(vec![]);
      id
    };
    if !self.enodes_per_versions[v].contains(&id) {
      self.enodes_per_eclass[v].insert(id, vec![]);
      self.var_enodes[v].entry(id).or_insert(vec![]);
      self.app_enodes[v].entry(id).or_insert(BTreeMap::new());
      self.case_enodes[v].entry(id).or_insert(vec![]);
      match &enode {
        ENode::Var(_) => {
          self.var_enodes[v].get_mut(&id).unwrap().push(id);
        }
        ENode::App(f, args) => {
          for a in args { self.parents[Id::as_usize(a)].push(id); }
          self.app_enodes[v].get_mut(&id).unwrap().entry(*f).or_insert(vec![]).push(id);
        }
        ENode::Case(scrutinee, _) => {
          self.parents[Id::as_usize(scrutinee)].push(id);
          self.case_enodes[v].get_mut(&id).unwrap().push(id);
        }
      }
    }
    self.proof_graph.entry(id).or_insert(BTreeSet::new());
    self.enodes_per_versions[v].insert(id);
    let class = self.find(id, v);
    if let Some(enodes) = self.enodes_per_eclass[v].get_mut(&class) {
      enodes.push(id);
    } else {
      self.enodes_per_eclass[v].insert(class, vec![ id ]);
    }
    let canon = self.canonicalize(enode.clone(), v);
    if canon != enode {
      let congr_args = match (enode, &canon) {
        (ENode::App(_,args1), ENode::App(_,args2)) =>
          args1.iter().zip(args2).map(|(a,b)|(*a,*b)).collect(),
        (ENode::Case(e1,_), ENode::Case(e2,_)) =>
          vec![ (e1,*e2) ],
        _ => vec![]
      };
      let canon_id = self.add_enode(canon, v);
      self.union(id, canon_id, v, ProofEdge::Congr(congr_args));
    }
    id
  }//}}}

  pub fn add_expr(&mut self, e: &Expr, v: Version) -> ENodeId {//{{{
    let enode = match e {
      Expr::Var(v) => ENode::Var(*v),
      Expr::Cons(k, args) => ENode::App(*k, args.iter().map(|a| self.add_expr(a, v)).collect()),
      Expr::App(f, args) => ENode::App(*f, args.iter().map(|a| self.add_expr(a, v)).collect()),
      Expr::Case(scrutinee, arms) => {
        let scrut_id = self.add_expr(scrutinee, v);
        ENode::Case(scrut_id, arms.clone())
      },
    };
    let id = self.add_enode(enode, v);
    return id;
  }//}}}

  pub fn find(&mut self, e: ENodeId, v: Version) -> ENodeId {//{{{
    let id = self.vuf.find(e, v);
    assert!(self.enodes_per_versions[v].contains(&id));
    return id;
  }//}}}

  pub fn union(&mut self, e1: ENodeId, e2: ENodeId, v: Version, proof: ProofEdge) -> ENodeId {//{{{
    if e1 != e2 {
      self.proof_graph.get_mut(&e1).unwrap().insert((v, proof.clone(), e2));
      self.proof_graph.get_mut(&e2).unwrap().insert((v, proof.inverse(), e1));
    }

    let e1p = self.find(e1, v);
    let e2p = self.find(e2, v);

    let (parent, child) = if e1.as_usize() <= e2.as_usize() { (e1p, e2p) } else { (e2p, e1p) };
    if parent == child { return e1; }

    if let Some(other) = self.enodes_per_eclass[v].remove(&child) {
      self.enodes_per_eclass[v].get_mut(&parent).unwrap().extend(other);
    }
    if let Some(other) = self.var_enodes[v].remove(&child) {
      self.var_enodes[v].get_mut(&parent).unwrap().extend(other);
    }
    if let Some(other) = self.app_enodes[v].remove(&child) {
      for (f, enodes) in other {
        self.app_enodes[v].get_mut(&parent).unwrap().entry(f).or_insert(vec![]).extend(enodes);
      }
    }
    if let Some(other) = self.case_enodes[v].remove(&child) {
      self.case_enodes[v].get_mut(&parent).unwrap().extend(other);
    }

    for vc in 0 .. self.vuf.tree.children[v].len() {
      self.union(e1, e2, self.vuf.tree.children[v][vc], proof.clone());
    }

    self.vuf.union(child, parent, v);

    for parent in 0 .. self.parents[Id::as_usize(&child)].len() {
      let parent = self.parents[Id::as_usize(&child)][parent];
      if !self.enodes_per_versions[v].contains(&parent) { continue; }
      let parent_enode = self.hashcons.get(&parent).clone();
      self.add_enode(parent_enode, v); // NOTE add_note recanonicalizes
      // let canonical_parent = self.canonicalize(parent_enode, v);
      // let canonical_parent = self.add_enode(canonical_parent, v);
      // self.union(canonical_parent, parent, v, ProofEdge::Congr(...));
    }

    return parent
  }//}}}

  pub fn fork(&mut self, v: Version, hyp: IdentId) -> Version {//{{{
    let vc = self.vuf.fork(v);
    self.enodes_per_versions.push(self.enodes_per_versions[v].clone());
    self.var_enodes.push(self.var_enodes[v].clone());
    self.app_enodes.push(self.app_enodes[v].clone());
    self.case_enodes.push(self.case_enodes[v].clone());
    self.enodes_per_eclass.push(self.enodes_per_eclass[v].clone());
    self.version_hyp.push(hyp);
    return vc;
  }//}}}

  pub fn query(&self, id: ENodeId, v: Version) -> ENodeId {//{{{
    self.vuf.query(id, v)
  }//}}}

  pub fn dump(&self, ctx: &Ctx) -> String {//{{{
    let mut ans = String::new();
    for v in 0 .. self.vuf.tree.parent.len() {
      ans.push_str(&format!("Version {v}, parent: {}\n", self.vuf.tree.parent[v]));
      for (eclass, enodes) in &self.enodes_per_eclass[v] {
        ans.push_str(&format!("  E-Class {}:\n", Id::as_usize(eclass)));
        for enode in enodes.iter().collect::<BTreeSet<_>>() {
          if let ENode::Case(s, _) = self.hashcons.get(enode) {
            if self.query(*s, v) != *s { continue }
          }
          ans.push_str(&format!("    {enode:?}: {}\n", self.dump_enode(ctx, *enode)))
        }
      }
      ans.push('\n');
    }
    ans
  }//}}}

  pub fn dump_enode(&self, ctx: &Ctx, enode: ENodeId) -> String {//{{{
    let enode = self.hashcons.get(&enode);
    match enode {
      ENode::Var(x) => format!("{}", ctx.vars.as_str(x)),
      ENode::App(f, args) => {
        let mut ans = format!("({}", ctx.idents.as_str(f));
        for a in args {
          ans.push(' ');
          ans.push_str(&self.dump_enode(ctx, *a));
        }
        ans.push(')');
        ans
      }
      ENode::Case(scrutinee, arms) => {
        let mut ans = format!("(case {}", self.dump_enode(ctx, *scrutinee));
        for (pat, expr) in arms {
          ans.push_str(" (");
          ans.push_str(&pat.to_string(ctx));
          ans.push(' ');
          ans.push_str(&expr.to_string(ctx));
          ans.push(')');
        }
        ans.push(')');
        ans
      }
    }
  }//}}}

  pub fn set_hyp_eq(&mut self, hyp: IdentId, e1: ENodeId, e2: ENodeId) {//{{{
    self.hyp_eq.insert(hyp, (e1, e2));
  }//}}}
}



#[test]
fn vuf() {//{{{
  let mut vuf = VUF::new();

  vuf.add(ENodeId(1));
  vuf.add(ENodeId(2));
  vuf.add(ENodeId(3));
  vuf.add(ENodeId(4));

  vuf.union(ENodeId(1), ENodeId(2), ROOT_VERSION);
  assert_eq!(vuf.find(ENodeId(1), ROOT_VERSION), vuf.find(ENodeId(2), ROOT_VERSION));
  assert!(vuf.find(ENodeId(1), ROOT_VERSION) != vuf.find(ENodeId(3), ROOT_VERSION));

  let v1 = vuf.fork(ROOT_VERSION);
  assert_eq!(vuf.find(ENodeId(1), ROOT_VERSION), vuf.find(ENodeId(2), v1));
  assert!(vuf.find(ENodeId(1), ROOT_VERSION) != vuf.find(ENodeId(3), v1));

  vuf.union(ENodeId(1), ENodeId(3), v1);
  assert_eq!(vuf.find(ENodeId(2), v1), vuf.find(ENodeId(3), v1));
  assert!(vuf.find(ENodeId(2), ROOT_VERSION) != vuf.find(ENodeId(3), ROOT_VERSION));

  let v2 = vuf.fork(ROOT_VERSION);

  vuf.union(ENodeId(3), ENodeId(4), ROOT_VERSION);
  assert_eq!(vuf.find(ENodeId(1), v1), vuf.find(ENodeId(4), v1));
  assert_eq!(vuf.find(ENodeId(3), ROOT_VERSION), vuf.find(ENodeId(4), ROOT_VERSION));
  assert!(vuf.find(ENodeId(2), ROOT_VERSION) != vuf.find(ENodeId(4), ROOT_VERSION));

  vuf.add(ENodeId(5));
  vuf.add(ENodeId(6));
  vuf.union(ENodeId(5), ENodeId(6), v2);
  assert_eq!(vuf.find(ENodeId(5), v2), vuf.find(ENodeId(6), v2));
  assert!(vuf.find(ENodeId(5), v1) != vuf.find(ENodeId(6), v1));
  assert!(vuf.find(ENodeId(5), ROOT_VERSION) != vuf.find(ENodeId(6), ROOT_VERSION));
}//}}}


#[test]
fn vegraph() {//{{{
  let mut veg = VEGraph::new();

  let id0 = veg.add_expr(&Expr::Var(Id::from(0)), ROOT_VERSION);
  let id1 = veg.add_expr(&Expr::Var(Id::from(1)), ROOT_VERSION);
  let id2 = veg.add_expr(&Expr::Var(Id::from(2)), ROOT_VERSION);

  assert!(veg.find(id0, ROOT_VERSION) != veg.find(id1, ROOT_VERSION));
  veg.union(id0, id1, ROOT_VERSION);
  assert_eq!(veg.find(id0, ROOT_VERSION), veg.find(id1, ROOT_VERSION));
  assert!(veg.find(id2, ROOT_VERSION) != veg.find(id1, ROOT_VERSION));

  let v1 = veg.fork(ROOT_VERSION);
  assert_eq!(veg.find(id0, v1), veg.find(id1, v1));
  assert!(veg.find(id2, v1) != veg.find(id1, v1));

  let id3 = veg.add_expr(&Expr::Cons(Id::from(0), vec![ Expr::Var(Id::from(0)) ]), v1);
  let id4 = veg.add_expr(&Expr::Cons(Id::from(0), vec![ Expr::Var(Id::from(1)) ]), v1);

  assert_eq!(veg.find(id3, v1), veg.find(id4, v1));
  assert_eq!(veg.find(id3, ROOT_VERSION), veg.find(id4, ROOT_VERSION));

  let id5 = veg.union(id2, id1, v1);
  assert_eq!(veg.find(id2, v1), veg.find(id0, v1));
  assert!(veg.find(id2, ROOT_VERSION) != veg.find(id0, ROOT_VERSION));

  let v2 = veg.fork(ROOT_VERSION);

  let id0 = veg.add_expr(&Expr::App(Id::from(0), vec![ Expr::Var(Id::from(10)) ]), v2);
  let id1 = veg.add_expr(&Expr::App(Id::from(0), vec![ Expr::Var(Id::from(11)) ]), v2);
  let id2 = veg.add_expr(&Expr::Var(Id::from(10)), v2);
  let id3 = veg.add_expr(&Expr::Var(Id::from(11)), v2);

  veg.union(id2, id3, v2);
  assert_eq!(veg.find(id0, v2), veg.find(id1, v2));
  assert!(veg.find(id0, ROOT_VERSION) != veg.find(id1, ROOT_VERSION));

  let v3 = veg.fork(v2);
  veg.union(id0, id2, v3);
  assert_eq!(veg.find(id1, v3), veg.find(id3, v3));
  assert!(veg.find(id1, v1) != veg.find(id3, v1));
}//}}}




#[derive(Debug)]
pub enum StructuralOrd {
  UNKNOWN, EQ, LE
}

impl VEGraph {

  pub fn all_eclasses(&self, v: Version) -> Vec<ENodeId> {//{{{
    self.enodes_per_eclass[v].keys().copied().collect()
  }//}}}

  pub fn add_pattern(&mut self, pat: &SearchPattern, bindings: &Bindings, v: Version) -> ENodeId {//{{{
    match pat {
      SearchPattern::MetaVar(i) => bindings[i],
      SearchPattern::App(f, args) => {
        let enode = ENode::App(*f, args.iter().map(|a| self.add_pattern(a, bindings, v)).collect::<_>());
        self.add_enode(enode, v)
      }
    }
  }//}}}

  pub fn structurally_less(&self, type_info: &BTreeMap<IdentId, TypeInfo>, big: ENodeId, small: ENodeId, v: Version) -> StructuralOrd {//{{{

    fn aux(g: &VEGraph, seen: &mut BTreeSet<ENodeId>, type_info: &BTreeMap<IdentId, TypeInfo>, big: ENodeId, small: ENodeId, v: Version) -> StructuralOrd {

      use StructuralOrd::*;
      let big = g.query(big, v);
      let small = g.query(small, v);

      if seen.contains(&big) { return UNKNOWN }
      seen.insert(big);

      if big == small { return EQ }

      // TODO BUG! enodes_per_eclass contains an enode that app_enodes does not!
      for enode in &g.enodes_per_eclass[v][&g.query(big, v)] {
        let ENode::App(func, args) = g.hashcons.get(enode) else { continue };
        if type_info.get(func).map(|tinfo| !tinfo.constructor).unwrap_or(true) { continue }

        for arg in args {
          if let EQ | LE = aux(g, seen, type_info, *arg, small, v) {
            return LE;
          }
        }

        break;
      }

      return UNKNOWN;
    }

    aux(self, &mut BTreeSet::new(), type_info, big, small, v)
  }//}}}

  pub fn extract(&self, enode: ENodeId) -> Expr {//{{{
    match self.hashcons.get(&enode) {
      ENode::Var(v) => Expr::Var(*v),
      ENode::Case(e, arms) => Expr::Case(Box::new(self.extract(*e)), arms.clone()),
      ENode::App(f, args) => Expr::App(*f, args.iter().map(|a| self.extract(*a)).collect()),
    }
  }//}}}

  pub fn equal(&self, e0: ENodeId, e1: ENodeId, v: Version) -> bool {//{{{
    self.query(e0, v) == self.query(e1, v) || self.vuf.tree.children[v].iter().all(|v| self.equal(e0, e1, *v))
  }//}}}

}

impl ENode {
  pub fn to_string(&self, ctx: &Ctx) -> String {{{
    match self {
      ENode::Var(var) => ctx.vars.as_str(var).to_string(),
      ENode::App(f, args) =>
        format!("{}{}{}{}",
          if args.len() > 0 { "(" } else { "" },
          ctx.idents.as_str(f).to_string(),
          args.iter().map(|a| format!(" {}", a.0)).collect::<Vec<String>>().join(""),
          if args.len() > 0 { ")" } else { "" },
        ),
      ENode::Case(_, _) => "(case - -)".to_string(),
    }
  }}}
}

impl VEGraph {

  pub fn visualise_proof_graph(&self, id: usize, ctx: &Ctx, source: ENodeId, lhs: &ENodeId, rhs: &ENodeId) -> String {{{
    // let costs = self.with_costs(ROOT_VERSION);
    let mut result = format!("digraph G_{id} {{ ranksep=1.5; nodesep=1.5; edge [minlen=2]; node [shape=rectangle]; ");
    for (eid, edges) in &self.proof_graph {
      result = format!("{result}\nn{} [label=\"n{}: {}\"{}];",
        eid.0, eid.0, self.extract(*eid).to_string(ctx),
        if eid == lhs || eid == rhs {
          ",style=filled,fillcolor=lightblue"
        } else { "" }
        );
    }
    for (source, edges) in &self.proof_graph {
      for (v, step, target) in edges {
        use ProofEdge::*;
        if let Definition(_,false) | Rewrite(_,false,_) | Hyp(_,false) | CaseSimpl(_,false) = step { continue }
        // let cost = costs.get(&(*source, step.clone(), *target));
        result = format!("{result}\nn{} -> n{} [label=\"{} @ v{v}\"];", source.0, target.0, step.to_string(ctx));
      }
    }
    format!("{result} }}")
  }}}

}
