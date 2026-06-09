use std::collections::{BTreeSet, BTreeMap};

use crate::lang::ast::{TheoremId, TypeId, VarId, IdentId};
use crate::lang::ast::{Constructor, Pattern, Expr};
use crate::lang::ctx::{Ctx};
use crate::lang::myegraph::{ROOT_VERSION, Version, VEGraph, ENodeId, ENode, StructuralOrd, ProofEdge};
use crate::lang::ematch::{SearchPattern};

pub struct Prover<'a> {
  theorem: TheoremId,
  arg_eclasses: Vec<ENodeId>,
  leaf_versions: BTreeSet<Version>,
  pub egraph: VEGraph,
  pub ctx: &'a mut Ctx,
  pub lhs: ENodeId,
  pub rhs: ENodeId,
  proven_true: bool,
  proven_false: bool,
  rules: Vec<(TheoremId, bool, SearchPattern, SearchPattern)>,

  mark_expanded: Vec<BTreeSet<ENodeId>>,
  expansion_quota: Vec<BTreeMap<IdentId, usize>>,
  case_vars: Vec<Vec<(VarId, TypeId)>>,

  hyp_counter: usize,
}

impl Prover<'_> {

  pub fn from<'a>(ctx: &'a mut Ctx, theorem: TheoremId) -> Prover<'a> {
    let mut egraph = VEGraph::new();
    let (theorem_args, lhs_expr, rhs_expr) = &ctx.theorem_stmts[&theorem];
    let lhs = egraph.add_expr(&lhs_expr, ROOT_VERSION);
    let rhs = egraph.add_expr(&rhs_expr, ROOT_VERSION);
    let arg_eclasses = theorem_args.iter().map(|a|
      egraph.add_expr(&Expr::Var(*a), ROOT_VERSION)).collect::<Vec<_>>();
    let expansion_quota = vec![
      lhs_expr.get_idents().union(&rhs_expr.get_idents()).map(|f| (*f, 4)).collect()
    ];
    let case_vars = vec![ theorem_args.iter().enumerate().filter(|(i,_)| *i < 2).map(|(_,v)| (*v, ctx.var_types[v])).rev().collect() ];

    let mut rules = vec![];
    for (lemma_id, (args, lhs, rhs)) in &ctx.theorem_stmts {
      // first cond allows for induction
      if *lemma_id != theorem && !ctx.proven_theorem.contains(lemma_id) { continue; }
      let Some(lhs_pat) = SearchPattern::from_expr_with_args(lhs, args) else { continue };
      let Some(rhs_pat) = SearchPattern::from_expr_with_args(rhs, args) else { continue };
      let lhs_fv = lhs_pat.get_fvs();
      let rhs_fv = rhs_pat.get_fvs();
      if let Expr::Var(_) = lhs {} else {
        if lhs_fv.is_superset(&rhs_fv) {
          rules.push((*lemma_id, true, lhs_pat.clone(), rhs_pat.clone()));
        }
      }
      if let Expr::Var(_) = rhs {} else {
        if rhs_fv.is_superset(&lhs_fv) {
          rules.push((*lemma_id, false, rhs_pat.clone(), lhs_pat.clone()));
        }
      }
    }

    Prover {
      theorem,
      arg_eclasses,
      ctx,
      leaf_versions: BTreeSet::from([ ROOT_VERSION ]),
      egraph,
      lhs,
      rhs,
      proven_true: false,
      proven_false: false,
      rules,
      mark_expanded: vec![ BTreeSet::new() ],
      expansion_quota,
      case_vars,
      hyp_counter: 0,
    }
  }

  pub fn proof_iter(&mut self) {
    if self.is_done() { return; }
    // let leaves = self.leaf_versions.iter().copied().collect::<Vec<_>>();
    for v in 0 .. self.egraph.vuf.tree.parent.len() { // TODO should this be leaves?
      // println!("> expand_defs");
      self.expand_defs(v);
      for _ in 0 .. 2 {
        // println!("> constructors_non_overlap");
        self.constructors_non_overlap(v);
        // println!("> constructors_injectivite");
        self.constructors_injectivite(v);
        if self.is_done() { return; }
        // println!("> apply_theorems");
        self.apply_theorems(v);
        if self.is_done() { return; }
      }
      if self.is_done() { return; }
      // println!("> case simpl");
      self.case_simpl(v);
      if self.is_done() { return; }
      // println!("> case_analysis");
      self.case_analysis(v);
    }
  }

  pub fn is_true(&mut self) -> bool {//{{{
    if self.proven_true { return true; }
    let mut children = vec![ ROOT_VERSION ];
    loop {
      let mut new_children = vec![];
      for v in children {
        if self.egraph.find(self.lhs,v) == self.egraph.find(self.rhs,v) {
        } else if self.egraph.vuf.tree.children[v].len() == 0 {
          return false;
        } else {
          new_children.extend(self.egraph.vuf.tree.children[v].clone());
        }
      }
      children = new_children;
      if children.len() == 0 { self.proven_true = true; return true; }
    }
  }//}}}

  pub fn is_false(&mut self) -> bool {//{{{
    if self.proven_false { return true; }
    return false;
  }//}}}

  pub fn is_done(&mut self) -> bool {//{{{
    self.is_true() || self.is_false()
  }//}}}

  pub fn fork(&mut self, v: Version, hyp: IdentId) -> Version {//{{{
    let vc = self.egraph.fork(v, hyp);
    self.leaf_versions.insert(vc);
    self.mark_expanded.push(self.mark_expanded[v].clone());
    self.expansion_quota.push(self.expansion_quota[v].clone());
    self.case_vars.push(self.case_vars[v].clone());
    vc
  }//}}}

  pub fn remove_version(&mut self, v: Version) {//{{{
    self.leaf_versions.remove(&v);
  }//}}}

  fn fresh_hyp(&mut self) -> IdentId {//{{{
    let id = self.ctx.idents.get(&format!("_h{}", self.hyp_counter));
    self.hyp_counter += 1;
    return id
  }//}}}

  pub fn explain(&mut self) -> String {
    self.egraph.explain(self.lhs, self.rhs, ROOT_VERSION).to_string(&self.egraph, &self.ctx, 0)
  }

}

impl Prover<'_> {

  fn expand_defs(&mut self, v: Version) {//{{{
    if v != ROOT_VERSION { return; }
    'func: for (f_id, (f_args, body)) in &self.ctx.defs {
      if !self.expansion_quota[v].contains_key(&f_id) { continue; }
      let mut new_terms: Vec<(IdentId, ENodeId, Expr)> = vec![];
      for eclass in self.egraph.all_eclasses(v) {
        for eid in self.egraph.app_enodes[v][&eclass].get(f_id).unwrap_or(&vec![]) {
          if self.mark_expanded[v].contains(&eid) { continue };
          let ENode::App(_, args) = self.egraph.hashcons.get(&eid) else { continue };
          let Some(quota) = self.expansion_quota[v].get_mut(f_id) else { continue };
          if *quota == 0 { continue; }
          *quota -= 1;
          self.mark_expanded[v].insert(*eid);
          let s = f_args.iter().zip(args).map(|(v,a)| (*v, self.egraph.extract(*a))).collect();
          // println!("Expanded {}", self.ctx.idents.as_str(f_id));
          new_terms.push((*f_id, eclass, body.subst(&s)));
        }
      }
      for (f_id, eclass, term) in new_terms {
        let rhs = self.egraph.add_expr(&term, v);
        self.egraph.union(eclass, rhs, v, ProofEdge::Definition(f_id, true));
      }
    }
  }//}}}

  fn constructors_injectivite(&mut self, v: Version) {//{{{
    let mut new_eqs = vec![];
    for (_, constructors) in &self.ctx.datatypes {
      for Constructor { name, .. } in constructors {
        for eclass in self.egraph.all_eclasses(v) {
          let Some(set) = &self.egraph.app_enodes[v][&eclass].get(&name) else { continue };
          for i in 0 .. set.len() { for j in 0 .. set.len() {
            if i == j || set[i] == set[j] { continue; }
            let ENode::App(f1, args1) = self.egraph.hashcons.get(&set[i]) else { continue };
            let ENode::App(f2, args2) = self.egraph.hashcons.get(&set[j]) else { continue };
            if !self.ctx.type_info[f1].constructor { continue };
            if !self.ctx.type_info[f2].constructor { continue };
            for i in 0 .. args1.len() {
              new_eqs.push((args1[i], args2[i], i, set[i], set[j]));
            }
          }}
        }
      }
    }
    for (a, b, i, e1, e2) in new_eqs {
      if e1 == e2 { continue; }
      self.egraph.union(a, b, v, ProofEdge::Injective(i as u8, e1, e2));
    }
  }//}}}

  fn constructors_non_overlap(&mut self, v: Version) {//{{{
    for (_, constructors) in &self.ctx.datatypes {
      for Constructor { name: cons1, .. } in constructors {
        for Constructor { name: cons2, .. } in constructors {
          if cons1 == cons2 { continue; }
          for eclass in self.egraph.all_eclasses(v) {
            let Some(set) = &self.egraph.app_enodes[v].get(&eclass) else { continue };
            let Some(set1) = set.get(cons1) else { continue };
            let Some(set2) = set.get(cons2) else { continue };
            if set1.len() > 0 && set2.len() > 0 {
              self.egraph.union(self.lhs, self.rhs, v, ProofEdge::Absurd(set1[0], set2[0]));
              // this branch is done!
              self.leaf_versions.remove(&v);
              return;
            }
          }
        }
      }
    }
  }//}}}

  fn case_simpl(&mut self, v: Version) {//{{{

    'eclass_search: for eclass in self.egraph.all_eclasses(v).into_iter() {

      // skip if eclass has value
      // TODO should probably cache this
      for (f, _) in &self.egraph.app_enodes[v][&eclass] {
        if self.ctx.type_info[&f].constructor {
          continue 'eclass_search
        }
      }

      let mut candidates = vec![];

      for i in 0 .. self.egraph.case_enodes[v][&eclass].len() {
        let eid = self.egraph.case_enodes[v][&eclass][i];
        let ENode::Case(scrutinee, arms) = self.egraph.hashcons.get(&eid).clone() else { continue };
        let ENode::App(constructor, _) = self.egraph.hashcons.get(&scrutinee).clone() else { continue };
        if !self.ctx.type_info[&constructor].constructor { continue; }

        candidates.push((eid,arms,constructor,scrutinee));
      }

      for (eid, arms, constructor, scrutinee) in candidates {
        for (arm_i, (pattern, expr)) in arms.into_iter().enumerate() {
          if let Pattern::App(f, _) = pattern { if f != constructor { continue; } }

          // freshen up pattern and expr
          let vars = pattern.get_vars();
          let subst: BTreeMap<VarId, VarId> = vars.into_iter().map(|v| (v, self.ctx.vars.mk_fresh())).collect();
          let pattern: Pattern = pattern.subst(&subst);
          let expr = expr.subst(&subst.into_iter().map(|(v0,v1)| (v0, Expr::Var(v1))).collect());

          let hyp = self.fresh_hyp();
          let pat = self.egraph.add_expr(&pattern.as_expr(), v);
          self.egraph.union(scrutinee, pat, v, ProofEdge::Hyp(hyp, true));
          self.egraph.set_hyp_eq(hyp, scrutinee, pat);
          let e = self.egraph.add_expr(&expr, v);
          self.egraph.union(eid, e, v, ProofEdge::CaseSimpl(hyp, arm_i, true));

          break;
        }
      }

    }

  }//}}}

  fn case_analysis(&mut self, v: Version) -> bool {//{{{
    // we only do case analysis on leaf nodes
    if !self.leaf_versions.contains(&v) { return false; }
    if self.egraph.vuf.tree.len() >= 20 { return false; }

    'eclass_search: for eclass in self.egraph.all_eclasses(v).into_iter() {

      // skip if eclass has value
      // TODO should probably cache this
      for (f, _) in &self.egraph.app_enodes[v][&eclass] {
        if self.ctx.type_info[&f].constructor {
          continue 'eclass_search
        }
      }

      let mut candidates = vec![];

      for i in 0 .. self.egraph.case_enodes[v][&eclass].len() {
        let eid = self.egraph.case_enodes[v][&eclass][i];
        let ENode::Case(scrutinee, arms) = self.egraph.hashcons.get(&eid).clone() else { continue };
        if self.egraph.find(scrutinee, v) != scrutinee { continue; }
        if self.mark_expanded[v].contains(&eid) { continue 'eclass_search; }
        candidates.push((eid,scrutinee,arms));
      }

      if let Some((eid, scrutinee, arms)) = candidates.into_iter().min_by_key(|(e,_,_)| *e) {
        // if eid.0 != 4 && eid.0 != 5 { continue; }
        // println!("Case analysis on {} at v{}", eid.0, v);
        self.mark_expanded[v].insert(eid);

        for (arm_i, (pattern, expr)) in arms.into_iter().enumerate() {
          // freshen up pattern and expr
          let vars = pattern.get_vars();
          let subst: BTreeMap<VarId, VarId> = vars.into_iter().map(|v| (v, self.ctx.vars.mk_fresh())).collect();
          let pattern: Pattern = pattern.subst(&subst);
          let expr = expr.subst(&subst.into_iter().map(|(v0,v1)| (v0, Expr::Var(v1))).collect());

          let hyp = self.fresh_hyp();
          let v = self.fork(v, hyp);
          // equate scrutinee to pattern
          let pat = self.egraph.add_expr(&pattern.as_expr(), v);
          self.egraph.union(scrutinee, pat, v, ProofEdge::Hyp(hyp, true));
          // equate eclass to the expr
          let e = self.egraph.add_expr(&expr, v);
          self.egraph.set_hyp_eq(hyp, scrutinee, pat);
          self.egraph.union(eid, e, v, ProofEdge::CaseReduct(hyp, arm_i, true));

          // print!("  v{v}: hyp: {hyp:?}");
          // println!(": {} = {}", self.egraph.extract(scrutinee).to_string(&self.ctx),
          //                       self.egraph.extract(pat).to_string(&self.ctx));
        }

        self.remove_version(v);
        return true;
      }

    }

    return false;
  }//}}}

  fn apply_theorems(&mut self, v: Version) {//{{{
    for (lemma_id, dir, lhs, rhs) in self.rules.iter().rev() { // search backwards is really better

      // println!("v{v} searching for {} while proving {} (lhs={})",
      //   self.ctx.theorems.as_str(lemma_id),
      //   self.ctx.theorems.as_str(&self.theorem),
      //   lhs.to_string(self.ctx));

      let search_results = self.egraph.search_all(lhs, v, 10);
      'search_result: for bindings in search_results {

        let enode = self.egraph.add_pattern(lhs, &bindings, v);

        // we must check decreasing measure here
        if *lemma_id == self.theorem {
          if bindings.len() != self.arg_eclasses.len() { continue; }
          // if bindings.values().collect::<BTreeSet<_>>() == self.arg_eclasses.iter().collect::<BTreeSet<_>>() { continue 'search_result }
          let mut all_eq = true;
          // TODO: comparing against arg_eclasses is not the right way!
          for i in 0 .. self.arg_eclasses.len() {
            let e = self.arg_eclasses[i];
            let bi = bindings[&(i as u8)];
            match self.egraph.structurally_less(&self.ctx.type_info, e, bi, v) {
              StructuralOrd::LE => { all_eq = false; break; }
              StructuralOrd::UNKNOWN => { continue 'search_result; }
              StructuralOrd::EQ => {}
            }
          }
          if all_eq { continue 'search_result; }
        }

        let id = self.egraph.add_pattern(rhs, &bindings, v);

        // println!("========= v{v} MATCH {}: enode={}, lhs={}, rhs={}, lhs_inst={}, rhs_inst={}, bindings={:?}",
        //   self.ctx.theorems.as_str(lemma_id),
        //   enode.0,
        //   lhs.to_string(self.ctx),
        //   rhs.to_string(self.ctx),
        //   self.egraph.extract(enode).to_string(self.ctx),
        //   self.egraph.extract(id).to_string(self.ctx),
        //   bindings.iter().map(|(k,v)| (k, self.egraph.extract(*v).to_string(self.ctx))).collect::<BTreeMap<_,_>>()
        // );

        self.egraph.union(enode, id, v, ProofEdge::Rewrite(*lemma_id, *dir, bindings));
        if self.egraph.find(self.lhs,v) == self.egraph.find(self.rhs,v) { return; }
      }
    }
  }//}}}

  pub fn dump(&self, file: &str) {
    let _ = std::fs::write(file, self.egraph.dump(&self.ctx));
  }

}
