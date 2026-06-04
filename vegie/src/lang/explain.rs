
use crate::lang::ast::{Proof};
use crate::lang::myegraph::{VEGraph, ENode, ProofEdge, ENodeId, Version, ROOT_VERSION};

use std::collections::{BTreeMap, BTreeSet};


#[derive(Debug)]
pub struct ExplainCost {
  pub cost: usize,
  pub prev: ENodeId,
  pub version: Version,
  pub proof: ProofEdge,
}


impl VEGraph {


  pub fn edge_costs(&self, source: ENodeId) -> BTreeMap<ENodeId, BTreeMap<Version, ExplainCost>> {{{
    let mut result: BTreeMap<ENodeId, BTreeMap<Version, ExplainCost>> = BTreeMap::new();

    result.insert(source, self.vuf.tree.all_versions().map(|v| (v, ExplainCost {
      cost: 0,
      prev: source,
      version: v,
      proof: ProofEdge::Congr, // anything will do
    })).collect());

    let mut queue = vec![ source ];
    let mut visited: BTreeSet<ENodeId> = BTreeSet::new();

    while let Some(node) = queue.pop() {
      if visited.contains(&node) { continue; }
      visited.insert(node);

      for (v, proof, next) in self.proof_graph.get(&node).unwrap_or(&Default::default()) {

        result.entry(*next).or_insert_with(|| BTreeMap::new());

        for vc in self.vuf.tree.all_descendents(*v) {
          let c = self.vuf.tree.all_between(ROOT_VERSION, vc).iter()
                               .filter_map(|v| result[&node].get(&v))
                               .map(|c| c.cost)
                               .min()
                               .unwrap_or(usize::MAX);

          if c == usize::MAX { continue; }
          let new_cost = c + match proof {
            ProofEdge::Congr | ProofEdge::Absurd(_,_) | ProofEdge::Injective(_,_,_) => 100,
            _ => 1
          };

          if result[&next].get(&vc).map(|c| c.cost).unwrap_or(usize::MAX) > new_cost {
            let entry = result.get_mut(&next).unwrap().entry(vc).or_insert(ExplainCost {
              cost: usize::MAX, prev: node, proof: ProofEdge::Congr, version: *v
            });
            entry.cost = new_cost;
            entry.prev = node;
            entry.version = *v;
            entry.proof = proof.clone();
            visited.remove(next); // TODO is there a better way?
          }
        }

        queue.push(*next);
      }
    }

    result
  }}}


  // TODO:
  //   1. do not make it so recursive
  //   2. do not recompute the edge costs all the time, especially when `src` does not change (see 1)
  pub fn explain(&mut self, src: ENodeId, dest: ENodeId, v: Version) -> Proof {{{

    println!("Explain {} = {} at v{v}", src.0, dest.0);

    if src == dest { return Proof::Refl }

    let costs = self.edge_costs(src);

    let c = costs.get(&dest).and_then(|m| m.get(&v)).map(|c| c.cost).unwrap_or(usize::MAX);

    if c < usize::MAX {
      let ExplainCost { prev: new_dest, proof: step, .. } = &costs[&dest][&v];
      let step =
        match step {
          ProofEdge::Definition(def, dir) => Proof::Definition(*def, *dir),
          ProofEdge::Absurd(e0, e1) =>
            Proof::Absurd(self.extract(*e0), self.extract(*e1), self.explain(*e0, *e1, v).into()),
          ProofEdge::Hyp(h, dir) => Proof::Hyp(*h, *dir),
          ProofEdge::Injective(arg, e0, e1) =>
            Proof::Injective(*arg, self.extract(*e0), self.extract(*e1), self.explain(*e0, *e1, v).into()),
          ProofEdge::Rewrite(thm, dir, bindings) =>
            Proof::Rewrite(*thm, *dir, bindings.iter().map(|(v,e)| (*v, self.extract(*e))).collect()),
          ProofEdge::CaseReduct(e, branch, dir) =>
            Proof::CaseReduct(*e, *branch, *dir),
          ProofEdge::CaseSimpl(branch, dir) =>
            Proof::CaseSimpl(*branch, *dir),
          ProofEdge::Congr => {
            match self.hashcons.get(&new_dest).clone() {
              ENode::App(f1, args1) => {
                let ENode::App(f2, args2) = self.hashcons.get(&dest).clone() else { panic!() };
                assert_eq!(f1, f2);
                assert_eq!(args1.len(), args2.len());
                Proof::Congr(f1, args1.into_iter().zip(args2).map(|(a1,a2)| self.explain(a1, a2, v)).collect())
              },
              ENode::Case(scrutinee1, _) => {
                let ENode::Case(scrutinee2, _) = self.hashcons.get(&dest).clone() else { panic!() };
                Proof::CongrScrutinee(Box::new(self.explain(scrutinee1, scrutinee2, v)))
              },
              _ => unreachable!()
            }
          }
        };

      let rest = self.explain(src, *new_dest, v);

      match rest {
        Proof::Seq(mut seq) => {
          seq.push(step);
          Proof::Seq(seq)
        },
        Proof::Refl => step,
        rest => Proof::Seq(vec![ rest, step ]),
      }

    } else {
      let v_children = self.vuf.tree.children[v].clone();
      if v_children.len() == 0 { panic!("There's no way to prove this"); }
      Proof::Cases(
        v_children.into_iter().map(|v| {
          let hyp = self.version_hyp[v];
          let (lhs_hyp, rhs_hyp) = self.hyp_eq[&hyp].clone();
          (hyp, self.extract(lhs_hyp), self.extract(rhs_hyp), self.explain(src, dest, v))
        }).collect()
      )
    }

  }}}


}
