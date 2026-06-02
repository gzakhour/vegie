
use crate::lang::ast::{Proof};
use crate::lang::myegraph::{VEGraph, ENode, ProofEdge, ENodeId, Version};

use std::collections::{BTreeMap};

impl VEGraph {

  pub fn explain(&mut self, src: ENodeId, dest: ENodeId, v: Version) -> Proof {{{
    if src == dest { return Proof::Refl; }

    use std::collections::{BinaryHeap};

    let mut found = false;
    let mut prev = BTreeMap::new();

    {
      use std::cmp::{Ordering};
      #[derive(Eq,PartialEq)]
      struct Node { node: ENodeId, cost: usize }
      impl Ord for Node { fn cmp(&self, other: &Self) -> Ordering { other.cost.cmp(&self.cost) } }
      impl PartialOrd for Node { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(&other)) } }

      let mut dist = BTreeMap::new();
      let mut queue = BinaryHeap::new();
      // let mut visited = BTreeSet::new();

      queue.push(Node { node: src.clone(), cost: 0 });
      dist.insert(src.clone(), 0);

      while let Some(Node { node, cost }) = queue.pop() {
        // if node == dest { found = true; break; }
        // if visited.contains(&node) { continue; }
        // visited.insert(node);

        'edge_search: for (ve, step, next) in &self.proof_graph[&node] {
          // if visited.contains(next) { continue; }
          let cost: usize = cost +
            if v == *ve { 1 }
            else if self.vuf.tree.is_ancestor(*ve, v) { 2 }
            else if self.vuf.tree.is_ancestor(v, *ve) {
              let dist = self.vuf.tree.distance(v, *ve);
              for vc in self.vuf.tree.all_between(v, *ve) {
                // check that the equality also holds at all versions in between
                // i.e. don't consider an edge at a subversion if there won't be a path at other subversions
                if !self.equal(node, *next, vc) { continue 'edge_search; }
              }
              15 << dist
            } else { continue };
          if cost < *dist.get(next).unwrap_or(&usize::MAX) {
            queue.push(Node { node: *next, cost });
            prev.insert(next.clone(), (*ve, step.clone(), node));
            dist.insert(*next, cost);
          }
        }

      }
    }

    // if !found { panic!("The proof does not contain all the required edges to show the equality!") }

    let mut path: Vec<Proof> = vec![];
    let mut node = dest.clone();
    while node != src {
      let (ve, step, prev) = prev[&node].clone();
      // println!("==== {v}: GOING BACK FROM {} to {} using edge at version {ve}", node.0, prev.0);
      path.push(if self.vuf.tree.is_ancestor(ve, v) {
        match step.clone() {
          ProofEdge::Definition(ident, dir) =>
            Proof::Definition(ident, dir),
          ProofEdge::Rewrite(id, dir, bindings) =>
            Proof::Rewrite(id, dir, bindings.into_iter().map(|(k,e)| (k, self.extract(e))).collect()),
          ProofEdge::Injective(i, a, b) =>
            Proof::Injective(i, self.extract(a), self.extract(b), Box::new(self.explain(a, b, v))),
          ProofEdge::Absurd(a, b) =>
            Proof::Absurd(self.extract(a), self.extract(b), Box::new(self.explain(a, b, v))),
          ProofEdge::CaseReduct(id, i, dir) => Proof::CaseReduct(id, i, dir),
          ProofEdge::Hyp(id, dir) => Proof::Hyp(id, dir),
          ProofEdge::Congr => {
            match self.hashcons.get(&prev).clone() {
              ENode::App(f1, args1) => {
                let ENode::App(f2, args2) = self.hashcons.get(&node).clone() else { panic!() };
                assert_eq!(f1, f2);
                assert_eq!(args1.len(), args2.len());
                Proof::Congr(f1, args1.into_iter().zip(args2).map(|(a1,a2)| self.explain(a1, a2, v)).collect())
              },
              ENode::Case(scrutinee1, _) => {
                let ENode::Case(scrutinee2, _) = self.hashcons.get(&node).clone() else { panic!() };
                Proof::CongrScrutinee(Box::new(self.explain(scrutinee1, scrutinee2, v)))
              },
              _ => unreachable!()
            }
          }
        }
      } else if self.vuf.tree.is_ancestor(v, ve) {
        let children = self.vuf.tree.children[v].clone();
        Proof::Cases(children.into_iter().map(|vc| {
          let hyp = self.version_hyp[vc];
          let (e1, e2) = self.hyp_eq[&hyp];
          assert!(self.equal(prev, node, vc));
          (hyp, self.extract(e1), self.extract(e2), self.explain(prev, node, vc))
        }).collect())
      } else {
        unreachable!()
      });
      node = prev;
    }

    path.reverse();

    if path.len() == 1 { path.pop().unwrap() }
    else { Proof::Seq(path) }
  }}}

}
