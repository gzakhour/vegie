
use crate::lang::ast::{Proof};
use crate::lang::myegraph::{VEGraph, ENode, ProofEdge, ENodeId, Version, ROOT_VERSION};

use std::collections::{BTreeMap, BTreeSet, BinaryHeap};


#[derive(Debug)]
pub struct ExplainCost {
  pub cost: usize,
  pub prev: ENodeId,
  pub version: Version,
  pub proof: ProofEdge,
}


impl VEGraph {


  fn shortest_path(
    &self,
    graph: &BTreeMap<(ENodeId, ProofEdge, ENodeId), usize>,
    source: ENodeId,
    target: ENodeId,
    compute_path: bool,
  ) -> Option<(usize, Vec<(ENodeId, ProofEdge, ENodeId)>)>
  {{{

    #[derive(Eq,PartialEq,Debug)]
    struct NodeAndCost {
      node: ENodeId,
      cost: usize
    }

    impl Ord for NodeAndCost { fn cmp(&self, other: &Self) -> std::cmp::Ordering { other.cost.cmp(&self.cost) } }
    impl PartialOrd for NodeAndCost { fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { Some(other.cost.cmp(&self.cost)) } }

    let mut dist: BTreeMap<ENodeId, usize> = BTreeMap::new();
    let mut queue: BinaryHeap<NodeAndCost> = BinaryHeap::new();
    let mut prev: BTreeMap<ENodeId, (ProofEdge, ENodeId)> = BTreeMap::new();

    dist.insert(source, 0);
    queue.push(NodeAndCost { node: source, cost: 0 });

    while let Some(node) = queue.pop() {
      let NodeAndCost { node, cost } = node;
      if node == target {
        return Some((cost, {
          let mut path = vec![];
          if compute_path {
            let mut node = target;
            while node != source {
              let (edge, prev) = &prev[&node];
              path.push((node, edge.clone(), *prev));
              node = *prev;
            }
            path.reverse();
          }
          path
        }))
      }
      for (_, e, next) in self.proof_graph.get(&node).unwrap_or(&BTreeSet::new()) {
        if let Some(edge_cost) = graph.get(&(node, e.clone(), *next)) {
          let alt_dist = cost + edge_cost;
          if alt_dist < dist.get(&next).copied().unwrap_or(usize::MAX) {
            dist.insert(*next, alt_dist);
            queue.push(NodeAndCost { node: *next, cost: alt_dist });
            prev.insert(*next, (e.clone(), node));
          }
        }
      }
    }

    return None;
  }}}

  pub fn with_costs(&self, v: Version) -> BTreeMap<(ENodeId, ProofEdge, ENodeId), usize> {{{
    use ProofEdge::*;

    let mut graph: BTreeMap<(ENodeId, ProofEdge, ENodeId), usize> = BTreeMap::new();

    let mut edges: BTreeSet<(ENodeId, ProofEdge, ENodeId)> = self.proof_graph.iter()
        .flat_map(|(s,es)| es.iter()
          .filter(|(ve,_,_)| self.vuf.tree.is_ancestor(*ve,v))
          .map(move |(v,e,t)| {
            (*s,e.clone(),*t)
          }))
        .collect::<BTreeSet<_>>();

    let mut congr_edges: Vec<_> = vec![];
    let total_edge_count = edges.len();

    for (start, edge, target) in edges {
      match edge {
        Definition(_,_) | Rewrite(_,_,_) | Hyp(_,_) | CaseSimpl(_,_)  => {
          graph.insert((start, edge, target), 1);
        }
        _ => {
          congr_edges.push((start, edge, target))
        }
      }
    }

    let mut iter_count = 0;
    while iter_count < 5 {
      iter_count += 1;
      let mut i = 0;
      while i < congr_edges.len() {
        match &congr_edges[i].1 {
          Congr(args) => {
            let costs = args.iter().map(|(arg0,arg1)| self.shortest_path(&graph, *arg0, *arg1, false))
                .collect::<Option<Vec<_>>>();
            if let Some(costs) = costs {
              let cost = costs.into_iter().map(|(x,_)|x).sum::<usize>();
              graph.insert(congr_edges[i].clone(), cost+1);
              congr_edges.swap_remove(i);
            } else {
              i += 1;
            }
          },

          Injective(_, arg0, arg1) | Absurd(arg0, arg1) => {
            if let Some((cost,_)) = self.shortest_path(&graph, *arg0, *arg1, false) {
              graph.insert(congr_edges[i].clone(), cost+1);
              congr_edges.swap_remove(i);
            } else {
              i += 1;
            }
          }

          Definition(_,_) | Rewrite(_,_,_) | Hyp(_,_) | CaseSimpl(_,_) =>
            unreachable!()
        }
      }
    }

    for e in congr_edges {
      graph.insert(e, total_edge_count+1);
    }

    graph
  }}}

  pub fn explain(&mut self, src: ENodeId, dest: ENodeId, v: Version) -> Proof {{{

    if self.query(src, v) == self.query(dest, v) {

      let graph = self.with_costs(v);

      let mut path = self.shortest_path(&graph, src, dest, true).unwrap().1.into_iter().map(|(before,step,after)|
        match step {
          ProofEdge::Definition(def, dir) => Proof::Definition(def, dir),
          ProofEdge::Absurd(e0, e1) =>
            Proof::Absurd(self.extract(e0), self.extract(e1), self.explain(e0, e1, v).into()),
          ProofEdge::Hyp(h, dir) => Proof::Hyp(h, dir),
          ProofEdge::Injective(arg, e0, e1) =>
            Proof::Injective(arg, self.extract(e0), self.extract(e1), self.explain(e0, e1, v).into()),
          ProofEdge::Rewrite(thm, dir, bindings) =>
            Proof::Rewrite(thm, dir, bindings.iter().map(|(v,e)| (*v, self.extract(*e).clone())).collect()),
          ProofEdge::CaseSimpl(branch, dir) =>
            Proof::CaseSimpl(branch, dir),
          ProofEdge::Congr(_) => {
            match self.hashcons.get(&before).clone() {
              ENode::App(f1, args1) => {
                let ENode::App(f2, args2) = self.hashcons.get(&after).clone() else { panic!() };
                assert_eq!(f1, f2);
                assert_eq!(args1.len(), args2.len());
                Proof::Congr(f1, args1.into_iter().zip(args2).map(|(a1,a2)| self.explain(a1, a2, v)).collect())
              },
              ENode::Case(scrutinee1, _) => {
                let ENode::Case(scrutinee2, _) = self.hashcons.get(&after).clone() else { panic!() };
                Proof::CongrScrutinee(Box::new(self.explain(scrutinee1, scrutinee2, v)))
              },
              _ => unreachable!()
            }
          }
        }).collect::<Vec<_>>();

      if path.len() == 0 { Proof::Refl }
      else if path.len() == 1 { path.pop().unwrap() }
      else { Proof::Seq(path) }

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
