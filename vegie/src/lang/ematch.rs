use crate::lang::myegraph::{Version, ENodeId, ENode, VEGraph};
use crate::lang::ast::{IdentId, VarId, Expr};
use crate::lang::ctx::{Ctx};

use std::collections::{BTreeSet, BTreeMap};

#[derive(Clone, Debug)]
pub enum SearchPattern {
  MetaVar(u8),
  App(IdentId, Vec<SearchPattern>),
}

impl SearchPattern {

  pub fn from_expr_with_args(e: &Expr, args: &Vec<VarId>) -> Option<Self> {//{{{
    Some(match e {
      Expr::Cons(id, eargs) => {
        let mut new_args = vec![];
        for a in eargs { new_args.push(Self::from_expr_with_args(a, args)?); }
        SearchPattern::App(*id, new_args)
      },
      Expr::App(id, eargs) => {
        let mut new_args = vec![];
        for a in eargs { new_args.push(Self::from_expr_with_args(a, args)?); }
        SearchPattern::App(*id, new_args)
      },
      Expr::Var(id) => {
        SearchPattern::MetaVar(args.iter().position(|p| p == id)? as u8)
      },
      Expr::Case(_, _) => None?,
    })
  }//}}}

  pub fn get_fvs(&self) -> BTreeSet<u8> {//{{{
    fn aux(p: &SearchPattern, result: &mut BTreeSet<u8>) {
      match p {
        SearchPattern::MetaVar(n) => { result.insert(*n); }
        SearchPattern::App(_, args) => { for a in args { aux(a, result) } }
      }
    }
    let mut result = BTreeSet::new();
    aux(self, &mut result);
    result
  }//}}}

  pub fn to_string(&self, ctx: &Ctx) -> String {{{
    match self {
      SearchPattern::MetaVar(n) => format!("?{n}"),
      SearchPattern::App(f, args) =>
        format!("{}{}{}{}",
          if args.len() > 0 { "(" } else { "" },
          ctx.idents.as_str(f),
          args.iter().map(|a| format!(" {}", a.to_string(ctx))).collect::<Vec<_>>().join(""),
          if args.len() > 0 { ")" } else { "" }
        )
    }
  }}}

}


pub type Bindings = BTreeMap<u8, ENodeId>;

impl VEGraph {

  pub fn search(&self, enode: ENodeId, pat: &SearchPattern, v: Version, limit: usize) -> BTreeSet<Bindings> {//{{{

    fn aux(
      egraph: &VEGraph,
      eclass: ENodeId,
      pat: &SearchPattern,
      v: Version,
      limit: usize,
      bindings: BTreeSet<Bindings>
    ) -> BTreeSet<Bindings> {

      let eclass = egraph.query(eclass, v);

      match pat {

        SearchPattern::MetaVar(var) => {
          bindings.into_iter()
            .filter_map(|mut binding| {
              match binding.get(var) {
                None => {
                  binding.insert(*var, eclass);
                  Some(binding)
                }
                Some(c) => if egraph.query(*c, v) == eclass {
                  Some(binding)
                } else {
                  None
                }
              }
            })
            .take(limit)
            .collect()
        }


        SearchPattern::App(f, args) => {

          egraph.app_enodes[v].get(&eclass).and_then(|m| m.get(f)).unwrap_or(&vec![])
          // egraph.enodes_per_eclass[v][&eclass]
            .iter()
            .flat_map(|enode| {
              if let ENode::App(enode_f, enode_args) = egraph.hashcons.get(&enode) {
                if enode_f != f { return BTreeSet::new() }

                assert_eq!(enode_f, f);
                assert_eq!(enode_args.len(), args.len());

                let mut result = bindings.clone();
                for i in 0 .. args.len() {
                  result = aux(egraph, enode_args[i], &args[i], v, limit, result);
                }

                result
              } else {
                BTreeSet::new()
              }
          }).take(limit)
            .collect()

        }

      }

    }

    aux(self, enode, pat, v, limit, BTreeSet::from([ BTreeMap::new() ]))

  }//}}}

  pub fn search_all(&self, pat: &SearchPattern, v: Version, limit: usize) -> BTreeSet<Bindings> {//{{{
    // println!("starting search for {pat:?} at v{v}");
    let ans = self.all_eclasses(v)
        .into_iter()
        .rev()
        .flat_map(move |eclass| self.search(eclass, pat, v, limit))
        .take(limit)
        .collect::<BTreeSet<_>>();
    // println!("  got {} results", ans.len());
    ans
  }//}}}

}

