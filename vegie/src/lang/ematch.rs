use crate::lang::myegraph::{Version, ENodeId, ENode, VEGraph};
use crate::lang::ast::{IdentId, VarId, Expr, Pattern, Proof};
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

  pub fn search(&self, enode: ENodeId, pat: &SearchPattern, v: Version, limit: usize, millis: u64) -> Vec<Bindings> {//{{{

    fn aux(
      egraph: &VEGraph,
      enode: ENodeId,
      pat: &SearchPattern,
      v: Version,
      limit: usize,
      millis: u64,
      mut bindings: Vec<Bindings>
    ) -> Vec<Bindings> {

      let eclass = egraph.query(enode, v);

      match pat {

        SearchPattern::MetaVar(var) => {
          let mut i = 0;
          while i < bindings.len() {
            match bindings[i].get(var) {
              None => {
                bindings[i].insert(*var, eclass);
                i += 1;
              }
              Some(c) => if egraph.query(*c, v) == eclass {
                i += 1;
              } else {
                bindings.swap_remove(i);
              }
            }
          }

          bindings
        }


        SearchPattern::App(f, args) => {

          if let ENode::App(enode_f, enode_args) = egraph.hashcons.get(&enode) {

            if enode_f != f { return vec![] }

            assert_eq!(enode_f, f);
            assert_eq!(enode_args.len(), args.len());

            let mut result = bindings.clone();
            for i in 0 .. args.len() {
              result = aux(egraph, enode_args[i], &args[i], v, limit, millis, result);
            }

            result

          } else {
            vec![]
          }

        }

      }

    }

    aux(self, enode, pat, v, limit, millis, vec![ BTreeMap::new() ])

  }//}}}

  pub fn search_all(&self, pat: &SearchPattern, v: Version, limit: usize) -> impl Iterator<Item=(ENodeId, Bindings)> {//{{{
    self.enodes_per_versions[v]
        .iter()
        .flat_map(move |enode|
          self.search(*enode, pat, v, limit, 100).into_iter().map(|b| (*enode, b)))
  }//}}}

}

