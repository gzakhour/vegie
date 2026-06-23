use crate::lang::ast::{Expr, Pattern, VarId};
use crate::lang::ctx::{Ctx};

use std::rc::{Rc};
use std::collections::{BTreeMap};

impl Pattern {
  fn unify(&self, e: &Expr) -> Option<BTreeMap<VarId, Expr>> {
    fn aux(arg: &Pattern, e: &Expr, map: &mut BTreeMap<VarId, Expr>) -> Option<()> {
      match arg {
        Pattern::Var(x) => {
          assert!(!map.contains_key(x));
          map.insert(x.clone(), e.clone());
          Some(())
        },
        Pattern::App(k1, args1) => match e {
          Expr::App(k2, args2) | Expr::Cons(k2, args2) if k1 == k2 && args1.len() == args2.len() => {
            for (a1,a2) in args1.iter().zip(args2) {
              aux(a1, a2, map)?;
            }
            Some(())
          },
          _ => None
        },
      }
    }
    let mut bindings = BTreeMap::new();
    aux(self, e, &mut bindings)?;
    Some(bindings)
  }
}

pub enum Env {
  Empty,
  Env {
    bindings: BTreeMap<VarId, Expr>,
    parent: Rc<Env>
  }
}

impl Env {
  fn get(&self, id: &VarId) -> Option<Expr> {
    match self {
      Env::Empty => None,
      Env::Env { bindings, parent } =>
        bindings.get(id).cloned().or_else(|| parent.get(id))
    }
  }
}

pub fn eval(e: &Expr, ctx: &Ctx, env: Rc<Env>) -> Expr {
  use Expr::*;
  match e {
    Var(x) => env.get(x).unwrap_or_else(|| e.clone()),

    Cons(k, args) =>
      Cons(k.clone(), args.iter().map(|a| eval(a, ctx, env.clone())).collect()),

    App(f, args) => {
      let args = args.iter().map(|a| eval(a, ctx, env.clone())).collect::<Vec<_>>();

      if let Some((func_args, body)) = ctx.defs.get(f) {
        if args.len() != func_args.len() {
          e.clone()
        } else {
          eval(body, ctx, Rc::new(Env::Env {
            bindings: args.into_iter().zip(func_args).map(|(a,b)| (b.clone(),a)).collect::<BTreeMap<_,_>>(),
            parent: env.clone()
          }))
        }
      } else {
        e.clone()
      }
    },

    Case(scrutinee, arms) => {
      let scrutinee = eval(scrutinee, ctx, env.clone());
      for (pattern, expr) in arms {
        if let Some(bindings) = pattern.unify(&scrutinee) {
          return eval(expr, ctx, Rc::new(Env::Env {
            bindings, parent: env.clone()
          }));
        }
      }
      return e.clone();
    }
  }
}
