#![allow(dead_code)]
use std::collections::{BTreeSet, BTreeMap};

use crate::lang::tokenizer::{WithLoc};
use crate::lang::ctx::{Ctx};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct IdentId(pub usize);
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct VarId(pub usize);
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct TypeId(pub usize);
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct TheoremId(pub usize);

#[derive(Clone, Debug)]
pub struct Constructor {
  pub name: IdentId,
  pub args: Vec<TypeId>,
}

#[derive(Eq, PartialEq, PartialOrd, Ord, Clone, Debug)]
pub enum Pattern {
  Var(VarId),
  App(IdentId, Vec<Pattern>),
}

#[derive(Eq, PartialEq, PartialOrd, Ord, Clone, Debug)]
pub enum Expr {
  Var(VarId),
  Cons(IdentId, Vec<Expr>),
  App(IdentId, Vec<Expr>),
  Case(Box<Expr>, Vec<(Pattern, Expr)>),
}

#[derive(Debug)]
pub enum Command {
  DatatypeDecl {
    name: TypeId,
    constructors: Vec<Constructor>,
  },

  TypeDecl {
    name: IdentId,
    dom: Vec<TypeId>,
    codom: TypeId,
  },

  Def {
    name: IdentId,
    args: Vec<VarId>,
    body: WithLoc<Expr>,
  },

  Theorem {
    name: WithLoc<TheoremId>,
    args: Vec<VarId>,
    lhs: Expr,
    rhs: Expr,
    is_assumed: bool,
  },

  Eval {
    expr: WithLoc<Expr>,
    typ: TypeId,
  }
}


pub trait Id {
  fn as_usize(&self) -> usize;
  fn from(n: usize) -> Self;
}

impl Id for IdentId {
  fn as_usize(&self) -> usize { self.0 }
  fn from(n: usize) -> Self { Self(n) }
}

impl Id for TypeId {
  fn as_usize(&self) -> usize { self.0 }
  fn from(n: usize) -> Self { Self(n) }
}

impl Id for VarId {
  fn as_usize(&self) -> usize { self.0 }
  fn from(n: usize) -> Self { Self(n) }
}

impl Id for TheoremId {
  fn as_usize(&self) -> usize { self.0 }
  fn from(n: usize) -> Self { Self(n) }
}


impl Expr {

  pub fn subst(&self, subst: &BTreeMap<VarId, Expr>) -> Expr {//{{{
    match self {
      // TODO what about unbound variables here?
      Expr::Var(id) => subst.get(id).cloned().unwrap_or(self.clone()),

      Expr::Cons(ident, args) =>
        Expr::Cons(*ident, args.iter().map(|a| a.subst(subst)).collect()),

      Expr::App(ident, args) =>
        Expr::App(*ident, args.iter().map(|a| a.subst(subst)).collect()),

      Expr::Case(scrutinee, arms) =>
        Expr::Case(Box::new(scrutinee.subst(subst)),
          arms.iter().map(|(p,e)| (p.clone(), e.subst(subst))).collect()),
    }
  }//}}}

  pub fn get_idents(&self) -> BTreeSet<IdentId> {{{
    fn aux(e: &Expr, set: &mut BTreeSet<IdentId>) {
      match e {
        Expr::Var(_) => {},
        Expr::Cons(f, args) | Expr::App(f, args) => {
          set.insert(*f);
          for a in args { aux(a, set); }
        }
        Expr::Case(e, arms) => {
          aux(e, set);
          for (_, e) in arms { aux(e, set); }
        }
      }
    }
    let mut result = BTreeSet::new();
    aux(self, &mut result);
    result
  }}}

}

impl Pattern {

  pub fn subst(&self, subst: &BTreeMap<VarId, VarId>) -> Pattern {//{{{
    match self {
      Pattern::Var(id) => Pattern::Var(*subst.get(id).unwrap()),
      Pattern::App(kons, args) =>
        Pattern::App(*kons, args.iter().map(|a| a.subst(subst)).collect()),
    }
  }//}}}

  pub fn get_vars(&self) -> Vec<VarId> {//{{{
    use std::collections::{BTreeSet};
    let mut set = BTreeSet::new();
    fn aux(pat: &Pattern, vars: &mut BTreeSet<VarId>) {
      match pat {
        Pattern::Var(id) => { vars.insert(*id); }
        Pattern::App(_, args) => {
          for a in args { aux(a, vars); }
        }
      }
    }
    aux(self, &mut set);
    return set.into_iter().collect()
  }//}}}

  pub fn as_expr(&self) -> Expr {//{{{
    match self {
      Pattern::Var(id) => Expr::Var(*id),
      Pattern::App(kons, args) =>
        Expr::Cons(*kons, args.iter().map(|a| a.as_expr()).collect())
    }
  }//}}}

}



pub enum Proof {
  Refl,
  Definition(IdentId, bool),
  Rewrite(TheoremId, bool, BTreeMap<u8, Expr>),
  Congr(IdentId, Vec<Proof>),
  CongrScrutinee(Box<Proof>),
  Injective(u8, Expr, Expr, Box<Proof>),
  Absurd(Expr, Expr, Box<Proof>),
  Cases(Vec<(IdentId, Expr, Expr, Proof)>),
  CaseReduct(IdentId, usize, bool),
  Hyp(IdentId, bool),
  Seq(Vec<Proof>),
}

impl Proof {
  pub fn to_string(&self, ctx: &Ctx) -> String {//{{{
    use Proof::*;
    match self {
      Refl => "refl".to_string(),
      Definition(ident, b) => format!("(expand {}{})", if *b { "" } else { "<- " }, ctx.idents.as_str(ident)),
      Congr(f, args) => {
        let mut result = format!("({}", ctx.idents.as_str(f));
        for a in args { result.push_str(&format!(" {}", a.to_string(ctx))); }
        result.push(')');
        return result
      },
      Injective(n, e1, e2, p) =>
        format!("(injectivity {n} {} {} {})", e1.to_string(ctx), e2.to_string(ctx), p.to_string(ctx)),
      Absurd(e1, e2, p) =>
        format!("(absurd {} {} {})",  e1.to_string(ctx), e2.to_string(ctx), p.to_string(ctx)),
      Cases(arms) => {
        let mut result = format!("(cases");
        for (hyp, e1, e2, p) in arms {
          result.push_str(&format!(" ({} ({} {}) {})", ctx.idents.as_str(hyp), e1.to_string(ctx), e2.to_string(ctx), p.to_string(ctx)));
        }
        result.push(')');
        return result
      },
      Rewrite(theorem, dir, bindings) => {
        let mut result = format!("(apply {}{}", if *dir { "" } else { "<- " }, ctx.theorems.as_str(theorem));
        for i in 0 .. bindings.len() {
          result.push_str(&format!(" {}", bindings[&(i as u8)].to_string(ctx)));
        }
        result.push(')');
        return result
      },
      Seq(steps) => {
        let mut result = format!("(seq");
        for s in steps { result.push_str(&format!(" {}", s.to_string(ctx))); }
        result.push(')');
        return result
      },
      CaseReduct(hyp, arm, dir) => {
        format!("(case-reduce {}{} {arm})", if *dir { "" } else { "<- " }, ctx.idents.as_str(hyp))
      },
      Hyp(ident, dir) => {
        format!("(hyp {}{})", if *dir { "" } else { "<- " }, ctx.idents.as_str(ident))
      },
      CongrScrutinee(p) => {
        format!("(congr-scrutinee {})", p.to_string(ctx))
      }
    }
  }//}}}
}
