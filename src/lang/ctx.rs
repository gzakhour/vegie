use std::collections::{BTreeMap, BTreeSet};

use crate::lang::ast::{Id, TypeId, IdentId, VarId, TheoremId};
use crate::lang::ast::{Constructor, Pattern, Expr};

pub struct Ctx {
  pub idents: NameCtx<IdentId>,
  pub vars: NameCtx<VarId>,
  pub types: NameCtx<TypeId>,
  pub theorems: NameCtx<TheoremId>,
  pub scoped: ScopedName,
  pub type_info: BTreeMap<IdentId, TypeInfo>,
  pub var_types: BTreeMap<VarId, TypeId>,
  pub datatypes: BTreeMap<TypeId, Vec<Constructor>>,
  pub defs: BTreeMap<IdentId, (Vec<VarId>, Expr)>,
  pub theorem_stmts: BTreeMap<TheoremId, (Vec<VarId>, Expr, Expr)>,
  pub proven_theorem: BTreeSet<TheoremId>,
}

impl Ctx {
  pub fn new() -> Ctx {
    Ctx {
      idents: NameCtx::new(),
      vars: NameCtx::new(),
      types: NameCtx::new(),
      theorems: NameCtx::new(),
      scoped: ScopedName::new(),
      type_info: BTreeMap::new(),
      var_types: BTreeMap::new(),
      datatypes: BTreeMap::new(),
      defs: BTreeMap::new(),
      theorem_stmts: BTreeMap::new(),
      proven_theorem: BTreeSet::new(),
    }
  }
}

pub struct TypeInfo {
  pub dom: Vec<TypeId>,
  pub codom: TypeId,
  pub constructor: bool,
}

#[derive(Debug)]
pub struct NameCtx<T: Id> {
  map: BTreeMap<String, T>,
  names: Vec<String>,
  fresh_count: usize,
}

impl<T: Id> NameCtx<T> {
  pub fn new() -> NameCtx<T> {
    NameCtx {
      map: BTreeMap::new(),
      names: vec![],
      fresh_count: 0,
    }
  }

  pub fn contains(&self, name: &String) -> bool {
    self.map.contains_key(name)
  }

  pub fn get(&mut self, name: &String) -> T {
    // let name = name.split('$').next().unwrap().to_string();
    let name = name.to_string();
    if let Some(id) = self.map.get(&name) { T::from(T::as_usize(id)) } else {
      let n = self.map.len();
      self.map.insert(name.clone(), T::from(n));
      self.names.push(name.clone());
      T::from(n)
    }
  }

  pub fn as_str(&self, id: &T) -> &String {
    &self.names[T::as_usize(id)]
  }

  pub fn mk_fresh(&mut self) -> T {
    let name = format!("__?{}", self.fresh_count);
    self.fresh_count += 1;
    self.get(&name)
  }
}

#[derive(Debug)]
pub struct ScopedName {
  pub map: BTreeMap<String, usize>,
}

impl ScopedName {
  pub fn new() -> ScopedName {
    ScopedName { map: BTreeMap::new() }
  }

  pub fn push(&mut self, name: &String) -> String {
    if let Some(val) = self.map.get_mut(name) {
      *val += 1;
    } else {
      self.map.insert(name.clone(), 1);
    }
    self.get(name).unwrap()
  }

  pub fn get(&self, name: &String) -> Option<String> {
    if let Some(val) = self.map.get(name) {
      if *val == 0 { None } else { Some(format!("{name}${val}")) }
    } else {
      None
    }
  }

  pub fn pop(&mut self, name: &String) {
    if let Some(val) = self.map.get_mut(name) {
      if *val == 0 { 
        assert!(false, "{name} should never be bound 0-times (missing remove)");
      }
      *val -= 1;
      if *val == 0 {
        self.map.remove(name);
      }
    } else {
      assert!(false, "{name} does not exist in the scope");
    }
  }
}



impl Pattern {
  pub fn to_string(&self, ctx: &Ctx) -> String {
    match self {
      Pattern::Var(id) => ctx.vars.as_str(id).to_string(),
      Pattern::App(id, args) => {
        if args.len() == 0 {
          ctx.idents.as_str(id).to_string()
        } else {
          let mut result = String::from("(");
          result.push_str(ctx.idents.as_str(id));
          for a in args {
            result.push(' ');
            result.push_str(&a.to_string(ctx));
          }
          result.push(')');
          result
        }
      },
    }
  }
}


impl Expr {
  pub fn to_string(&self, ctx: &Ctx) -> String {
    match self {
      Expr::Var(id) => ctx.vars.as_str(id).to_string(),
      Expr::Cons(id, args) => {
        if args.len() == 0 { ctx.idents.as_str(id).to_string() }
        else {
          let mut result = String::from("(");
          result.push_str(ctx.idents.as_str(id));
          for a in args {
            result.push(' ');
            result.push_str(&a.to_string(ctx));
          }
          result.push(')');
          result
        }
      },
      Expr::App(id, args) => {
        if ctx.type_info[id].constructor {
          Expr::Cons(*id, args.clone()).to_string(ctx)
        } else {
          let mut result = String::from("(");
          result.push_str(ctx.idents.as_str(id));
          for a in args {
            result.push(' ');
            result.push_str(&a.to_string(ctx));
          }
          result.push(')');
          result
        }
      },
      Expr::Case(scrutinee, arms) => {
        let mut result = "(case ".to_string();
        result.push_str(&scrutinee.to_string(ctx));
        for (arg, expr) in arms {
          result.push_str(" (");
          result.push_str(&arg.to_string(ctx));
          result.push(' ');
          result.push_str(&expr.to_string(ctx));
          result.push(')');
        }
        result.push(')');
        result
      }
    }
  }
}

impl crate::lang::myegraph::ProofEdge {
  pub fn to_string(&self, ctx: &Ctx) -> String {
    fn op(x: String, dir: &bool) -> String {
      if *dir { format!("{x}⁻¹") } else { x }
    }

    use crate::lang::myegraph::ProofEdge::*;
    match self {
      Definition(id, dir) => op(ctx.idents.as_str(id).to_string(), dir),
      Congr(args) => format!("congr {:?}", args.iter().map(|(a,b)|(a.0,b.0)).collect::<Vec<_>>()),
      Rewrite(id, dir, bindings) => format!("{}", op(ctx.theorems.as_str(id).to_string(), dir)),
      Absurd(e1, e2) => format!("n{}=n{}: ※", e1.0, e2.0),
      Hyp(id, dir) => format!("hyp: {}", op(ctx.idents.as_str(id).to_string(), dir)),
      CaseSimpl(arm, dir) => format!("case-simpl:{dir:?} arm={arm}"),
      Injective(arg, e1, e2) => format!("n{}=n{}: inj={arg}", e1.0, e2.0),
    }
  }
}
