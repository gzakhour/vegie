use crate::egraph::aliases::{*};
use crate::egraph::version_egraph::{*};

use std::ops::{Deref, DerefMut};

use egg::{ENodeOrVar, Pattern, SearchMatches, Subst, Var};
use egg::{FromOp, Id, Language, PatternAst, RecExpr};
use std::result::{Result};

impl Language for ENode {
  type Discriminant = Operator;
  fn discriminant(&self) -> Self::Discriminant {
    self.op
  }
  fn matches(&self, other: &Self) -> bool {
    self.op == other.op && self.args.len() == other.args.len()
  }
  fn children(&self) -> &[egg::Id] {
    &self.args
  }
  fn children_mut(&mut self) -> &mut [egg::Id] {
    &mut self.args
  }
}
impl FromOp for ENode {
  type Error = ();
  fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
    Ok(ENode { op: SymbolIds::from_string(op), args: children })
  }
}
pub trait MachineRequirements {
  fn canonicals(&self) -> impl std::iter::Iterator<Item = &Id>;
  fn for_each_matching_node<Err>(
    &self,
    eclass: EClass,
    enode: &ENode,
    callback: impl FnMut(&ENode) -> Result<(), Err>,
  ) -> Result<(), Err>;
}
fn private_extract<L: Language>(expr: &RecExpr<L>, new_root: Id) -> RecExpr<L> {
  expr[new_root].build_recexpr(|id| expr[id].clone())
}

#[derive(Default)]
struct Machine {
  reg: Vec<Id>,
  // a buffer to re-use for lookups
  lookup: Vec<Id>,
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Reg(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
  instructions: Vec<Instruction>,
  subst: Subst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Instruction {
  Bind { node: ENode, i: Reg, out: Reg },
  Compare { i: Reg, j: Reg },
  Lookup { term: Vec<ENodeOrReg>, i: Reg },
  Scan { out: Reg },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ENodeOrReg {
  ENode(ENode),
  Reg(Reg),
}

impl Machine {
  #[inline(always)]
  fn reg(&self, reg: Reg) -> Id {
    self.reg[reg.0 as usize]
  }

  fn run<S: Deref<Target=VersionedEGraph>>(
    &mut self,
    egraph: &Projection<S>,
    instructions: &[Instruction],
    subst: &Subst,
    yield_fn: &mut impl FnMut(&Self, &Subst) -> Result<(), ()>,
  ) -> Result<(), ()> {
    let mut instructions = instructions.iter();
    while let Some(instruction) = instructions.next() {
      match instruction {
        Instruction::Bind { i, out, node } => {
          let remaining_instructions = instructions.as_slice();
          let eclass = egraph.find(self.reg(*i));
          return egraph.for_each_matching_node(eclass, node, |matched| {
            self.reg.truncate(out.0 as usize);
            matched.for_each(|id| self.reg.push(id));
            self.run(egraph, remaining_instructions, subst, yield_fn)
          });
        },
        Instruction::Scan { out } => {
          let remaining_instructions = instructions.as_slice();
          for &class in egraph.canonicals() {
            self.reg.truncate(out.0 as usize);
            self.reg.push(class);
            self.run(egraph, remaining_instructions, subst, yield_fn)?
          }
          return Ok(());
        },
        Instruction::Compare { i, j } => {
          if egraph.find(self.reg(*i)) != egraph.find(self.reg(*j)) {
            return Ok(());
          }
        },
        Instruction::Lookup { term, i } => {
          self.lookup.clear();
          for node in term {
            match node {
              ENodeOrReg::ENode(node) => {
                let look = |i| self.lookup[usize::from(i)];
                match egraph.get_class(&node.clone().map_children(look)) {
                  Some(id) => self.lookup.push(egraph.find(*id)),
                  None => return Ok(()),
                }
              },
              ENodeOrReg::Reg(r) => {
                self.lookup.push(egraph.find(self.reg(*r)));
              },
            }
          }

          let id = egraph.find(self.reg(*i));
          if self.lookup.last().copied() != Some(id) {
            return Ok(());
          }
        },
      }
    }
    yield_fn(self, subst)
  }
}

struct Compiler {
  v2r: Map<Var, Reg>, // CHANGED was IndexMap
  free_vars: Vec<Set<Var>>,
  subtree_size: Vec<usize>,
  todo_nodes: Map<(Id, Reg), ENode>,
  instructions: Vec<Instruction>,
  next_reg: Reg,
}

impl Compiler {
  fn new() -> Self {
    Self {
      free_vars: Default::default(),
      subtree_size: Default::default(),
      v2r: Default::default(),
      todo_nodes: Default::default(),
      instructions: Default::default(),
      next_reg: Reg(0),
    }
  }

  fn add_todo(&mut self, pattern: &PatternAst<ENode>, id: Id, reg: Reg) {
    match &pattern[id] {
      ENodeOrVar::Var(v) => {
        if let Some(&j) = self.v2r.get(v) {
          self.instructions.push(Instruction::Compare { i: reg, j })
        } else {
          self.v2r.insert(*v, reg);
        }
      },
      ENodeOrVar::ENode(pat) => {
        self.todo_nodes.insert((id, reg), pat.clone());
      },
    }
  }

  fn load_pattern(&mut self, pattern: &PatternAst<ENode>) {
    let len = pattern.len();
    self.free_vars = Vec::with_capacity(len);
    self.subtree_size = Vec::with_capacity(len);

    for node in pattern {
      let mut free = Set::default();
      let mut size = 0;
      match node {
        ENodeOrVar::ENode(n) => {
          size = 1;
          for &child in n.children() {
            free.extend(&self.free_vars[usize::from(child)]);
            size += self.subtree_size[usize::from(child)];
          }
        },
        ENodeOrVar::Var(v) => {
          free.insert(*v);
        },
      }
      self.free_vars.push(free);
      self.subtree_size.push(size);
    }
  }

  fn next(&mut self) -> Option<((Id, Reg), ENode)> {
    // we take the max todo according to this key
    // - prefer grounded
    // - prefer more free variables
    // - prefer smaller term
    let key = |(id, _): &&(Id, Reg)| {
      let i = usize::from(*id);
      let n_bound = self.free_vars[i].iter().filter(|v| self.v2r.contains_key(*v)).count();
      let n_free = self.free_vars[i].len() - n_bound;
      let size = self.subtree_size[i] as isize;
      (n_free == 0, n_free, -size)
    };

    self.todo_nodes
      .keys()
      .max_by_key(key)
      .copied()
      .map(|k| (k, self.todo_nodes.remove(&k).unwrap()))
  }

  /// check to see if this e-node corresponds to a term that is grounded by
  /// the variables bound at this point
  fn is_ground_now(&self, id: Id) -> bool {
    self.free_vars[usize::from(id)].iter().all(|v| self.v2r.contains_key(v))
  }

  fn compile(&mut self, patternbinder: Option<Var>, pattern: &PatternAst<ENode>) {
    self.load_pattern(pattern);
    let root = pattern.root();

    let mut next_out = self.next_reg;

    // Check if patternbinder already bound in v2r
    // Behavior common to creating a new pattern
    let add_new_pattern = |comp: &mut Compiler| {
      if !comp.instructions.is_empty() {
        // After first pattern needs scan
        comp.instructions.push(Instruction::Scan { out: comp.next_reg });
      }
      comp.add_todo(pattern, root, comp.next_reg);
    };

    if let Some(v) = patternbinder {
      if let Some(&i) = self.v2r.get(&v) {
        // patternbinder already bound
        self.add_todo(pattern, root, i);
      } else {
        // patternbinder is new variable
        next_out.0 += 1;
        add_new_pattern(self);
        self.v2r.insert(v, self.next_reg); //add to known variables.
      }
    } else {
      // No pattern binder
      next_out.0 += 1;
      add_new_pattern(self);
    }

    while let Some(((id, reg), node)) = self.next() {
      if self.is_ground_now(id) && !node.is_leaf() {
        let extracted = private_extract(pattern, id);
        self.instructions.push(Instruction::Lookup {
          i: reg,
          term: extracted
            .iter()
            .map(|n| match n {
              ENodeOrVar::ENode(n) => ENodeOrReg::ENode(n.clone()),
              ENodeOrVar::Var(v) => ENodeOrReg::Reg(self.v2r[v]),
            })
            .collect(),
        });
      } else {
        let out = next_out;
        next_out.0 += node.len() as u32;

        // zero out the children so Bind can use it to sort
        let op = node.clone().map_children(|_| Id::from(0));
        self.instructions.push(Instruction::Bind { i: reg, node: op, out });

        for (i, &child) in node.children().iter().enumerate() {
          self.add_todo(pattern, child, Reg(out.0 + i as u32));
        }
      }
    }
    self.next_reg = next_out;
  }

  fn extract(self) -> Program {
    let mut subst = Subst::default();
    for (v, r) in self.v2r {
      subst.insert(v, Id::from(r.0 as usize));
    }
    Program { instructions: self.instructions, subst }
  }
}

impl Program {
  pub(crate) fn compile_from_pat(pattern: &PatternAst<ENode>) -> Self {
    let mut compiler = Compiler::new();
    compiler.compile(None, pattern);
    let program = compiler.extract();
    program
  }

  pub(crate) fn compile_from_multi_pat(patterns: &[(Var, PatternAst<ENode>)]) -> Self {
    let mut compiler = Compiler::new();
    for (var, pattern) in patterns {
      compiler.compile(Some(*var), pattern);
    }
    compiler.extract()
  }

  pub fn run_with_limit<S: Deref<Target=VersionedEGraph>>(
    &self,
    egraph: &Projection<S>,
    eclass: Id,
    mut limit: usize,
  ) -> Vec<Subst> {
    assert!(egraph.is_clean(), "Tried to search a dirty e-graph!");

    if limit == 0 {
      return vec![];
    }

    let mut machine = Machine::default();
    assert_eq!(machine.reg.len(), 0);
    machine.reg.push(eclass);

    let mut matches: Vec<Subst> = Vec::new();
    machine
      .run(egraph, &self.instructions, &self.subst, &mut |machine, subst| {
        // CHANGED we don't need this
        // if !egraph.analysis.allow_ematching_cycles() {
        //   if let Some((first, rest)) = machine.reg.split_first() {
        //     if rest.contains(first) {
        //       return Ok(());
        //     }
        //   }
        // }

        let subst_vec_private = unsafe {
          std::mem::transmute::<&Subst, &smallvec::SmallVec<[(Var, Id); 3]>>(subst)
        };
        let subst_vec = subst_vec_private
          .iter()
          // HACK we are reusing Ids here, this is bad
          .map(|(v, reg_id)| (*v, machine.reg(Reg(usize::from(*reg_id) as u32))))
          .collect();
        let subst_private = unsafe {
          std::mem::transmute::<smallvec::SmallVec<[(Var, Id); 3]>, Subst>(subst_vec)
        };
        matches.push(subst_private);
        limit -= 1;
        if limit != 0 {
          Ok(())
        } else {
          Err(())
        }
      })
      .unwrap_or_default();
    matches
  }
}

struct ProgramInspector {
  ast: PatternAst<ENode>,
  program: Program,
}
impl ProgramInspector {
  pub fn inspect(pattern: &Pattern<ENode>) -> &ProgramInspector {
    unsafe { std::mem::transmute::<&Pattern<ENode>, &ProgramInspector>(pattern) }
  }
}

pub trait CanEMatch<L: Language, S: Deref<Target=VersionedEGraph>> {
  fn ematch(&self, egraph: &Projection<S>) -> Vec<SearchMatches<L>>;
}
impl<S: Deref<Target=VersionedEGraph>> CanEMatch<ENode, S> for Pattern<ENode> {
  fn ematch(&self, egraph: &Projection<S>) -> Vec<SearchMatches<ENode>> {
    let mut ms = vec![];
    for &eclass in egraph.canonicals() {
      let inspector = ProgramInspector::inspect(self);
      let substs = inspector.program.run_with_limit(egraph, eclass, usize::MAX);
      if !substs.is_empty() {
        let ast = Some(std::borrow::Cow::Borrowed(&inspector.ast));
        let m = SearchMatches { eclass, substs, ast };
        ms.push(m)
      };
    }
    ms
  }
}

pub trait CanBind<S: DerefMut<Target=VersionedEGraph>> {
  fn bind(&self, egraph: &mut Projection<S>, eclass: Id, subst: &Subst) -> Vec<Id>;
}
impl<S: DerefMut<Target=VersionedEGraph>> CanBind<S> for Pattern<ENode> {
  fn bind(&self, egraph: &mut Projection<S>, eclass: Id, subst: &Subst) -> Vec<Id> {
    let mut ids = vec![0.into(); self.ast.len()];
    for (i, pat_node) in self.ast.iter().enumerate() {
      let id = match pat_node {
        ENodeOrVar::Var(w) => subst[*w],
        ENodeOrVar::ENode(e) => {
          let n = e.clone().map_children(|child| ids[usize::from(child)]);
          egraph.add(n)
        },
      };
      ids[i] = id;
    }
    let id = *ids.last().unwrap();

    if eclass == id {
      vec![]
    } else {
      vec![id]
    }
  }
}
