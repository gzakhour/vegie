pub enum SearchPattern {
  MetaVar(u8),
  Var(VarId),
  Cons(IdentId, Vec<SearchPattern>),
  App(IdentId, Vec<SearchPattern>),
  Case(Box<SearchPattern>, Vec<(PatternId, SearchPattern)>),
}

pub type Bindings = BTreeMap<u8, ENodeId>;

impl VEGraph {

  fn search<F>(&mut self, pattern: SearchPattern) -> Vec<Bindings> {

    fn aux(
      egraph: &mut VEGraph,
      enodes: &BTreeSet<ENodeId>,
      eclass: ENodeId,
      pat: SearchPattern,
      bindings: &mut Bindings,
    ) -> Vec<Bindings> {
      use SearchPattern::*;
      /*
      match pat {
        MetaVar(x) => todo!(),
        Var(id) => todo!(),
        Cons(id, args) => {
          let mut result = vec![];
          for enode in {
            todo!()
          }
          return result;
        },
        App(id, args) => todo!(),
        Case(scrutinee, arms) => todo!(),
      }
      */
      todo!()
    }

    todo!()
  }

}

