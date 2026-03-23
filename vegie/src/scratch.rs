#![allow(warnings)]

mod lang;
mod util;

use crate::lang::myegraph::{*};
use crate::lang::ast::{*};
use crate::lang::ctx::{*};

fn main() {

  let mut egraph = VEGraph::new();
  let mut ctx = Ctx::new();

  let f_id = ctx.idents.get(&"f".to_string());
  let g_id = ctx.idents.get(&"g".to_string());
  let a_id = ctx.idents.get(&"a".to_string());
  let b_id = ctx.idents.get(&"b".to_string());
  let c_id = ctx.idents.get(&"c".to_string());

  macro_rules! app {
  (f, $x1:expr, $x2:expr) => { Expr::App(f_id, vec![ $x1, $x2 ]) };
  (g, $x:expr) => { Expr::App(g_id, vec![ $x ]) };
  (a) => { Expr::App(a_id, vec![]) };
  (b) => { Expr::App(b_id, vec![]) };
  (c) => { Expr::App(c_id, vec![]) };
  };

  let a = egraph.add_expr(&app!(a), ROOT_VERSION);
  let b = egraph.add_expr(&app!(b), ROOT_VERSION);
  egraph.union(a, b, ROOT_VERSION, ProofEdge::Definition(a_id, true));

  let gc = egraph.add_expr(&app!(g, app!(c)), ROOT_VERSION);
  let c = egraph.add_expr(&app!(c), ROOT_VERSION);
  egraph.union(gc, c, ROOT_VERSION, ProofEdge::Definition(c_id, false));

  let src = egraph.add_expr(&app!(f, app!(a), app!(g, app!(c))), ROOT_VERSION);
  let dest = egraph.add_expr(&app!(f, app!(b), app!(c)), ROOT_VERSION);
  let proof = egraph.explain(src, dest, ROOT_VERSION);

  println!("src = {}", egraph.extract(src).to_string(&ctx));
  println!("dest = {}", egraph.extract(dest).to_string(&ctx));
  println!("proof = {}", proof.to_string(&ctx));

}
