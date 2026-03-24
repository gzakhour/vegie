// #![allow(warnings)]
// mod egraph;
mod lang;
mod util;

// use crate::egraph::aliases::{*};
// use crate::egraph::version_egraph::{*};
// use egg::{Pattern};

use crate::lang::ast::{Command};
use crate::lang::parser::{Parser};
use crate::lang::eval::{eval, Env};
use crate::lang::prover::{Prover};


fn main() {

  {
    use std::fs::{File};
    use std::io::{Read, BufReader};
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() < 2 {
      eprintln!("Usage: {} file", args[0]);
      std::process::exit(-1);
    }
    let filename = args[1].clone();
    let file = File::open(&filename).unwrap();
    let mut buf_reader = BufReader::new(file);
    let mut contents = String::new();
    buf_reader.read_to_string(&mut contents).unwrap();
    let contents = contents.chars().collect::<Vec<_>>();

    let mut parser = Parser::from(&contents);
    while parser.has_more() {
      match parser.next() {
        Ok(cmd) => match cmd {

          Command::Theorem  { name, is_assumed: true, .. } => {
            let (line, _) = name.line_col(&contents);
            let name = name.data;
            let axiom_name = parser.ctx.theorems.as_str(&name).to_string();
            println!("\x1b[33maxiom\x1b[0m:{filename}:{line}: {}: {axiom_name}", name.0);
            parser.ctx.proven_theorem.insert(name);
          },

          Command::Theorem  { name, is_assumed: false, .. } => {
            let (line, _) = name.line_col(&contents);
            let name = name.data;
            let theorem_name = parser.ctx.theorems.as_str(&name).to_string();

            let mut prover = Prover::from(&mut parser.ctx, name);
            prover.proof_iter();
            prover.proof_iter();
            prover.proof_iter();
            prover.proof_iter();
            prover.proof_iter();
            prover.proof_iter();
            // prover.dump(&format!("/tmp/proof-{theorem_name}.log"));

            let (code, state) =
              if prover.is_true() { (32, "true") }
              else if prover.is_false() { (31, "false") }
              else { (33, "unknown") };
            println!("\x1b[{code}mtheorem\x1b[0m:{filename}:{line}: {theorem_name} is {state}");
            if code == 32 {
              println!("{}", prover.explain());
              // prover.egraph.visualise_proof_graph(&prover.ctx);
              parser.ctx.proven_theorem.insert(name);
            }
          },

          Command::Eval { expr, typ, } => {
            let (line, _) = expr.line_col(&contents);
            let expr = eval(&expr.data, &parser.ctx, Env::Empty.into());
            println!("\x1b[34meval\x1b[0m:{filename}:{line}: {} :: {}",
              expr.to_string(&parser.ctx),
              parser.ctx.types.as_str(&typ));
          }

          _ => {}
        },
        Err(err) => {
          parser.show_err(&err, &filename);
          break;
        }
      }
    }
  }


  // if false {
  //   let mut _egraph = VersionedEGraph::with_ematching_caches(1);

  //   let mut egraph = _egraph.project_mut(crate::egraph::version_tree::VersionTree::ROOT_VERSION);

  //   let [_0, _1, _2] = ["0", "1", "2"].map(|num| egraph.add(ENode::constant(SymbolIds::from_string(num))));
  //   let f: Operator = SymbolIds::from_string("f");
  //   let g: Operator = SymbolIds::from_string("g");
  //   let _f_0 = egraph.add(ENode::application(f, vec![_0]));
  //   let _f_1 = egraph.add(ENode::application(f, vec![_1]));
  //   let _f_2 = egraph.add(ENode::application(f, vec![_2]));

  //   egraph.union(_0, _f_0);

  //   let pattern = |s: &str| s.parse::<Pattern<ENode>>().unwrap();

  //   let lhs = pattern("(f ?x)");
  //   let rhs = pattern("(g ?x)");

  //   egraph.run(
  //     &RunnerConfig::default(),
  //     &[
  //       ("hello".to_string(), lhs, rhs)
  //     ]
  //   );

  //   let g_0 = egraph.add(ENode::application(g, vec![_0]));
  //   println!("{:?}", egraph.find(_0) == egraph.find(g_0));
  // }
}
