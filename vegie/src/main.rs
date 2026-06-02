// #![allow(warnings)]
mod lang;

use crate::lang::ast::{Command};
use crate::lang::parser::{Parser};
use crate::lang::eval::{eval, Env};
use crate::lang::prover::{Prover};


fn main() {

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
            println!("=== DEBUG ===");
            println!("lhs: {}, rhs: {}", prover.lhs.0, prover.rhs.0);
            prover.egraph.visualise_proof_graph(&prover.ctx);

            println!("{}", prover.explain());
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
