// #![allow(warnings)]
mod lang;

use crate::lang::ast::{Command};
use crate::lang::parser::{Parser};
use crate::lang::eval::{eval, Env};
use crate::lang::prover::{Prover};


fn main() {

  use std::fs::{File, create_dir_all};
  use std::io::{Read, BufReader};
  use std::path::{Path};

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

  let proofs_dir = Path::new("out/proofs");
  let _ = create_dir_all(proofs_dir).unwrap();

  let dot_dir = Path::new("out/dot");
  let _ = create_dir_all(dot_dir).unwrap();

  let mut parser = Parser::from(&contents);
  while parser.has_more() {
    match parser.next() {
      Ok(cmd) => match cmd {

        Command::Theorem  { name, is_assumed: true, .. } => {
          let (line, _) = name.line_col(&contents);
          let name = name.data;
          let axiom_name = parser.ctx.theorems.as_str(&name).to_string();
          println!("\x1b[33maxiom\x1b[0m:{filename}:{line}: {axiom_name}");
          parser.ctx.proven_theorem.insert(name);
        },

        Command::Theorem  { name, is_assumed: false, .. } => {
          let (line, _) = name.line_col(&contents);
          let name = name.data;
          let theorem_name = parser.ctx.theorems.as_str(&name).to_string();

          print!("Attempting {theorem_name}");
          use std::io::Write;
          std::io::stdout().flush().unwrap();
          let mut prover = Prover::from(&mut parser.ctx, name);
          prover.proof_iter();
          prover.proof_iter();
          prover.proof_iter();
          prover.proof_iter();
          prover.proof_iter();
          // prover.proof_iter();
          // prover.proof_iter();
          // prover.dump(&format!("/tmp/proof-{theorem_name}.log"));
          print!("\r");

          let (code, state) =
            if prover.is_true() { (32, "true") }
            else if prover.is_false() { (31, "false") }
            else { (33, "unknown") };
          print!("\x1b[{code}mtheorem\x1b[0m:{filename}:{line}: {theorem_name} is {state}");
          std::io::stdout().flush().unwrap();

          // println!("=== DEBUG ===");
          // println!("lhs: {}, rhs: {}", prover.lhs.0, prover.rhs.0);
          // prover.egraph.visualise_proof_graph(name.0, &prover.ctx, prover.lhs);

          use std::fs;
          let _ = fs::write(dot_dir.join(&theorem_name).with_extension("dot"),
                            prover.egraph.visualise_proof_graph(name.0, &prover.ctx, prover.lhs, &prover.lhs, &prover.rhs));
          if code == 32 {
            let _ = fs::write(proofs_dir.join(&theorem_name), prover.explain());
            print!("... printing proof...");
            std::io::stdout().flush().unwrap();
            parser.ctx.proven_theorem.insert(name);
            println!(" done");
          } else { println!(""); }
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
