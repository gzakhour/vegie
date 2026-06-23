use std::iter::{Peekable};
use std::collections::{BTreeSet};

use crate::lang::tokenizer::{Token, WithLoc, Tokenizer};
use crate::lang::ast::{Id, TypeId, IdentId};
use crate::lang::ast::{Constructor, Pattern, Expr, Command};
use crate::lang::ctx::{Ctx, NameCtx, TypeInfo};


#[derive(Debug)]
pub struct ParseError {
  token: WithLoc<Token>,
  message: String,
  ctx: String,
}


#[derive(Eq,PartialEq,Ord,PartialOrd,Clone)]
enum PatternType { Var(TypeId), App(IdentId, Vec<PatternType>) }

impl PatternType {
  fn expand(typ: &TypeId, ctx: &Ctx) -> Vec<PatternType> {{{
    let mut result = vec![];
    for Constructor { name, args } in &ctx.datatypes[typ] {
      result.push(PatternType::App(name.clone(), args.iter().map(|a| PatternType::Var(a.clone())).collect()));
    }
    result
  }}}

  fn minus(&self, ctx: &Ctx, arg: &Pattern) -> Vec<PatternType> {{{
    match arg {
      Pattern::Var(_) => vec![],
      Pattern::App(k1, args1) => match self {
        PatternType::App(k2, args2) => {
          if k1 == k2 && args1.len() == args2.len() {
            // the minus of each arg, flattened
            let mut parts = vec![];
            for i in 0 .. args1.len() {
              for part in args2[i].minus(ctx, &args1[i]) {
                parts.push((i, part));
              }
            }
            // at the end there's as many missing cases as the flattened one.
            let mut result = vec![];
            for (i, part) in parts {
              result.push(PatternType::App(k2.clone(), {
                let mut args = vec![];
                for j in 0 .. args1.len() {
                  args.push(if i == j { part.clone() } else { args2[j].clone() });
                }
                args
              }));
            }
            result
          } else { vec![ self.clone() ] }
        },
        PatternType::Var(typ) => {
          Self::expand(typ, ctx).into_iter().flat_map(|pt| pt.minus(ctx, arg)).collect()
        }
      },
    }
  }}}

  fn missing_cases(ctx: &Ctx, typ: TypeId, patterns: &Vec<&Pattern>) -> Vec<PatternType> {{{
    use PatternType::*;
    let mut missing = vec![ Var(typ) ];
    for pat in patterns {
      let mut result = vec![];
      while let Some(miss) = missing.pop() {
        result.extend(miss.minus(ctx, pat));
      }
      missing = result;
    }
    missing
  }}}

  fn to_string(&self, ctx: &Ctx) -> String {{{
    match self {
      PatternType::Var(_) => "_".to_string(),
      PatternType::App(k, args) =>
        if args.len() == 0 {
          ctx.idents.as_str(k).to_string()
        } else {
          let mut result = "(".to_string();
          result.push_str(ctx.idents.as_str(k));
          for arg in args {
            result.push(' ');
            result.push_str(&arg.to_string(ctx));
          }
          result.push(')');
          result
        }
    }
  }}}

  fn contains(&self, other: &PatternType) -> bool {{{{
    use PatternType::*;
    match (self, other) {
      (Var(_), _) => true,
      (_, Var(_)) => false,
      (App(k1, args1), App(k2, args2)) =>
        k1 == k2 && args1.len() == args2.len() &&
          args1.iter().zip(args2).all(|(a1,a2)| a1.contains(a2))
    }
  }}}}

  fn minimize(ps: &Vec<PatternType>) -> Vec<PatternType> {{{
    let mut min: Vec<PatternType> = vec![];
    'outer: for p in ps {
      let mut to_remove = vec![];
      for (i, m) in min.iter().enumerate() {
        if m.contains(p) { continue 'outer; }
        if p.contains(m) { to_remove.push(i); }
      }
      for i in to_remove.into_iter().rev() {
        min.swap_remove(i);
      }
      min.push(p.clone());
    }
    min
  }}}

  fn intersect(p1: &Pattern, p2: &Pattern) -> bool {//{{{
    use Pattern::*;
    match (p1, p2) {
      (Var(_), _) | (_, Var(_)) => true,
      (App(k1, ps1), App(k2, ps2)) =>
        k1 == k2 && ps1.len() == ps2.len() &&
          ps1.iter().zip(ps2).all(|(p1, p2)| Self::intersect(p1, p2))
    }
  }//}}}
}




fn parse_constructor<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, dt: TypeId) -> Result<Constructor, ParseError> {//{{{
  let token = tokens.peek().unwrap();
  if token.data.is_ident() {
    let (_, name) = parse_new_name(tokens, &mut ctx.idents, "constructor name")?;
    ctx.type_info.insert(name.clone(), TypeInfo { dom: vec![], codom: dt, constructor: true });
    Ok(Constructor { name, args: vec![] })
  } else if token.data == Token::OParen {
    let _ = tokens.next(); // oparen
    let (_, name) = parse_new_name(tokens, &mut ctx.idents, "constructor name")?;
    let mut args = vec![];
    while tokens.peek().unwrap().data != Token::CParen {
      args.push(parse_existing_name(tokens, &mut ctx.types, "constructor argument")?.1);
    }
    let _ = tokens.next(); // cparen
    ctx.type_info.insert(name.clone(), TypeInfo { dom: args.clone(), codom: dt, constructor: true });
    Ok(Constructor { name, args })
  } else {
    let token = tokens.next().unwrap();
    return Err(ParseError {
      token, ctx: "constructor definition".to_string(), message: "Expected ( or identifier".to_string()
    })
  }
}//}}}

fn parse_pattern<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, typ: TypeId) -> Result<(Vec<String>, Pattern), ParseError> {//{{{
  let first = tokens.peek().unwrap();
  let f = first.clone();
  if first.data.is_ident() {
    let (name, id) = parse_existing_name(tokens, &mut ctx.idents, "argument")?;
    let tinfo = &ctx.type_info[&id];
    if !tinfo.constructor {
      return Err(ParseError {
        token: f,
        ctx: "argument".to_string(),
        message: format!("{name} is not a constructor")
      });
    }
    if tinfo.dom.len() > 0 {
      return Err(ParseError {
        token: f,
        ctx: "argument".to_string(),
        message: format!("{name} takes {} arguments but 0 given", tinfo.dom.len())
      });
    }
    if tinfo.codom != typ {
      return Err(ParseError {
        token: f,
        ctx: "argument".to_string(),
        message: format!("{name} constructs a {} but {} expected",
          ctx.types.as_str(&tinfo.codom), ctx.types.as_str(&typ))
      });
    }
    Ok((vec![], Pattern::App(id, vec![])))
  } else if first.data.is_var() {
    let token = tokens.next().unwrap();
    let name = token.data.get_var().unwrap();
    let new_name = ctx.scoped.push(&name);
    let id = ctx.vars.get(&new_name);
    ctx.var_types.insert(id.clone(), typ);
    Ok((vec![ name.to_string() ], Pattern::Var(id)))
  } else if first.data == Token::OParen {
    let _ = tokens.next(); // oparen
    let (name, id) = parse_existing_name(tokens, &mut ctx.idents, "argument")?;
    let tinfo = &ctx.type_info[&id];
    if !tinfo.constructor {
      return Err(ParseError {
        token: f,
        ctx: "argument".to_string(),
        message: format!("{name} is not a constructor"),
      });
    }
    if tinfo.codom != typ {
      return Err(ParseError {
        token: f,
        ctx: "argument".to_string(),
        message: format!("{name} constructs a {} but {} expected",
          ctx.types.as_str(&tinfo.codom), ctx.types.as_str(&typ))
      });
    }
    let mut args = vec![];
    let mut names = vec![];
    for i in 0 .. tinfo.dom.len() {
      let (arg_names, arg) = parse_pattern(tokens, ctx, ctx.type_info[&id].dom[i].clone())?;
      args.push(arg);
      names.extend(arg_names);
    }
    if tokens.next().unwrap().data != Token::CParen {
      return Err(ParseError {
        token: f,
        ctx: "end of arguments".to_string(),
        message: format!("expected )")
      });
    }
    Ok((names, Pattern::App(id, args)))
  } else {
    Err(ParseError {
      token: tokens.next().unwrap(),
      ctx: "argument".to_string(),
      message: "Expected variable or constructor constant or application".to_string()
    })
  }
}//}}}


fn parse_expr_ident<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, typ: Option<TypeId>, f: WithLoc<Token>, start: usize) -> Result<(WithLoc<Expr>, TypeId), ParseError> {//{{{
  let (name, id) = parse_existing_name(tokens, &mut ctx.idents, "expression")?;
  if ctx.type_info[&id].dom.len() > 0 {
    return Err(ParseError {
      token: f, ctx: "identifier".to_string(),
      message: format!("{name} expects {} arguments but 0 given",
        ctx.type_info[&id].dom.len())
    });
  }
  if let Some(typ) = typ {
    if ctx.type_info[&id].codom != typ {
      return Err(ParseError {
        token: f, ctx: "identifier".to_string(),
        message: format!("Expected {} but {name} is {}",
          ctx.types.as_str(&typ), ctx.types.as_str(&ctx.type_info[&id].codom))
      });
    }
  }
  let typ = ctx.type_info[&id].codom.clone();
  Ok((WithLoc::from(start,
    if ctx.type_info[&id].constructor { Expr::Cons(id, vec![]) } else { Expr::App(id, vec![]) }
  ), typ))
}//}}}

fn parse_expr_var<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, typ: Option<TypeId>, start: usize) -> Result<(WithLoc<Expr>, TypeId), ParseError> {//{{{
  let token = tokens.next().unwrap();
  let name = token.data.get_var().unwrap();
  if let Some(actual_name) = ctx.scoped.get(name) {
    let id = ctx.vars.get(&actual_name);
    if let Some(typ) = typ {
      if ctx.var_types[&id] != typ {
        return Err(ParseError {
          token: token.clone(), ctx: "variable".to_string(),
          message: format!("Expected {} but {name} is {}",
            ctx.types.as_str(&typ), ctx.types.as_str(&ctx.var_types[&id]))
        })
      }
    }
    let typ = ctx.var_types[&id].clone();
    Ok((WithLoc::from(start, Expr::Var(id)), typ))
  } else {
    Err(ParseError {
      ctx: "expression variable".to_string(),
      message: format!("{name} is not bound"),
      token,
    })
  }
}//}}}

fn parse_expr_case<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, typ: Option<TypeId>, start: usize) -> Result<(WithLoc<Expr>, TypeId), ParseError> {//{{{
  let case_token = tokens.next();
  let (scrutinee, scrutinee_type) = parse_expr(tokens, ctx, None)?;
  let mut arms = vec![];
  let mut result_type = typ.clone();
  let mut arm_i = 0;

  while tokens.peek().unwrap().data != Token::CParen {
    arm_i += 1;
    let oparen = tokens.next().unwrap();
    if oparen.data != Token::OParen {
      return Err(ParseError {
        token: oparen,
        ctx: "case arm".to_string(),
        message: "each case must be in parenthesis".to_string(),
      })
    }
    let (arg_names, arg) = parse_pattern(tokens, ctx, scrutinee_type.clone())?;
    for (arm_j, (other_arg, _)) in arms.iter().enumerate() {
      if PatternType::intersect(other_arg, &arg) {
        return Err(ParseError {
          token: oparen,
          ctx: "case overlap".to_string(),
          message: format!("Case {} and case {arm_i} overlap", arm_j+1),
        })
      }
    }
    let (arm, arm_type) = parse_expr(tokens, ctx, typ.clone())?;
    if let Some(typ) = &result_type {
      if *typ != arm_type {
        return Err(ParseError {
          token: case_token.unwrap(),
          ctx: format!("case {arm_i}"),
          message: format!("previous cases return {} but case {arm_i} returns {}",
            ctx.types.as_str(typ), ctx.types.as_str(&arm_type))
        })
      }
    } else {
      result_type = Some(arm_type);
    }
    if tokens.next().unwrap().data != Token::CParen {
      return Err(ParseError {
        token: oparen,
        ctx: "case arm".to_string(),
        message: "missing closed parenthesis".to_string(),
      })
    }
    for name in arg_names { ctx.scoped.pop(&name); }
    arms.push((arg, arm.data));
  }
  let _ = tokens.next(); // cparen

  let missing = PatternType::minimize(&PatternType::missing_cases(&ctx, scrutinee_type, &arms.iter().map(|(a,_)| a).collect()));
  if missing.len() > 0 {
    return Err(ParseError {
      token: case_token.unwrap(),
      ctx: "case expression".to_string(),
      message: format!("uncovered cases: {}", missing.iter().map(|a| a.to_string(ctx)).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>().join(", ")),
    })
  }

  Ok((WithLoc::from(start, Expr::Case(Box::new(scrutinee.data), arms)), result_type.unwrap()))
}//}}}

fn parse_expr_app<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, typ: Option<TypeId>, f: WithLoc<Token>, start: usize) -> Result<(WithLoc<Expr>, TypeId), ParseError> {//{{{
  let (name, id) = parse_existing_name(tokens, &mut ctx.idents, "expression")?;
  if let Some(typ) = typ {
    if ctx.type_info[&id].codom != typ {
      return Err(ParseError {
        token: f,
        ctx: "function application".to_string(),
        message: format!("Expected {} but {name} returns {}",
          ctx.types.as_str(&typ), ctx.types.as_str(&ctx.type_info[&id].codom))
      })
    }
  }
  let mut args = vec![];
  for i in 0 .. ctx.type_info[&id].dom.len() {
    args.push(parse_expr(tokens, ctx, Some(ctx.type_info[&id].dom[i].clone()))?.0.data);
  }
  let t = tokens.next().unwrap();
  if t.data != Token::CParen {
    return Err(ParseError {
      token: t,
      ctx: "function arguments".to_string(),
      message: "Expected )".to_string()
    })
  }
  let typ = ctx.type_info[&id].codom.clone();
  Ok((WithLoc::from(start,
    if ctx.type_info[&id].constructor { Expr::Cons(id, args) } else { Expr::App(id, args) }), typ))
}//}}}

fn parse_expr<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, typ: Option<TypeId>) -> Result<(WithLoc<Expr>, TypeId), ParseError> {//{{{
  let first = tokens.peek().unwrap();
  let f = first.clone();
  let start = first.index;
  if first.data.is_ident() {
    parse_expr_ident(tokens, ctx, typ, f, start)
  } else if first.data.is_var() {
    parse_expr_var(tokens, ctx, typ, start)
  } else if first.data == Token::OParen {
    let _ = tokens.next(); // oparen
    if tokens.peek().unwrap().data == Token::Case {
      parse_expr_case(tokens, ctx, typ, start)
    } else {
      parse_expr_app(tokens, ctx, typ, f, start)
    }
  } else {
    Err(ParseError {
      token: tokens.next().unwrap(),
      ctx: "argument".to_string(),
      message: "Expected variable or constructor constant or application".to_string()
    })
  }
}//}}}


fn parse_name<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &'static str) -> Result<(String, WithLoc<Token>), ParseError> {//{{{
  let token = tokens.next().unwrap();
  let ctx = ctx.to_string();
  if !token.data.is_ident() {
    return Err(ParseError {
      token, ctx,
      message: format!("expected an identifier"),
    })
  }
  Ok((token.data.get_ident().unwrap().to_string(), token))
}//}}}

fn parse_new_name<'a, T: Id>(tokens: &mut Peekable<Tokenizer<'a>>, name_ctx: &mut NameCtx<T>, ctx: &'static str) -> Result<(String, T), ParseError> {//{{{
  let (val, token) = parse_name(tokens, ctx)?;
  if name_ctx.contains(&val) {
    return Err(ParseError {
      message: format!("{val} was already defined"),
      token, ctx: ctx.to_string(),
    })
  }
  let id = name_ctx.get(&val);
  Ok((val, id))
}//}}}

fn parse_existing_name<'a, T: Id>(tokens: &mut Peekable<Tokenizer<'a>>, name_ctx: &mut NameCtx<T>, ctx: &'static str) -> Result<(String, T), ParseError> {//{{{
  let (val, token) = parse_name(tokens, ctx)?;
  if !name_ctx.contains(&val) {
    return Err(ParseError {
      message: format!("{val} was never defined"),
      token, ctx: ctx.to_string(),
    })
  }
  let id = name_ctx.get(&val);
  Ok((val, id))
}//}}}


fn parse_cmd_datatype<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx) -> Result<Command, ParseError> {//{{{
  let (_, name) = parse_new_name(tokens, &mut ctx.types, "datatype name")?;
  let mut constructors = vec![];
  while tokens.peek().unwrap().data != Token::CParen {
    constructors.push(parse_constructor(tokens, ctx, name.clone())?);
  }
  Ok(Command::DatatypeDecl { name, constructors, })
}//}}}

fn parse_cmd_type<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, token: WithLoc<Token>) -> Result<Command, ParseError> {//{{{
  let (_, name) = parse_new_name(tokens, &mut ctx.idents, "function name")?;

  let oparen = tokens.next().unwrap();
  if oparen.data != Token::OParen {
    return Err(ParseError {
      token,
      ctx: "definition type signature".to_string(),
      message: "Expected ( or identifier".to_string(),
    })
  }

  let mut dom = vec![];
  while tokens.peek().unwrap().data != Token::CParen {
    dom.push(parse_existing_name(tokens, &mut ctx.types, "function argument type")?.1);
  }
  let _ = tokens.next(); // cparen
  let (_, codom) = parse_existing_name(tokens, &mut ctx.types, "function return type")?;
  ctx.type_info.insert(name.clone(), TypeInfo { dom: dom.clone(), codom: codom.clone(), constructor: false });
  Ok(Command::TypeDecl { name, codom, dom })
}//}}}

fn parse_cmd_def<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, token: WithLoc<Token>) -> Result<Command, ParseError> {//{{{
  let (func_name, name) = parse_existing_name(tokens, &mut ctx.idents, "definition name")?;

  if ctx.defs.contains_key(&name) {
    return Err(ParseError {
      token,
      ctx: "definition".to_string(),
      message: format!("{func_name} has already been defined"),
    })
  }

  let oparen = tokens.next().unwrap();
  if oparen.data != Token::OParen {
    return Err(ParseError {
      token: oparen,
      ctx: "definition argument".to_string(),
      message: "Expected (".to_string(),
    })
  }

  let mut args = vec![];
  let mut names = vec![];

  for i in 0 .. ctx.type_info[&name].dom.len() {
    let arg = tokens.next().unwrap();
    if !arg.data.is_var() {
      return Err(ParseError {
        token: arg,
        ctx: "function argument".to_string(),
        message: "Expected variable".to_string(),
      });
    }
    let arg_name = arg.data.get_var().unwrap().clone();
    let new_name = ctx.scoped.push(&arg_name);
    let arg = ctx.vars.get(&new_name);
    ctx.var_types.insert(arg.clone(), ctx.type_info[&name].dom[i].clone());
    names.push(arg_name);
    args.push(arg);
  }

  if tokens.next().unwrap().data != Token::CParen {
    return Err(ParseError {
      token,
      ctx: "definition arguments".to_string(),
      message: "Expected )".to_string(),
    })
  }

  let body = parse_expr(tokens, ctx, Some(ctx.type_info[&name].codom.clone()))?.0;
  for name in names { ctx.scoped.pop(&name); }
  Ok(Command::Def { name, body, args })
}//}}}

fn parse_cmd_theorem<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx, is_axiom: bool) -> Result<Command, ParseError> {//{{{
  let (_, name) = parse_new_name(tokens, &mut ctx.theorems, "theorem name")?;
  let mut args = vec![];
  let mut names = vec![];
  let token = tokens.next().unwrap();
  if token.data != Token::OParen {
    return Err(ParseError {
      token,
      ctx: "theorem name".to_string(),
      message: "Expected (".to_string(),
    })
  }
  while tokens.peek().unwrap().data != Token::CParen {
    let oparen = tokens.next().unwrap();
    if oparen.data != Token::OParen {
      return Err(ParseError {
        token: oparen,
        ctx: "theorem argument".to_string(),
        message: "theorem argument is a pair of variable and type".to_string()
      })
    }
    let token = tokens.next().unwrap();
    if !token.data.is_var() {
      return Err(ParseError {
        token,
        ctx: "theorem argument".to_string(),
        message: "Expected variable".to_string(),
      });
    }
    let (_, arg_typ) = parse_existing_name(tokens, &mut ctx.types, "theorem argument")?;
    let cparen = tokens.next().unwrap();
    if cparen.data != Token::CParen {
      return Err(ParseError {
        token: cparen,
        ctx: "theorem argument".to_string(),
        message: "Expected )".to_string()
      })
    }
    let name = token.data.get_var().unwrap().clone();
    let new_name = ctx.scoped.push(&name);
    let arg = ctx.vars.get(&new_name);
    ctx.var_types.insert(arg.clone(), arg_typ);
    names.push(name);
    args.push(arg);
  }
  let _ = tokens.next(); // cparen
  let lhs = parse_expr(tokens, ctx, None)?;
  let rhs = parse_expr(tokens, ctx, Some(lhs.1))?;
  for name in names { ctx.scoped.pop(&name); }
  ctx.theorem_stmts.insert(name.clone(), (args.clone(), lhs.0.data.clone(), rhs.0.data.clone()));
  let name = WithLoc::from(token.index, name);
  Ok(Command::Theorem { name, args, lhs: lhs.0.data, rhs: rhs.0.data, is_assumed: is_axiom })
}//}}}

fn parse_cmd<'a>(tokens: &mut Peekable<Tokenizer<'a>>, ctx: &mut Ctx) -> Result<Command, ParseError> {//{{{
  let token = tokens.next().unwrap();
  if token.data != Token::OParen {
    return Err(ParseError {
      token, ctx: "command".to_string(), message: "Commands must start with (".to_string()
    })
  }

  let token = tokens.next().unwrap();

  let ans = match token.data {
    Token::Type => parse_cmd_type(tokens, ctx, token)?,
    Token::Def => {
      let def = parse_cmd_def(tokens, ctx, token)?;
      if let Command::Def { name, args, body } = &def {
        ctx.defs.entry(name.clone()).or_insert((args.clone(), body.data.clone()));
      }
      def
    },
    Token::Datatype => {
      let datatype = parse_cmd_datatype(tokens, ctx)?;
      if let Command::DatatypeDecl { name, constructors } = &datatype {
        ctx.datatypes.insert(name.clone(), constructors.clone());
      }
      datatype
    },
    Token::Theorem => parse_cmd_theorem(tokens, ctx, false)?,
    Token::Axiom => parse_cmd_theorem(tokens, ctx, true)?,
    Token::Eval => {
      let (expr, typ) = parse_expr(tokens, ctx, None)?;
      Command::Eval { expr, typ }
    },
    _ => {
      let message = format!("Unexpected {} while parsing command. Commands must be one of `datatype`, `type`, `def`, `theorem`, `axiom`, or `eval`", token.data);
      return Err(ParseError { ctx: "command".to_string(), token, message })
    }
  };

  let token = tokens.next().unwrap();
  if let Token::CParen = token.data {
    Ok(ans)
  } else {
    Err(ParseError {
      token,
      ctx: "command".to_string(),
      message: "Unclosed command, expected )".to_string()
    })
  }
}//}}}




pub struct Parser<'a> {
  pub ctx: Ctx,
  tokens: Peekable<Tokenizer<'a>>,
  contents: &'a Vec<char>,
}

impl<'a> Parser<'a> {
  pub fn from(contents: &'a Vec<char>) -> Parser<'a> {
    Parser {
      ctx: Ctx::new(),
      tokens: Tokenizer::from(contents).peekable(),
      contents
    }
  }

  pub fn next(&mut self) -> Result<Command, ParseError> {
    parse_cmd(&mut self.tokens, &mut self.ctx)
  }

  pub fn has_more(&mut self) -> bool {
    self.tokens.peek().unwrap().data != Token::EOF
  }

  pub fn show_err(&self, err: &ParseError, file: &String) {
    let (line, col) = err.token.line_col(self.contents);
    let ctx = &err.ctx;
    let message = &err.message;
    eprintln!("\x1b[31merror\x1b[0m:{file}:{line}:{col}: while parsing {ctx}, at {}: {message}", err.token.data);
  }
}
