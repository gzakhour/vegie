#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Token { OParen, CParen, Datatype, Type, Def, Theorem, Axiom, Eval, Case, Var(String), Ident(String), EOF, }

impl Token {
  pub fn is_ident(&self) -> bool {
    match self { Token::Ident(_) => true, _ => false }
  }

  pub fn get_ident(&self) -> Option<&String> {
    if let Token::Ident(v) = self { Some(v) } else { None }
  }

  pub fn is_var(&self) -> bool {
    match self { Token::Var(_) => true, _ => false }
  }

  pub fn get_var(&self) -> Option<&String> {
    if let Token::Var(v) = self { Some(v) } else { None }
  }
}

impl std::fmt::Display for Token {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    use Token::*;
    match self {
      OParen => write!(f, "("),
      CParen => write!(f, ")"),
      Datatype => write!(f, "`datatype`"),
      Type => write!(f, "`type`"),
      Def => write!(f, "`def`"),
      Theorem => write!(f, "`theorem`"),
      Axiom => write!(f, "`axiom`"),
      Eval => write!(f, "`eval`"),
      Case => write!(f, "`case`"),
      Var(x) | Ident(x) => write!(f, "{x}"),
      EOF => write!(f, "<EOF>"),
    }
  }
}

#[derive(Debug, Clone)]
pub struct WithLoc<T> {
  pub index: usize,
  pub data: T,
}

impl<T> WithLoc<T> {
  pub fn from(index: usize, data: T) -> WithLoc<T> {
    WithLoc { index, data }
  }

  pub fn line_col(&self, source: &Vec<char>) -> (usize, usize) {
    let mut line = 1;
    let mut col = 0;
    let mut i = 0;
    while i <= self.index {
      col += 1;
      if source[i] == '\n' { line += 1; col = 0; }
      i += 1;
    }
    (line, col)
  }
}

pub struct Tokenizer<'a> {
  data: &'a Vec<char>,
  index: usize,
}

impl<'a> Tokenizer<'a> {
  pub fn from(data: &'a Vec<char>) -> Tokenizer<'a> {
    Tokenizer { data, index: 0 }
  }
}

impl Tokenizer<'_> {
  fn peek(&self) -> char {
    if self.index < self.data.len() { self.data[self.index] }
    else { '\0' }
  }

  fn consume(&mut self) -> char {
    if self.index >= self.data.len() { return '\0' }
    let ans = self.data[self.index];
    self.index += 1;
    ans
  }

  fn skip_white(&mut self) {
    while self.index < self.data.len() {
      let c = self.data[self.index];
      if c == ';' {
        while self.index < self.data.len() {
          if self.peek() == '\n' { break; }
          self.index += 1;
        }
      } else if c.is_whitespace() {
        self.index += 1;
      } else {
        break;
      }
    }
  }
}

impl Iterator for Tokenizer<'_> {
  type Item=WithLoc<Token>;

  fn next(&mut self) -> Option<Self::Item> {
    fn is_special(c: char) -> bool {
      c.is_whitespace() || c == '(' || c == ')' || c == ';'
    }
    self.skip_white();
    let ans = Some(WithLoc::from(self.index, match self.consume() {
      '\0' => Token::EOF,
      '(' => Token::OParen,
      ')' => Token::CParen,
      c => {
        let mut value = String::new();
        value.push(c);
        while !is_special(self.peek()) { value.push(self.consume()); }
        if c == '?' {
          Token::Var(value)
        } else if value == "theorem" {
          Token::Theorem
        } else if value == "axiom" {
          Token::Axiom
        } else if value == "datatype" {
          Token::Datatype
        } else if value == "type" {
          Token::Type
        } else if value == "def" {
          Token::Def
        } else if value == "eval" {
          Token::Eval
        } else if value == "case" {
          Token::Case
        } else {
          Token::Ident(value)
        }
      }
    }));
    self.skip_white();
    ans
  }
}
