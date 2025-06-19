use std::fmt;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenType {
  Nil,
  True,
  False,
  Let,
  Ident,
  String,
  Int,
  Float,
  Bang,
  Assign,
  Plus,
  Minus,
  Slash,
  Asterisk,
  Function,
  LParen,
  RParen,
  LBrace,
  RBrace,
  If,
  Else,
  Eq,
  NotEq,
  LessThan,
  GreaterThan,
  Comma,
  Semicolon,
  Return,
  Eof,
  Invalid,
}

impl fmt::Display for TokenType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let token_str = match self {
      Self::Nil => "NIL",
      Self::True => "BOOLEAN",
      Self::False => "BOOLEAN",
      Self::Let => "LET",
      Self::Ident => "IDENTIFIER",
      Self::String => "STRING",
      Self::Int => "INTEGER",
      Self::Float => "FLOAT",
      Self::Bang => "BANG",
      Self::Assign => "ASSIGN",
      Self::Plus => "PLUS",
      Self::Minus => "MINUS",
      Self::Slash => "SLASH",
      Self::Asterisk => "ASTERISK",
      Self::Function => "FUNCTION",
      Self::LParen => "LPAREN",
      Self::RParen => "RPAREN",
      Self::LBrace => "LBRACE",
      Self::RBrace => "RBRACE",
      Self::If => "IF",
      Self::Else => "ELSE",
      Self::Eq => "EQUALS",
      Self::NotEq => "NOT_EQUALS",
      Self::LessThan => "LESS_THAN",
      Self::GreaterThan => "GREATER_THAN",
      Self::Comma => "COMMA",
      Self::Semicolon => "SEMICOLON",
      Self::Return => "RETURN",
      Self::Eof => "EOF",
      Self::Invalid => "TOKEN",
    };
    write!(f, "{}", token_str)
  }
}

impl From<&str> for TokenType {
  fn from(value: &str) -> Self {
    match value {
      "nil" => Self::Nil,
      "true" => Self::True,
      "false" => Self::False,
      "let" => Self::Let,
      "fn" => Self::Function,
      "if" => Self::If,
      "else" => Self::Else,
      "return" => Self::Return,
      _ => Self::Ident,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
  token_type: TokenType,
  literal: String,
}

impl Token {
  pub fn new(tt: TokenType, literal: &str) -> Self {
    Self {
      token_type: tt,
      literal: literal.to_string(),
    }
  }

  pub fn token_type(&self) -> TokenType {
    self.token_type
  }

  pub fn literal(&self) -> &str {
    &self.literal
  }
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.token_type {
      TokenType::Eof => self.token_type.fmt(f),
      TokenType::String => write!(f, "{}", self.token_type),
      _ => write!(f, "{}({})", self.token_type, self.literal),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn is_normal<T: Sized + Send + Sync + Unpin>() {}

  #[test]
  fn token_normal_types() {
    is_normal::<TokenType>();
    is_normal::<Token>();
  }
}
