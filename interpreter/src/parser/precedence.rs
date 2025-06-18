use crate::lexer::token::TokenType;
use std::fmt;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Precedence {
  Lowest,
  Equals,
  LessGreater,
  Sum,
  Product,
  Prefix,
  Call,
}

impl fmt::Display for Precedence {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let precedence_str = match self {
      Self::Lowest => "LOWEST",
      Self::Equals => "EQUALS",
      Self::LessGreater => "LESS_GREATER",
      Self::Sum => "SUM",
      Self::Product => "PRODUCT",
      Self::Prefix => "PREFIX",
      Self::Call => "CALL",
    };
    write!(f, "{}({})", precedence_str, *self as u8)
  }
}

impl From<TokenType> for Precedence {
  fn from(value: TokenType) -> Self {
    match value {
      TokenType::Eq => Self::Equals,
      TokenType::NotEq => Self::Equals,
      TokenType::LessThan => Self::LessGreater,
      TokenType::GreaterThan => Self::LessGreater,
      TokenType::Plus => Self::Sum,
      TokenType::Minus => Self::Sum,
      TokenType::Slash => Self::Product,
      TokenType::Asterisk => Self::Product,
      TokenType::LParen => Self::Call,
      _ => Self::Lowest,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn is_normal<T: Sized + Send + Sync + Unpin>() {}

  #[test]
  fn precedence_normal_types() {
    is_normal::<Precedence>();
  }
}
