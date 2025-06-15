pub mod crab;
pub mod token;

use crate::lexer::token::Token;

pub trait Lexer: Send + Sync {
  fn next_token(&mut self) -> Token;
}
