pub mod ast;
pub mod crab;
pub mod precedence;

use crate::{lexer::Lexer, parser::ast::Node};

pub trait Parser<L: Lexer>: Send + Sync {
  fn parse(&mut self) -> Result<Node, &Vec<String>>;
}
