pub mod ast;
pub mod crab;
pub mod precedence;

use crate::parser::ast::Node;

pub trait Parser: Send + Sync {
  fn parse(self) -> Result<Node, Vec<String>>;
}
