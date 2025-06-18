pub mod ast;
pub mod crab;
pub mod precedence;

use crate::{lexer::Lexer, parser::ast::Program};

pub trait Parser<L: Lexer>: Send + Sync {
  fn errors(&self) -> &Vec<String>;
  fn parse_program(&mut self) -> Program;
}
