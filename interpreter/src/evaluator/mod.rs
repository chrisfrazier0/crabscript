pub mod crab;
pub mod env;
pub mod object;

use crate::{
  evaluator::{env::Environment, object::Object},
  parser::ast,
};
use std::{cell::RefCell, rc::Rc};

pub trait Evaluator: Send + Sync {
  fn eval(&self, node: &ast::Node, env: Rc<RefCell<Environment>>) -> Object;
}
