pub mod builtin;
pub mod crab;
pub mod env;
pub mod object;

use crate::{
  evaluator::{env::Environment, object::Object},
  parser::ast,
};
use std::{cell::RefCell, rc::Rc};

pub type Shared<T> = Rc<RefCell<T>>;

pub trait Evaluator: Send + Sync {
  fn eval(&self, node: &ast::Node, env: Shared<Environment>) -> Object;
}
