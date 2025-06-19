use crate::{evaluator::env::Environment, parser::ast::FunctionExpression};
use std::{cell::RefCell, fmt, rc::Rc};

#[derive(Debug, Clone)]
pub enum Object {
  Nil,
  Integer(i32),
  Boolean(bool),
  Function(FunctionExpression, Rc<RefCell<Environment>>),
  Return(Box<Object>),
  Error(String),
}

impl PartialEq for Object {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Object::Integer(a), Object::Integer(b)) => a == b,
      (Object::Boolean(a), Object::Boolean(b)) => a == b,
      (Object::Function(a, _), Object::Function(b, _)) => a == b,
      (Object::Return(a), Object::Return(b)) => a == b,
      (Object::Error(a), Object::Error(b)) => a == b,
      (Object::Nil, Object::Nil) => true,
      _ => false,
    }
  }
}

impl fmt::Display for Object {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Nil => write!(f, "nil"),
      Self::Integer(i) => i.fmt(f),
      Self::Boolean(b) => b.fmt(f),
      Self::Function(n, _) => n.fmt(f),
      Self::Return(r) => r.fmt(f),
      Self::Error(e) => write!(f, "ERROR: {}", e),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn is_normal<T: Sized + Unpin>() {}

  #[test]
  fn object_normal_types() {
    is_normal::<Object>();
  }
}
