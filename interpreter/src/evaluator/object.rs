use crate::{
  evaluator::{Shared, builtin::BuiltinFunction, env::Environment},
  format::f64_to_string,
  parser::ast::FunctionExpression,
};
use std::{fmt, rc::Rc};

#[derive(Debug, Clone)]
pub enum Object {
  Nil,
  Integer(i64),
  Float(f64),
  Boolean(bool),
  String(Rc<String>),
  Function(Rc<FunctionExpression>, Shared<Environment>),
  Builtin(String, BuiltinFunction),
  Return(Box<Object>),
  Error(String),
}

impl PartialEq for Object {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Integer(a), Self::Integer(b)) => a == b,
      (Self::Float(a), Self::Float(b)) => a == b,
      (Self::Boolean(a), Self::Boolean(b)) => a == b,
      (Self::String(a), Self::String(b)) => a == b,
      (Self::Function(a, _), Self::Function(b, _)) => a == b,
      (Self::Builtin(a, _), Self::Builtin(b, _)) => a == b,
      (Self::Return(a), Self::Return(b)) => a == b,
      (Self::Error(a), Self::Error(b)) => a == b,
      (Self::Nil, Self::Nil) => true,
      _ => false,
    }
  }
}

impl fmt::Display for Object {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Nil => write!(f, "nil"),
      Self::Integer(i) => i.fmt(f),
      Self::Float(x) => write!(f, "{}", f64_to_string(*x)),
      Self::Boolean(b) => b.fmt(f),
      Self::String(s) => write!(f, "'{}'", s),
      Self::Function(n, _) => n.fmt(f),
      Self::Builtin(n, _) => write!(f, "{}()", n),
      Self::Return(r) => r.fmt(f),
      Self::Error(e) => e.fmt(f),
    }
  }
}

impl Object {
  pub fn is_truthy(obj: &Self) -> bool {
    match obj {
      Self::Nil => false,
      Self::Integer(0) => false,
      Self::Integer(_) => true,
      Self::Float(0.0) => false,
      Self::Float(_) => true,
      Self::Boolean(true) => true,
      Self::Boolean(false) => false,
      Self::String(s) => !s.is_empty(),
      Self::Function(_, _) => true,
      Self::Builtin(_, _) => true,
      Self::Error(_) => false,
      Self::Return(r) => Self::is_truthy(r),
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
