use crate::evaluator::{Shared, object::Object};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Debug, Clone, Default)]
pub struct Environment {
  store: HashMap<String, Object>,
  outer: Option<Shared<Environment>>,
}

impl Environment {
  pub fn new_child(outer: &Shared<Environment>) -> Self {
    Self {
      store: HashMap::new(),
      outer: Some(Rc::clone(outer)),
    }
  }

  pub fn shared() -> Shared<Self> {
    Rc::new(RefCell::new(Self::default()))
  }

  pub fn shared_child(outer: &Shared<Environment>) -> Shared<Self> {
    Rc::new(RefCell::new(Self::new_child(outer)))
  }

  pub fn insert(&mut self, key: &str, value: Object) {
    self.store.insert(key.to_string(), value);
  }

  pub fn get(&self, key: &str) -> Option<Object> {
    self.store.get(key).cloned().or_else(|| {
      self
        .outer
        .as_ref()
        .and_then(|outer| outer.borrow().get(key))
    })
  }
}

impl From<Environment> for Shared<Environment> {
  fn from(value: Environment) -> Self {
    Rc::new(RefCell::new(value))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn is_normal<T: Sized + Unpin>() {}

  #[test]
  fn env_normal_types() {
    is_normal::<Environment>();
  }
}
