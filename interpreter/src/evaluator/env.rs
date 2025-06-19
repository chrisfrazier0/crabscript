use crate::evaluator::object::Object;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Debug, Clone, Default)]
pub struct Environment {
  store: HashMap<String, Object>,
  outer: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
  pub fn new() -> Self {
    Self {
      store: HashMap::new(),
      outer: None,
    }
  }

  pub fn new_child(outer: Rc<RefCell<Environment>>) -> Self {
    Self {
      store: HashMap::new(),
      outer: Some(outer),
    }
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

#[cfg(test)]
mod tests {
  use super::*;

  fn is_normal<T: Sized + Unpin>() {}

  #[test]
  fn env_normal_types() {
    is_normal::<Environment>();
  }
}
