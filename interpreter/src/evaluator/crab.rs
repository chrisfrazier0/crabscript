use crate::{
  evaluator::{Evaluator, Shared, builtin::BUILTINS, env::Environment, object::Object},
  parser::ast::{Alternative, BlockExpression, Expression, IfExpression, Node, Statement},
};
use std::mem;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct CrabEvaluator;

impl Evaluator for CrabEvaluator {
  fn eval(&self, node: &Node, env: Shared<Environment>) -> Object {
    let obj = match node {
      Node::Program(p) => self.eval_statements(p.statements(), env),
      Node::Statement(s) => self.eval_statement(s, env),
      Node::Expression(x) => self.eval_expression(x, env),
    };
    match obj {
      Object::Return(x) => *x,
      other => other,
    }
  }
}

impl CrabEvaluator {
  fn eval_block(&self, be: &BlockExpression, env: Shared<Environment>) -> Object {
    let env = Environment::shared_child(&env);
    self.eval_statements(be.statements(), env)
  }

  fn eval_statements(&self, stmts: &[Statement], env: Shared<Environment>) -> Object {
    let mut result = Object::Nil;
    for stmt in stmts {
      result = self.eval_statement(stmt, env.clone());
      if matches!(result, Object::Return(_)) || matches!(result, Object::Error(_)) {
        return result;
      }
    }
    result
  }

  fn eval_statement(&self, stmt: &Statement, env: Shared<Environment>) -> Object {
    match stmt {
      Statement::Expression(x) => self.eval_expression(x.expr(), env),
      Statement::If(ie) => self.eval_if(ie, env),
      Statement::Block(be) => self.eval_block(be, env),
      Statement::Let(ls) => {
        let val = ls
          .value()
          .as_ref()
          .map(|v| self.eval_expression(v, env.clone()))
          .unwrap_or(Object::Nil);
        if matches!(val, Object::Error(_)) {
          return val;
        }
        env.borrow_mut().insert(ls.name().value(), val.clone());
        val
      }
      Statement::Return(r) => {
        let ret = r
          .value()
          .as_ref()
          .map(|v| self.eval_expression(v, env))
          .unwrap_or(Object::Nil);
        if matches!(ret, Object::Error(_)) {
          return ret;
        }
        Object::Return(Box::new(ret))
      }
    }
  }

  fn eval_expression(&self, expr: &Expression, env: Shared<Environment>) -> Object {
    match expr {
      Expression::Nil(_) => Object::Nil,
      Expression::Integer(i) => Object::Integer(i.value()),
      Expression::Boolean(b) => Object::Boolean(b.value()),
      Expression::String(s) => Object::String(s.value().to_string()),
      Expression::Identifier(id) => env
        .borrow()
        .get(id.value())
        .or_else(|| {
          BUILTINS
            .get(id.value())
            .map(|b| Object::Builtin(id.value().into(), *b))
        })
        .unwrap_or(Object::Error(format!(
          "identifier not found: {}",
          id.value()
        ))),
      Expression::Prefix(p) => {
        let right = self.eval_expression(p.right(), env);
        if matches!(right, Object::Error(_)) {
          return right;
        }
        self.eval_prefix(p.op(), &right)
      }
      Expression::Infix(f) => {
        let left = self.eval_expression(f.left(), env.clone());
        if matches!(left, Object::Error(_)) {
          return left;
        }
        let right = self.eval_expression(f.right(), env);
        if matches!(right, Object::Error(_)) {
          return right;
        }
        self.eval_infix(f.op(), &left, &right)
      }
      Expression::If(ie) => self.eval_if(ie, env),
      Expression::Function(fe) => Object::Function(fe.clone(), env),
      Expression::Call(ce) => {
        let function = self.eval_expression(ce.function(), env.clone());
        if matches!(function, Object::Error(_)) {
          return function;
        }
        let args = self.eval_expression_vec(ce.arguments(), env);
        if args.len() == 1 && matches!(args[0], Object::Error(_)) {
          return args[0].clone();
        }
        let args: Vec<&Object> = args.iter().collect();
        self.apply_function(&function, &args)
      }
      Expression::Block(b) => self.eval_block(b, env),
    }
  }

  fn eval_expression_vec(
    &self,
    expressions: &Vec<Expression>,
    env: Shared<Environment>,
  ) -> Vec<Object> {
    let mut result = vec![];
    for expr in expressions {
      let evaluated = self.eval_expression(expr, env.clone());
      if matches!(evaluated, Object::Error(_)) {
        return vec![evaluated];
      }
      result.push(evaluated);
    }
    result
  }

  fn eval_prefix(&self, op: &str, right: &Object) -> Object {
    match op {
      "!" => Object::Boolean(!Object::is_truthy(right)),
      "-" => {
        let Object::Integer(int) = right else {
          return Object::Error(format!("unknown operator: {}{}", op, right));
        };
        Object::Integer(-int)
      }
      _ => Object::Error(format!("unknown operator: {}{}", op, right)),
    }
  }

  fn eval_infix(&self, op: &str, left: &Object, right: &Object) -> Object {
    match (left, right) {
      (Object::Integer(l), Object::Integer(r)) => self.eval_infix_integers(op, *l, *r),
      (Object::Boolean(l), Object::Boolean(r)) => self.eval_infix_booleans(op, *l, *r),
      (Object::String(l), Object::String(r)) => self.eval_infix_strings(op, l, r),
      _ => {
        if mem::discriminant(left) != mem::discriminant(right) {
          Object::Error(format!("type mismatch: {} {} {}", left, op, right))
        } else {
          Object::Error(format!("unknown operator: {} {} {}", left, op, right))
        }
      }
    }
  }

  fn eval_infix_integers(&self, op: &str, left: i32, right: i32) -> Object {
    match op {
      "+" => Object::Integer(left + right),
      "-" => Object::Integer(left - right),
      "*" => Object::Integer(left * right),
      "/" => Object::Integer(left / right),
      "<" => Object::Boolean(left < right),
      ">" => Object::Boolean(left > right),
      "==" => Object::Boolean(left == right),
      "!=" => Object::Boolean(left != right),
      _ => Object::Error(format!("unknown operator: {} {} {}", left, op, right)),
    }
  }

  fn eval_infix_booleans(&self, op: &str, left: bool, right: bool) -> Object {
    match op {
      "==" => Object::Boolean(left == right),
      "!=" => Object::Boolean(left != right),
      _ => Object::Error(format!("unknown operator: {} {} {}", left, op, right)),
    }
  }

  fn eval_infix_strings(&self, op: &str, left: &str, right: &str) -> Object {
    match op {
      "+" => Object::String(left.to_string() + right),
      "==" => Object::Boolean(left == right),
      "!=" => Object::Boolean(left != right),
      _ => Object::Error(format!("unknown operator: STRING {} STRING", op)),
    }
  }

  fn eval_if(&self, ie: &IfExpression, env: Shared<Environment>) -> Object {
    let condition = self.eval_expression(ie.condition(), env.clone());
    if matches!(condition, Object::Error(_)) {
      return condition;
    }
    if Object::is_truthy(&condition) {
      self.eval_block(ie.consequence(), env)
    } else if let Some(alt) = ie.alternative() {
      match alt {
        Alternative::Block(be) => self.eval_block(be, env),
        Alternative::If(ie) => self.eval_if(ie, env),
      }
    } else {
      Object::Nil
    }
  }

  fn apply_function(&self, func: &Object, args: &[&Object]) -> Object {
    if let Object::Builtin(_, f) = func {
      return f(args);
    }
    let Object::Function(fe, _) = func else {
      return Object::Error(format!("not a function: {:?}", func));
    };
    if fe.parameters().len() != args.len() {
      return Object::Error(format!(
        "wrong number of arguments: expected {}, got {}",
        fe.parameters().len(),
        args.len()
      ));
    }
    let env = self.extend_function_env(func, args);
    match self.eval_statements(fe.body().statements(), env) {
      Object::Return(x) => *x,
      other => other,
    }
  }

  fn extend_function_env(&self, func: &Object, args: &[&Object]) -> Shared<Environment> {
    if let Object::Function(fe, env) = func {
      let mut function_env = Environment::new_child(env);
      for (param, arg) in fe.parameters().iter().zip(args.iter()) {
        function_env.insert(param.value(), (*arg).clone());
      }
      function_env.into()
    } else {
      Environment::shared()
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    evaluator::object::Object,
    parser::{Parser, crab::CrabParser},
  };

  // --- Test Helpers ---

  fn is_normal<T: Sized + Send + Sync + Unpin>() {}

  fn test_eval(input: &str) -> Object {
    let crab = CrabEvaluator::default();
    let env = Environment::shared();
    let parser = CrabParser::from(input);

    parser
      .parse()
      .map_err(|errors| {
        panic!(
          "Failed to parse input: {}\nParser errors: {:?}",
          input, errors,
        )
      })
      .map(|program| crab.eval(&program, env))
      .unwrap()
  }

  // --- Test Cases ---

  #[test]
  fn crab_eval_normal_types() {
    is_normal::<CrabEvaluator>();
  }

  #[test]
  fn crab_eval_nil() {
    let output = test_eval("nil");
    assert_eq!(output.to_string(), "nil");
  }

  #[test]
  fn crab_eval_integer() {
    let tests = [
      ("5", Object::Integer(5)),
      ("10;", Object::Integer(10)),
      ("-5;", Object::Integer(-5)),
      ("-10", Object::Integer(-10)),
      ("--1", Object::Integer(1)),
      ("5", Object::Integer(5)),
      ("10", Object::Integer(10)),
      ("-5", Object::Integer(-5)),
      ("-10", Object::Integer(-10)),
      ("5 + 5 + 5 + 5 - 10", Object::Integer(10)),
      ("2 * 2 * 2 * 2 * 2", Object::Integer(32)),
      ("-50 + 100 + -50", Object::Integer(0)),
      ("5 * 2 + 10", Object::Integer(20)),
      ("5 + 2 * 10", Object::Integer(25)),
      ("20 + 2 * -10", Object::Integer(0)),
      ("50 / 2 * 2 + 10", Object::Integer(60)),
      ("2 * (5 + 10)", Object::Integer(30)),
      ("3 * 3 * 3 + 10", Object::Integer(37)),
      ("3 * (3 * 3) + 10", Object::Integer(37)),
      ("(5 + 10 * 2 + 15 / 3) * 2 + -10", Object::Integer(50)),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_boolean() {
    let tests = [
      ("true", Object::Boolean(true)),
      ("false;", Object::Boolean(false)),
      ("!true;", Object::Boolean(false)),
      ("!false;", Object::Boolean(true)),
      ("!5;", Object::Boolean(false)),
      ("!!true;", Object::Boolean(true)),
      ("!!false", Object::Boolean(false)),
      ("!!5", Object::Boolean(true)),
      ("!!0", Object::Boolean(false)),
      ("!''", Object::Boolean(true)),
      ("!!''", Object::Boolean(false)),
      ("!!'hello'", Object::Boolean(true)),
      ("1 < 2", Object::Boolean(true)),
      ("1 > 2", Object::Boolean(false)),
      ("1 < 1", Object::Boolean(false)),
      ("1 > 1", Object::Boolean(false)),
      ("1 == 1", Object::Boolean(true)),
      ("1 != 1", Object::Boolean(false)),
      ("1 == 2", Object::Boolean(false)),
      ("1 != 2", Object::Boolean(true)),
      ("true == true", Object::Boolean(true)),
      ("false == false", Object::Boolean(true)),
      ("true == false", Object::Boolean(false)),
      ("true != false", Object::Boolean(true)),
      ("false != true", Object::Boolean(true)),
      ("(1 < 2) == true", Object::Boolean(true)),
      ("(1 < 2) == false", Object::Boolean(false)),
      ("(1 > 2) == true", Object::Boolean(false)),
      ("(1 > 2) == false", Object::Boolean(true)),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_string() {
    let tests = [
      ("'hello_world'", Object::String("hello_world".into())),
      ("'Hello World!';", Object::String("Hello World!".into())),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_string_concat() {
    let tests = [
      (
        "'Hello ' + 'World!';",
        Object::String("Hello World!".into()),
      ),
      ("'Hello' == 'Hello'", Object::Boolean(true)),
      ("'Hello' != 'Hello'", Object::Boolean(false)),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn eval_let_statements() {
    let tests = [
      ("let a = 5; a;", Object::Integer(5)),
      ("let a = 5 * 5; a", Object::Integer(25)),
      ("let a = 5; let b = a; b;", Object::Integer(5)),
      (
        "let a = 5; let b = a; let c = a + b + 5; c;",
        Object::Integer(15),
      ),
      (
        "let a = 5; let b = a; let c = a + b + 10",
        Object::Integer(20),
      ),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_if_else() {
    let tests = [
      ("if true { 10 };", Object::Integer(10)),
      ("if (false) { 10 };", Object::Nil),
      ("if 1 { 10 };", Object::Integer(10)),
      ("if (1 < 2) { 10 };", Object::Integer(10)),
      ("if (1 > 2) { 10 };", Object::Nil),
      ("if 1 < 2 { 10 } else { 20 }", Object::Integer(10)),
      ("if 1 > 2 { 10 } else { 20 }", Object::Integer(20)),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_function() {
    let input = "fn(x) { x + 2; };";
    let result = test_eval(input);
    if let Object::Function(f, _) = result {
      assert_eq!(f.parameters().len(), 1, "function param length");
      assert_eq!(f.parameters()[0].value(), "x", "function param name");
      assert_eq!(f.body().to_string(), "{ (x + 2); }", "function body");
    } else {
      panic!("Expected a function, got: {:?}", result);
    }
  }

  #[test]
  fn crab_eval_call() {
    let tests = [
      ("let ident = fn(x) { x; }; ident(5);", Object::Integer(5)),
      (
        "let ident = fn(x) { return x; }; ident(5);",
        Object::Integer(5),
      ),
      (
        "let double = fn(x) { x * 2 }; double(5)",
        Object::Integer(10),
      ),
      (
        "let add = fn(x, y) { x + y; }; add(5, 5);",
        Object::Integer(10),
      ),
      (
        "let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));",
        Object::Integer(20),
      ),
      ("fn(x) { x }(5)", Object::Integer(5)),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_return() {
    let tests = [
      ("return 10;", Object::Integer(10)),
      ("; return 10; 9;", Object::Integer(10)),
      ("return 2*5; 9;", Object::Integer(10)),
      ("9; return 2 * 5; 9;", Object::Integer(10)),
      (
        r#"
        if (10 > 1) {
          if (10 > 1) {
            return 10;
          };
          return 1;
        }
        "#,
        Object::Integer(10),
      ),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, expected.clone(), "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_closures() {
    let input = r#"
      let newAdder = fn(x) {
        fn(y) { x + y }
      };
      let addTwo = newAdder(2);
      let _ = newAdder(10);
      addTwo(2);
    "#;

    let output = test_eval(input);
    assert_eq!(output, Object::Integer(4), "closure value");
  }

  #[test]
  fn crab_eval_builtins() {
    let tests = [
      ("len!('')", Object::Integer(0)),
      ("len!('four')", Object::Integer(4)),
      ("len!('hello world')", Object::Integer(11)),
      (
        "len!(1)",
        Object::Error("argument to `len!` not supported, got `1`".into()),
      ),
      (
        "len!('', '')",
        Object::Error("wrong number of arguments for `len!`: expected 1, got 2".into()),
      ),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(output, *expected, "test[{}] value", i + 1);
    }
  }

  #[test]
  fn crab_eval_error_handling() {
    let tests = [
      ("5 + true;", "type mismatch: 5 + true"),
      ("5 + true; 5;", "type mismatch: 5 + true"),
      ("-true", "unknown operator: -true"),
      ("true + false;", "unknown operator: true + false"),
      ("5; true + false; 5", "unknown operator: true + false"),
      (
        "if 10 > 1 { true + false; }",
        "unknown operator: true + false",
      ),
      (
        r#"
        if (10 > 1) {
          if (10 > 1) {
            return true + false;
          };
          return 1;
        };
        "#,
        "unknown operator: true + false",
      ),
      ("foobar", "identifier not found: foobar"),
      (
        r#"
        let newAdder = fn(x) {
          fn(y) { x + y }
        };
        let addTwo = newAdder(2);
        x;
        "#,
        "identifier not found: x",
      ),
      (
        "fn(x) { let foo = x; }(10); foo;",
        "identifier not found: foo",
      ),
      (
        "if true { let foo = 10; } foo;",
        "identifier not found: foo",
      ),
      ("'Hello ' - 'World';", "unknown operator: STRING - STRING"),
      ("'Hello ' > 'World';", "unknown operator: STRING > STRING"),
    ];

    for (i, (input, expected)) in tests.iter().enumerate() {
      let output = test_eval(input);
      assert_eq!(
        output,
        Object::Error(expected.to_string()),
        "test[{}] value",
        i + 1
      );
    }
  }
}
