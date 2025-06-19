use crate::evaluator::object::Object;
use std::{
  collections::HashMap,
  io::{self, BufRead},
  sync::LazyLock,
};

pub type BuiltinFunction = fn(args: &[&Object]) -> Object;

pub static BUILTINS: LazyLock<HashMap<String, BuiltinFunction>> = LazyLock::new(|| {
  let mut builtins = HashMap::new();
  builtins.insert("len!".to_string(), len as BuiltinFunction);
  builtins.insert("print!".to_string(), print as BuiltinFunction);
  builtins.insert("println!".to_string(), println as BuiltinFunction);
  builtins.insert("read!".to_string(), read as BuiltinFunction);
  builtins.insert("trim!".to_string(), trim as BuiltinFunction);
  builtins.insert("typeof!".to_string(), type_of as BuiltinFunction);
  builtins
});

fn len(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `len!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::String(s) => Object::Integer(s.len() as i32),
    _ => Object::Error(format!(
      "argument to `len!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn print(args: &[&Object]) -> Object {
  let mut output = vec![];
  for arg in args {
    match arg {
      Object::String(s) => output.push(s.clone()),
      other => output.push(other.to_string()),
    }
  }
  print!("{}", process_escapes(&output.join(" ")));
  Object::Nil
}

fn println(args: &[&Object]) -> Object {
  let mut output = vec![];
  for arg in args {
    match arg {
      Object::String(s) => output.push(s.clone()),
      other => output.push(other.to_string()),
    }
  }
  println!("{}", process_escapes(&output.join(" ")));
  Object::Nil
}

fn process_escapes(input: &str) -> String {
  let mut result = String::new();
  let mut chars = input.chars().peekable();
  while let Some(ch) = chars.next() {
    if ch != '\\' {
      result.push(ch);
      continue;
    }
    let Some(ch) = chars.next() else {
      break;
    };
    match ch {
      'n' => result.push('\n'),
      'r' => result.push('\r'),
      't' => result.push('\t'),
      other => result.push(other),
    }
  }
  result
}

fn read(args: &[&Object]) -> Object {
  if !args.is_empty() {
    return Object::Error(format!(
      "wrong number of arguments for `read!`: expected 0, got {}",
      args.len()
    ));
  }
  let mut line = String::new();
  if io::stdin().lock().read_line(&mut line).is_ok() {
    Object::String(line.trim_end_matches(['\r', '\n']).to_string())
  } else {
    Object::Error("failed to read from stdin".to_string())
  }
}

fn trim(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `trim!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::String(s) => Object::String(s.trim().to_string()),
    _ => Object::Error(format!(
      "argument to `trim!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn type_of(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `typeof!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::Nil => Object::String("nil".into()),
    Object::Integer(_) => Object::String("integer".into()),
    Object::Boolean(_) => Object::String("boolean".into()),
    Object::String(_) => Object::String("string".into()),
    Object::Function(_, _) => Object::String("function".into()),
    Object::Builtin(_, _) => Object::String("builtin".into()),
    Object::Error(_) => Object::String("error".into()),
    Object::Return(x) => type_of(&[x]),
  }
}
