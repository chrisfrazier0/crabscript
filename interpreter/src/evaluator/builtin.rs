use crate::evaluator::object::Object;
use std::{
  collections::HashMap,
  io::{self, BufRead},
  sync::LazyLock,
};

pub type BuiltinFunction = fn(args: &[&Object]) -> Object;

pub static BUILTINS: LazyLock<HashMap<String, BuiltinFunction>> = LazyLock::new(|| {
  let mut builtins = HashMap::new();
  builtins.insert("atoi!".to_string(), atoi as BuiltinFunction);
  builtins.insert("itoa!".to_string(), itoa as BuiltinFunction);
  builtins.insert("atof!".to_string(), atof as BuiltinFunction);
  builtins.insert("ftoa!".to_string(), ftoa as BuiltinFunction);
  builtins.insert("itof!".to_string(), itof as BuiltinFunction);
  builtins.insert("len!".to_string(), len as BuiltinFunction);
  builtins.insert("print!".to_string(), print as BuiltinFunction);
  builtins.insert("println!".to_string(), println as BuiltinFunction);
  builtins.insert("read!".to_string(), read as BuiltinFunction);
  builtins.insert("trim!".to_string(), trim as BuiltinFunction);
  builtins.insert("typeof!".to_string(), type_of as BuiltinFunction);
  builtins
});

fn atoi(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `atoi!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::String(s) => s
      .parse::<i64>()
      .map(Object::Integer)
      .unwrap_or(Object::Error("failed to parse integer".to_string())),
    _ => Object::Error(format!(
      "argument to `atoi!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn itoa(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `itoa!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::Integer(i) => Object::String(i.to_string()),
    _ => Object::Error(format!(
      "argument to `itoa!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn atof(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `atof!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::String(s) => s
      .parse::<f64>()
      .map(Object::Float)
      .unwrap_or(Object::Error("failed to parse float".to_string())),
    _ => Object::Error(format!(
      "argument to `atof!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn ftoa(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `ftoa!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::Float(f) => Object::String(f.to_string()),
    _ => Object::Error(format!(
      "argument to `ftoa!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn itof(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `itof!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::Integer(i) => Object::Float(*i as f64),
    _ => Object::Error(format!(
      "argument to `itof!` not supported, got `{}`",
      args[0]
    )),
  }
}

fn len(args: &[&Object]) -> Object {
  if args.len() != 1 {
    return Object::Error(format!(
      "wrong number of arguments for `len!`: expected 1, got {}",
      args.len()
    ));
  }
  match args[0] {
    Object::String(s) => Object::Integer(s.len() as i64),
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
    Object::Float(_) => Object::String("float".into()),
    Object::Boolean(_) => Object::String("boolean".into()),
    Object::String(_) => Object::String("string".into()),
    Object::Function(_, _) => Object::String("function".into()),
    Object::Builtin(_, _) => Object::String("builtin".into()),
    Object::Error(_) => Object::String("error".into()),
    Object::Return(x) => type_of(&[x]),
  }
}
