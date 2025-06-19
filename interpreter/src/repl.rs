use crate::{
  evaluator::{Evaluator, crab::CrabEvaluator, env::Environment, object::Object},
  parser::{Parser, crab::CrabParser},
};
use std::{
  cell::RefCell,
  io::{self, BufRead, Write},
  rc::Rc,
};

const PROMPT: &str = ">> ";
const ASCII_CRAB: &str = r#" v  ____  v
 \(. , .)/
  //———\\   "#;

pub fn start<R: BufRead, W: Write>(mut input: R, mut output: W) -> io::Result<()> {
  let crab = CrabEvaluator::default();
  let env = Rc::new(RefCell::new(Environment::default()));

  loop {
    write!(output, "{}", PROMPT)?;
    output.flush()?;

    let mut line = String::new();
    if input.read_line(&mut line)? == 0 {
      return Ok(());
    }

    let evaluated = CrabParser::from(line.as_str())
      .parse()
      .map(|program| crab.eval(&program, Rc::clone(&env)))
      .map_err(|errors| print_errors(&mut output, errors))
      .unwrap_or(Object::Nil);

    if !matches!(evaluated, Object::Nil) {
      writeln!(output, "{}", evaluated)?;
    }
  }
}

fn print_errors<W: Write>(output: &mut W, errors: &Vec<String>) -> io::Result<()> {
  writeln!(
    output,
    "\n{}Woops! We ran into some issues!\n\nParser errors:",
    ASCII_CRAB,
  )?;
  for msg in errors {
    writeln!(output, "  - {}", msg)?;
  }
  writeln!(output)
}
