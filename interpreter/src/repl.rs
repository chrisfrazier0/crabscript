use crate::{
  evaluator::{Evaluator, crab::CrabEvaluator, env::Environment, object::Object},
  parser::{Parser, crab::CrabParser},
};
use std::io::{self, BufRead, Write};

const PROMPT: &str = ">> ";
const ASCII_CRAB: &str = r#" v  ____  v
 \(. , .)/
  //———\\   "#;

pub fn start() -> io::Result<()> {
  let mut output = io::stdout();
  let crab = CrabEvaluator::default();
  let env = Environment::shared();

  loop {
    write!(output, "{}", PROMPT)?;
    output.flush()?;

    let mut line = String::new();
    {
      if io::stdin().lock().read_line(&mut line)? == 0 {
        return Ok(());
      }
    }

    let evaluated = CrabParser::from(line.as_str())
      .parse()
      .map_err(|errors| print_errors(&mut output, "Parser", &errors))
      .map(|program| crab.eval(&program, env.clone()))
      .unwrap_or(Object::Nil);

    if let Object::Error(errors) = evaluated {
      print_errors(&mut output, "Runtime", &vec![errors])?;
      continue;
    }

    match evaluated {
      Object::Integer(_) | Object::Boolean(_) | Object::String(_) => {
        writeln!(output, " {}", evaluated)?
      }
      _ => {}
    }
  }
}

fn print_errors<W: Write>(
  output: &mut W,
  error_type: &str,
  errors: &Vec<String>,
) -> io::Result<()> {
  writeln!(
    output,
    "\n{}Woops! We ran into some issues!\n\n{} errors:",
    ASCII_CRAB, error_type,
  )?;
  for msg in errors {
    writeln!(output, "  - {}", msg)?;
  }
  writeln!(output)
}
