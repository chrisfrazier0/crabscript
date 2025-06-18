use crate::parser::{Parser, crab::CrabParser};
use std::io::{self, BufRead, Write};

const PROMPT: &str = ">> ";
const ASCII_CRAB: &str = r#" v  ____  v
 \(. , .)/
  //———\\   "#;

pub fn start<R: BufRead, W: Write>(mut input: R, mut output: W) -> io::Result<()> {
  loop {
    write!(output, "{}", PROMPT)?;
    output.flush()?;

    let mut line = String::new();
    if input.read_line(&mut line)? == 0 {
      return Ok(());
    }

    let mut parser = CrabParser::from(line.as_str());
    let program = parser.parse_program();

    if !parser.errors().is_empty() {
      writeln!(
        output,
        "\n{}Woops! We ran into some issues!\n\nParser errors:",
        ASCII_CRAB,
      )?;
      for msg in parser.errors() {
        writeln!(output, "  - {}", msg)?;
      }
      writeln!(output)?;
      continue;
    }

    writeln!(output, "{}", program)?;
  }
}
