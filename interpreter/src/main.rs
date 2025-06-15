use interpreter::repl;
use std::io;

fn main() -> io::Result<()> {
  let mut username = whoami::username();
  username = username
    .chars()
    .next()
    .map(|c| format!(" {}{}", c.to_uppercase(), &username[1..]))
    .unwrap_or_default();

  println!(
    "\nHello{}! Welcome to the CrabScript programming language!",
    username
  );
  println!("Feel free to enter commands below\n");

  repl::start(io::stdin().lock(), io::stdout())
}
