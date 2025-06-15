use crate::lexer::{
  Lexer,
  token::{Token, TokenType},
};

#[derive(Debug, Clone)]
pub struct CrabLexer {
  input: Vec<char>,
  position: usize,
  read_position: usize,
  ch: Option<char>,
}

impl Lexer for CrabLexer {
  fn next_token(&mut self) -> Token {
    self.skip_whitespace();
    let token = match self.ch {
      Some('!') => {
        if self.peek_char() == Some('=') {
          self.read_char();
          Token::new(TokenType::NotEq, "!=")
        } else {
          Token::new(TokenType::Bang, "!")
        }
      }
      Some('=') => {
        if self.peek_char() == Some('=') {
          self.read_char();
          Token::new(TokenType::Eq, "==")
        } else {
          Token::new(TokenType::Assign, "=")
        }
      }
      Some('+') => Token::new(TokenType::Plus, "+"),
      Some('-') => Token::new(TokenType::Minus, "-"),
      Some('/') => Token::new(TokenType::Slash, "/"),
      Some('*') => Token::new(TokenType::Asterisk, "*"),
      Some('(') => Token::new(TokenType::LParen, "("),
      Some(')') => Token::new(TokenType::RParen, ")"),
      Some('{') => Token::new(TokenType::LBrace, "{"),
      Some('}') => Token::new(TokenType::RBrace, "}"),
      Some('<') => Token::new(TokenType::LessThan, "<"),
      Some('>') => Token::new(TokenType::GreaterThan, ">"),
      Some(',') => Token::new(TokenType::Comma, ","),
      Some(';') => Token::new(TokenType::Semicolon, ";"),
      Some(ch) => {
        if Self::is_letter(ch) {
          let ident = self.read_identifier();
          let token_type = TokenType::from(ident.as_str());
          return Token::new(token_type, &ident);
        } else if Self::is_digit(ch) {
          let number = self.read_number();
          return Token::new(TokenType::Int, &number);
        } else {
          Token::new(TokenType::Invalid, &ch.to_string())
        }
      }
      None => Token::new(TokenType::Eof, ""),
    };
    self.read_char();
    token
  }
}

impl CrabLexer {
  pub fn new(input: &str) -> Self {
    let mut lexer = Self {
      input: input.chars().collect(),
      position: 0,
      read_position: 0,
      ch: None,
    };
    lexer.read_char();
    lexer
  }

  fn read_char(&mut self) {
    if self.read_position >= self.input.len() {
      self.ch = None;
    } else {
      self.ch = Some(self.input[self.read_position]);
    }
    self.position = self.read_position;
    self.read_position += 1;
  }

  fn peek_char(&self) -> Option<char> {
    if self.read_position >= self.input.len() {
      None
    } else {
      Some(self.input[self.read_position])
    }
  }

  fn skip_whitespace(&mut self) {
    while let Some(ch) = self.ch {
      if ch.is_whitespace() {
        self.read_char();
      } else {
        break;
      }
    }
  }

  fn read_identifier(&mut self) -> String {
    let position = self.position;
    while self.ch.is_some_and(Self::is_ident) {
      self.read_char();
    }
    self.input[position..self.position].iter().collect()
  }

  fn read_number(&mut self) -> String {
    let position = self.position;
    while self.ch.is_some_and(Self::is_digit) {
      self.read_char();
    }
    self.input[position..self.position].iter().collect()
  }

  fn is_letter(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
  }

  fn is_digit(ch: char) -> bool {
    ch.is_ascii_digit()
  }

  fn is_ident(ch: char) -> bool {
    ch.is_alphabetic() || ch.is_ascii_digit() || ch == '_'
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn is_normal<T: Sized + Send + Sync + Unpin>() {}

  #[test]
  fn crab_lexer_normal_types() {
    is_normal::<CrabLexer>();
  }

  #[test]
  fn crab_lexer_next_token() {
    let input = r#"
      let five5 = 5;
      let _ten = 10;

      let add = fn(x, y) {
        x + y;
      };

      let result = add(five, _ten);
      !-/*5;
      5 < 10 > 5;

      if (5 < 10) {
        return true;
      } else {
        return false;
      }

      10 == 10;
      10 != 9;
    "#;

    let tests = vec![
      (TokenType::Let, "let"),
      (TokenType::Ident, "five5"),
      (TokenType::Assign, "="),
      (TokenType::Int, "5"),
      (TokenType::Semicolon, ";"),
      (TokenType::Let, "let"),
      (TokenType::Ident, "_ten"),
      (TokenType::Assign, "="),
      (TokenType::Int, "10"),
      (TokenType::Semicolon, ";"),
      (TokenType::Let, "let"),
      (TokenType::Ident, "add"),
      (TokenType::Assign, "="),
      (TokenType::Function, "fn"),
      (TokenType::LParen, "("),
      (TokenType::Ident, "x"),
      (TokenType::Comma, ","),
      (TokenType::Ident, "y"),
      (TokenType::RParen, ")"),
      (TokenType::LBrace, "{"),
      (TokenType::Ident, "x"),
      (TokenType::Plus, "+"),
      (TokenType::Ident, "y"),
      (TokenType::Semicolon, ";"),
      (TokenType::RBrace, "}"),
      (TokenType::Semicolon, ";"),
      (TokenType::Let, "let"),
      (TokenType::Ident, "result"),
      (TokenType::Assign, "="),
      (TokenType::Ident, "add"),
      (TokenType::LParen, "("),
      (TokenType::Ident, "five"),
      (TokenType::Comma, ","),
      (TokenType::Ident, "_ten"),
      (TokenType::RParen, ")"),
      (TokenType::Semicolon, ";"),
      (TokenType::Bang, "!"),
      (TokenType::Minus, "-"),
      (TokenType::Slash, "/"),
      (TokenType::Asterisk, "*"),
      (TokenType::Int, "5"),
      (TokenType::Semicolon, ";"),
      (TokenType::Int, "5"),
      (TokenType::LessThan, "<"),
      (TokenType::Int, "10"),
      (TokenType::GreaterThan, ">"),
      (TokenType::Int, "5"),
      (TokenType::Semicolon, ";"),
      (TokenType::If, "if"),
      (TokenType::LParen, "("),
      (TokenType::Int, "5"),
      (TokenType::LessThan, "<"),
      (TokenType::Int, "10"),
      (TokenType::RParen, ")"),
      (TokenType::LBrace, "{"),
      (TokenType::Return, "return"),
      (TokenType::True, "true"),
      (TokenType::Semicolon, ";"),
      (TokenType::RBrace, "}"),
      (TokenType::Else, "else"),
      (TokenType::LBrace, "{"),
      (TokenType::Return, "return"),
      (TokenType::False, "false"),
      (TokenType::Semicolon, ";"),
      (TokenType::RBrace, "}"),
      (TokenType::Int, "10"),
      (TokenType::Eq, "=="),
      (TokenType::Int, "10"),
      (TokenType::Semicolon, ";"),
      (TokenType::Int, "10"),
      (TokenType::NotEq, "!="),
      (TokenType::Int, "9"),
      (TokenType::Semicolon, ";"),
      (TokenType::Eof, ""),
    ];

    let mut lexer = CrabLexer::new(input);
    for (i, (expected_type, expected_literal)) in tests.iter().enumerate() {
      let token = lexer.next_token();
      assert_eq!(token.token_type(), *expected_type, "test[{}-1]", i);
      assert_eq!(token.literal(), expected_literal, "test[{}-2]", i);
    }
  }
}
