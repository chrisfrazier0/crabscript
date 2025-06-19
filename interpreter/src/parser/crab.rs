use crate::{
  lexer::{
    Lexer,
    crab::CrabLexer,
    token::{Token, TokenType},
  },
  parser::{
    Parser,
    ast::{
      Alternative, BlockExpression, Boolean, CallExpression, Expression, ExpressionStatement,
      FunctionExpression, Identifier, IfExpression, InfixExpression, Integer, LetStatement, Nil,
      Node, PrefixExpression, Program, ReturnStatement, Statement, StringValue,
    },
    precedence::Precedence,
  },
};
use std::mem;

#[derive(Debug, Clone)]
pub struct CrabParser<L: Lexer> {
  lexer: L,
  cur_token: Token,
  peek_token: Token,
  errors: Vec<String>,
}

impl From<&str> for CrabParser<CrabLexer> {
  fn from(value: &str) -> Self {
    Self::new(CrabLexer::new(value))
  }
}

impl<L> Parser for CrabParser<L>
where
  L: Lexer,
{
  fn parse(mut self) -> Result<Node, Vec<String>> {
    let program = Node::Program(self.parse_program());
    if self.errors.is_empty() {
      Ok(program)
    } else {
      Err(self.errors)
    }
  }
}

impl<L> CrabParser<L>
where
  L: Lexer,
{
  pub fn new(mut lexer: L) -> Self {
    let cur_token = lexer.next_token();
    let peek_token = lexer.next_token();
    Self {
      lexer,
      cur_token,
      peek_token,
      errors: vec![],
    }
  }

  // --- Error Factories ---

  fn token_error(&mut self, tt: TokenType, token: &Token) {
    self
      .errors
      .push(format!("expected next token to be {}, got {}", tt, token,));
  }

  fn integer_error(&mut self) {
    self.errors.push(format!(
      "could not parse '{}' as integer",
      self.cur_token.literal(),
    ));
  }

  fn prefix_error(&mut self) {
    self
      .errors
      .push(format!("no prefix parse function for {}", self.cur_token));
  }

  fn infix_error(&mut self) {
    self
      .errors
      .push(format!("no infix parse function for {}", self.cur_token,));
  }

  fn if_block_error(&mut self) {
    self
      .errors
      .push("if condition must not be a block expression".to_string());
  }

  fn if_else_error(&mut self) {
    self
      .errors
      .push("if else must be followed by a block or another if".to_string());
  }

  // --- Utility ---

  fn next_token(&mut self) {
    self.cur_token = mem::replace(&mut self.peek_token, self.lexer.next_token());
  }

  fn current_is(&self, tt: TokenType) -> bool {
    self.cur_token.token_type() == tt
  }

  fn current_precedence(&self) -> Precedence {
    Precedence::from(self.cur_token.token_type())
  }

  fn peek_is(&self, tt: TokenType) -> bool {
    self.peek_token.token_type() == tt
  }

  fn peek_precedence(&self) -> Precedence {
    Precedence::from(self.peek_token.token_type())
  }

  fn maybe_peek(&mut self, tt: TokenType) -> bool {
    if self.peek_is(tt) {
      self.next_token();
      true
    } else {
      false
    }
  }

  fn expect_peek(&mut self, tt: TokenType) -> bool {
    if self.peek_is(tt) {
      self.next_token();
      true
    } else {
      self.token_error(tt, &self.peek_token.clone());
      false
    }
  }

  // --- Parse Statements ---

  fn parse_program(&mut self) -> Program {
    let mut program = Program::default();
    while !self.current_is(TokenType::Eof) {
      if let Some(stmt) = self.parse_statement(false) {
        program.push_statement(stmt);
      }
      self.next_token();
    }
    program
  }

  fn parse_statement(&mut self, block: bool) -> Option<Statement> {
    let mut skip = false;
    let result = match self.cur_token.token_type() {
      TokenType::Semicolon => return None,
      TokenType::Let => self.parse_let_statement().map(Statement::Let),
      TokenType::Return => self.parse_return_statement().map(Statement::Return),
      TokenType::If => {
        skip = true;
        self.parse_if().map(Statement::If)
      }
      TokenType::LBrace => {
        skip = true;
        self.parse_block().map(Statement::Block)
      }
      _ => self.parse_expression_statement().map(Statement::Expression),
    };
    if result.is_some()
      && !self.peek_is(TokenType::Eof)
      && !(block && self.peek_is(TokenType::RBrace))
    {
      if skip {
        self.maybe_peek(TokenType::Semicolon);
      } else {
        self.expect_peek(TokenType::Semicolon);
      }
    }
    result
  }

  fn parse_let_statement(&mut self) -> Option<LetStatement> {
    let token = self.cur_token.clone();
    if !self.expect_peek(TokenType::Ident) {
      return None;
    }
    let name = Identifier::new(self.cur_token.clone(), self.cur_token.literal().to_string());
    let value = if self.maybe_peek(TokenType::Assign) {
      self.next_token();
      Some(self.parse_expression(Precedence::Lowest)?)
    } else {
      None
    };
    Some(LetStatement::new(token, name, value))
  }

  fn parse_return_statement(&mut self) -> Option<ReturnStatement> {
    let token = self.cur_token.clone();
    let value = if !self.peek_is(TokenType::Semicolon) && !self.peek_is(TokenType::Eof) {
      self.next_token();
      Some(self.parse_expression(Precedence::Lowest)?)
    } else {
      None
    };
    Some(ReturnStatement::new(token, value))
  }

  fn parse_expression_statement(&mut self) -> Option<ExpressionStatement> {
    let token = self.cur_token.clone();
    self
      .parse_expression(Precedence::Lowest)
      .map(|e| ExpressionStatement::new(token, e))
  }

  // --- Parse Expressions ---

  fn parse_expression(&mut self, precedence: Precedence) -> Option<Expression> {
    // literals and prefix expressions
    let mut left = match self.cur_token.token_type() {
      TokenType::LParen => self.parse_grouped(),
      TokenType::LBrace => self.parse_block().map(Expression::Block),
      TokenType::Function => self.parse_function().map(Expression::Function),
      TokenType::If => self.parse_if().map(|ie| Expression::If(Box::new(ie))),
      TokenType::Nil => self.parse_nil().map(Expression::Nil),
      TokenType::Int => self.parse_integer().map(Expression::Integer),
      TokenType::True | TokenType::False => self.parse_boolean().map(Expression::Boolean),
      TokenType::String => self.parse_string().map(Expression::String),
      TokenType::Ident => self.parse_identifier().map(Expression::Identifier),
      TokenType::Bang | TokenType::Minus => self
        .parse_prefix()
        .map(|pe| Expression::Prefix(Box::new(pe))),
      _ => {
        self.prefix_error();
        return None;
      }
    };
    // infix expressions
    while left.is_some() && precedence < self.peek_precedence() {
      self.next_token();
      left = match self.cur_token.token_type() {
        TokenType::Eq
        | TokenType::NotEq
        | TokenType::LessThan
        | TokenType::GreaterThan
        | TokenType::Plus
        | TokenType::Minus
        | TokenType::Slash
        | TokenType::Asterisk => self
          .parse_infix(left.unwrap())
          .map(|ie| Expression::Infix(Box::new(ie))),
        TokenType::LParen => self
          .parse_call(left.unwrap())
          .map(|ce| Expression::Call(Box::new(ce))),
        _ => {
          self.infix_error();
          return None;
        }
      };
    }
    left
  }

  fn parse_grouped(&mut self) -> Option<Expression> {
    self.next_token();
    let expr = self.parse_expression(Precedence::Lowest)?;
    if !self.expect_peek(TokenType::RParen) {
      return None;
    }
    Some(expr)
  }

  fn parse_nil(&self) -> Option<Nil> {
    Some(Nil::new(self.cur_token.clone()))
  }

  fn parse_integer(&mut self) -> Option<Integer> {
    let token = self.cur_token.clone();
    let Ok(value) = self.cur_token.literal().parse::<i32>() else {
      self.integer_error();
      return None;
    };
    Some(Integer::new(token, value))
  }

  fn parse_boolean(&mut self) -> Option<Boolean> {
    let token = self.cur_token.clone();
    let value = self.current_is(TokenType::True);
    Some(Boolean::new(token, value))
  }

  fn parse_string(&mut self) -> Option<StringValue> {
    let token = self.cur_token.clone();
    let value = self.cur_token.literal().to_string();
    Some(StringValue::new(token, value))
  }

  fn parse_identifier(&mut self) -> Option<Identifier> {
    let token = self.cur_token.clone();
    let value = self.cur_token.literal().to_string();
    Some(Identifier::new(token, value))
  }

  fn parse_prefix(&mut self) -> Option<PrefixExpression> {
    let token = self.cur_token.clone();
    let op = self.cur_token.literal().to_string();
    self.next_token();
    let right = self.parse_expression(Precedence::Prefix)?;
    Some(PrefixExpression::new(token, op, right))
  }

  fn parse_infix(&mut self, left: Expression) -> Option<InfixExpression> {
    let token = self.cur_token.clone();
    let op = self.cur_token.literal().to_string();
    let precedence = self.current_precedence();
    self.next_token();
    let right = self.parse_expression(precedence)?;
    Some(InfixExpression::new(token, left, op, right))
  }

  fn parse_if(&mut self) -> Option<IfExpression> {
    let token = self.cur_token.clone();
    let parens = if self.peek_is(TokenType::LParen) {
      self.next_token();
      true
    } else {
      false
    };
    if self.peek_is(TokenType::LBrace) {
      self.if_block_error();
      return None;
    }
    self.next_token();
    let condition = self.parse_expression(Precedence::Lowest)?;
    if parens && !self.expect_peek(TokenType::RParen) {
      return None;
    }
    if !self.expect_peek(TokenType::LBrace) {
      return None;
    }
    let consequence = self.parse_block()?;
    let alternative = if self.maybe_peek(TokenType::Else) {
      if self.maybe_peek(TokenType::LBrace) {
        Some(self.parse_block().map(Alternative::Block)?)
      } else if self.maybe_peek(TokenType::If) {
        Some(self.parse_if().map(|ie| Alternative::If(Box::new(ie)))?)
      } else {
        self.if_else_error();
        return None;
      }
    } else {
      None
    };
    Some(IfExpression::new(
      token,
      condition,
      consequence,
      alternative,
    ))
  }

  fn parse_function(&mut self) -> Option<FunctionExpression> {
    let token = self.cur_token.clone();
    if !self.expect_peek(TokenType::LParen) {
      return None;
    }
    let parameters = self.parse_function_params();
    if !self.expect_peek(TokenType::LBrace) {
      return None;
    }
    let body = self.parse_block()?;
    Some(FunctionExpression::new(token, parameters, body))
  }

  fn parse_function_params(&mut self) -> Vec<Identifier> {
    let mut idents = vec![];
    if self.maybe_peek(TokenType::RParen) {
      return idents;
    }
    if !self.expect_peek(TokenType::Ident) {
      return idents;
    }
    idents.push(Identifier::new(
      self.cur_token.clone(),
      self.cur_token.literal().to_string(),
    ));
    while self.maybe_peek(TokenType::Comma) {
      if !self.expect_peek(TokenType::Ident) {
        return idents;
      }
      idents.push(Identifier::new(
        self.cur_token.clone(),
        self.cur_token.literal().to_string(),
      ));
    }
    self.expect_peek(TokenType::RParen);
    idents
  }

  fn parse_call(&mut self, function: Expression) -> Option<CallExpression> {
    Some(CallExpression::new(
      self.cur_token.clone(),
      function,
      self.parse_call_args(),
    ))
  }

  fn parse_call_args(&mut self) -> Vec<Expression> {
    let mut args = vec![];
    if self.maybe_peek(TokenType::RParen) {
      return args;
    }
    self.next_token();
    let Some(arg) = self.parse_expression(Precedence::Lowest) else {
      return args;
    };
    args.push(arg);
    while self.maybe_peek(TokenType::Comma) {
      self.next_token();
      let Some(arg) = self.parse_expression(Precedence::Lowest) else {
        return args;
      };
      args.push(arg);
    }
    self.expect_peek(TokenType::RParen);
    args
  }

  fn parse_block(&mut self) -> Option<BlockExpression> {
    let mut block = BlockExpression::new(self.cur_token.clone(), vec![]);
    self.next_token();
    while !self.current_is(TokenType::RBrace) && !self.current_is(TokenType::Eof) {
      if let Some(stmt) = self.parse_statement(true) {
        block.push_statement(stmt);
      }
      self.next_token();
    }
    if !self.current_is(TokenType::RBrace) {
      self.token_error(TokenType::RBrace, &self.cur_token.clone());
      return None;
    }
    Some(block)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    lexer::crab::CrabLexer,
    parser::ast::{Expression, Integer, Statement},
  };

  // --- Statement Test Helpers ---

  fn is_normal<T: Sized + Send + Sync + Unpin>() {}

  fn test_parser_errors<L: Lexer>(parser: &CrabParser<L>) {
    let errors = &parser.errors;
    if !errors.is_empty() {
      println!("parser has {} errors", errors.len());
      for err in errors {
        println!("parser error: {}", err);
      }
    }
    assert_eq!(errors.len(), 0, "parser returned errors");
  }

  fn test_let_statement(stmt: &Statement, name: &str, value: &Option<Expression>) -> bool {
    let Statement::Let(ls) = stmt else {
      panic!("stmt not LetStatement, got: {:?}", stmt);
    };
    assert_eq!(ls.token().literal(), "let", "let token literal");
    assert_eq!(ls.name().value(), name, "let name value");
    assert_eq!(ls.name().token().literal(), name, "let name literal");
    assert_eq!(ls.value(), value, "let value");
    true
  }

  fn test_return_statement(stmt: &Statement, value: &Option<Expression>) -> bool {
    let Statement::Return(rs) = stmt else {
      panic!("stmt not ReturnStatement, got: {:?}", stmt);
    };
    assert_eq!(rs.token().literal(), "return", "token literal");
    assert_eq!(rs.value(), value, "token value");
    true
  }

  // --- Expression Test Helpers ---

  #[derive(Debug)]
  enum Expected {
    Integer(i32),
    Boolean(bool),
    String(String),
    Identifier(String),
    PrefixInteger(String, i32),
    PrefixBoolean(String, bool),
    PrefixIdentifier(String, String),
    InfixInteger(i32, String, i32),
    InfixBoolean(bool, String, bool),
    InfixIdentifier(String, String, String),
    IfIdentifier(String, String, String, String, Option<String>),
    Function(Vec<String>, String),
    Call(String, Vec<Expected>),
    Block(String),
  }

  fn test_expression_statement(stmt: &Statement, expected: &Expected) -> bool {
    if let (Statement::Let(ls), Expected::IfIdentifier(a, op, b, cons, alt)) = (stmt, expected) {
      let Expression::If(ie) = ls.value().as_ref().unwrap() else {
        panic!("let value not IfExpression, got: {:?}", ls.value());
      };
      return test_if_identifier(&ie, a, op, b, cons, alt.clone());
    } else if let (Statement::Block(bs), Expected::Block(ident)) = (stmt, expected) {
      return test_block(bs, ident);
    } else if let (Statement::Let(ls), Expected::Block(ident)) = (stmt, expected) {
      let Expression::Block(be) = ls.value().as_ref().unwrap() else {
        panic!("let value not BlockExpression, got: {:?}", ls.value());
      };
      return test_block(be, ident);
    }

    let Statement::Expression(es) = stmt else {
      panic!("stmt not ExpressionStatement, got: {:?}", stmt);
    };
    match (es.expr(), expected) {
      (Expression::Integer(i), Expected::Integer(val)) => test_integer(i, *val),
      (Expression::Boolean(b), Expected::Boolean(val)) => test_boolean(b, *val),
      (Expression::String(s), Expected::String(val)) => test_string(s, val),
      (Expression::Identifier(ident), Expected::Identifier(val)) => test_identifier(ident, val),
      (Expression::Prefix(pe), Expected::PrefixInteger(op, val)) => {
        test_prefix_integer(pe, op, *val)
      }
      (Expression::Prefix(pe), Expected::PrefixBoolean(op, val)) => {
        test_prefix_boolean(pe, op, *val)
      }
      (Expression::Prefix(pe), Expected::PrefixIdentifier(op, val)) => {
        test_prefix_identifier(pe, op, val)
      }
      (Expression::Infix(ie), Expected::InfixInteger(a, op, b)) => {
        test_infix_integer(ie, *a, op, *b)
      }
      (Expression::Infix(ie), Expected::InfixBoolean(a, op, b)) => {
        test_infix_boolean(ie, *a, op, *b)
      }
      (Expression::Infix(ie), Expected::InfixIdentifier(a, op, b)) => {
        test_infix_identifier(ie, a, op, b)
      }
      (Expression::If(ie), Expected::IfIdentifier(a, op, b, cons, alt)) => {
        test_if_identifier(ie, a, op, b, cons, alt.clone())
      }
      (Expression::Function(fe), Expected::Function(params, body)) => {
        test_function_expr(fe, params, body)
      }
      (Expression::Call(ce), Expected::Call(name, exp)) => test_call_expr(ce, name, exp),
      (Expression::Block(be), Expected::Block(val)) => test_block(be, val),
      _ => panic!(
        "expression combination not supported, got: '{}' -> {:?}",
        es.expr(),
        expected
      ),
    }
  }

  fn test_integer(i: &Integer, value: i32) -> bool {
    assert_eq!(i.value(), value, "integer value");
    assert_eq!(i.token().literal(), &value.to_string(), "integer literal");
    true
  }

  fn test_boolean(b: &Boolean, value: bool) -> bool {
    assert_eq!(b.value(), value, "boolean value");
    assert_eq!(b.token().literal(), &value.to_string(), "boolean literal");
    true
  }

  fn test_string(s: &StringValue, value: &str) -> bool {
    assert_eq!(s.value(), value, "string value");
    assert_eq!(s.token().literal(), &value.to_string(), "value literal");
    true
  }

  fn test_identifier(ident: &Identifier, value: &str) -> bool {
    assert_eq!(ident.value(), value, "identifier value");
    assert_eq!(ident.token().literal(), value, "identifier literal");
    true
  }

  fn test_prefix_integer(pe: &PrefixExpression, op: &str, value: i32) -> bool {
    assert_eq!(pe.op(), op, "prefix integer operator");
    let Expression::Integer(i) = pe.right() else {
      panic!("right expression not Integer, got: {:?}", pe.right());
    };
    test_integer(i, value)
  }

  fn test_prefix_boolean(pe: &PrefixExpression, op: &str, value: bool) -> bool {
    assert_eq!(pe.op(), op, "prefix boolean operator");
    let Expression::Boolean(b) = pe.right() else {
      panic!("right expression not Boolean, got: {:?}", pe.right());
    };
    test_boolean(b, value)
  }

  fn test_prefix_identifier(pe: &PrefixExpression, op: &str, value: &str) -> bool {
    assert_eq!(pe.op(), op, "prefix identifier operator");
    let Expression::Identifier(i) = pe.right() else {
      panic!("right expression not Identifier, got: {:?}", pe.right());
    };
    test_identifier(i, value)
  }

  fn test_infix_integer(ie: &InfixExpression, left: i32, op: &str, right: i32) -> bool {
    assert_eq!(ie.op(), op, "infix integer operator");
    let Expression::Integer(a) = ie.left() else {
      panic!("left expression not Integer, got: {:?}", ie.left());
    };
    let Expression::Integer(b) = ie.right() else {
      panic!("right expression not Integer, got: {:?}", ie.right());
    };
    test_integer(a, left);
    test_integer(b, right);
    true
  }

  fn test_infix_boolean(ie: &InfixExpression, left: bool, op: &str, right: bool) -> bool {
    assert_eq!(ie.op(), op, "infix boolean operator");
    let Expression::Boolean(a) = ie.left() else {
      panic!("left expression not Boolean, got: {:?}", ie.left());
    };
    let Expression::Boolean(b) = ie.right() else {
      panic!("right expression not Boolean, got: {:?}", ie.right());
    };
    test_boolean(a, left);
    test_boolean(b, right);
    true
  }

  fn test_infix_identifier(ie: &InfixExpression, left: &str, op: &str, right: &str) -> bool {
    assert_eq!(ie.op(), op, "infix identifier operator");
    let Expression::Identifier(a) = ie.left() else {
      panic!("left expression not Identifier, got: {:?}", ie.left());
    };
    let Expression::Identifier(b) = ie.right() else {
      panic!("right expression not Identifier, got: {:?}", ie.right());
    };
    test_identifier(a, left);
    test_identifier(b, right);
    true
  }

  fn test_if_identifier(
    ie: &IfExpression,
    left: &str,
    op: &str,
    right: &str,
    cons: &str,
    alt: Option<String>,
  ) -> bool {
    let Expression::Infix(infix) = ie.condition() else {
      panic!(
        "condition expression not InfixExpression, got: {:?}",
        ie.condition()
      );
    };
    test_infix_identifier(infix, left, op, right);

    let Some(Statement::Expression(es)) = ie.consequence().statements().first() else {
      panic!(
        "consequence is not an ExpressionStatement, got: {:?}",
        ie.consequence()
      );
    };
    let Expression::Identifier(ident) = es.expr() else {
      panic!(
        "consequence expression not Identifier, got: {:?}",
        es.expr()
      );
    };
    test_identifier(ident, cons);
    assert_eq!(ie.alternative().as_ref().map(|a| a.to_string()), alt);
    true
  }

  fn test_function_expr(fe: &FunctionExpression, params: &[String], body: &str) -> bool {
    assert_eq!(fe.parameters().len(), params.len(), "function param length");
    for (i, param) in fe.parameters().iter().enumerate() {
      test_identifier(param, params[i].as_str());
    }
    assert_eq!(fe.body().to_string(), body, "function body to_string");
    true
  }

  fn test_call_expr(ce: &CallExpression, name: &str, expected: &[Expected]) -> bool {
    assert_eq!(ce.function().to_string(), name, "call name");
    assert_eq!(ce.arguments().len(), expected.len(), "call argument length");
    for (i, exp) in expected.iter().enumerate() {
      match exp {
        Expected::Integer(expected) => {
          let Expression::Integer(ie) = &ce.arguments()[i] else {
            panic!(
              "call argument[{}] not Integer, got: {:?}",
              i,
              ce.arguments()[i],
            );
          };
          test_integer(ie, *expected);
        }
        Expected::InfixInteger(a, op, b) => {
          let Expression::Infix(ie) = &ce.arguments()[i] else {
            panic!(
              "call argument[{}] not InfixExpression, got: {:?}",
              i,
              ce.arguments()[i],
            );
          };
          test_infix_integer(&ie, *a, op, *b);
        }
        _ => panic!(
          "call expression combination not supported, got: '{}' -> {:?}",
          ce, exp
        ),
      }
    }
    true
  }

  fn test_block(be: &BlockExpression, value: &str) -> bool {
    assert_eq!(be.statements().len(), 1, "block statement length");
    let Statement::Expression(es) = &be.statements()[0] else {
      panic!(
        "block statement not ExpressionStatement, got: {:?}",
        be.statements()[0]
      );
    };
    let Expression::Identifier(ident) = es.expr() else {
      panic!("block expression not Identifier, got: {:?}", es.expr());
    };
    test_identifier(ident, value)
  }

  // --- CrabParser Test Cases ---

  #[test]
  fn crab_parser_normal_types() {
    is_normal::<CrabParser<CrabLexer>>();
  }

  #[test]
  fn crab_parser_let_statements() {
    let input = r#"
      let x = 5;
      let y = 10;
      let foobar = 838383;
      let a;
      let b = c;
      let z = true;
    "#;

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 6, "statement length");

    let expected = [
      (
        "x",
        Some(Expression::Integer(Integer::new(
          Token::new(TokenType::Int, "5"),
          5,
        ))),
      ),
      (
        "y",
        Some(Expression::Integer(Integer::new(
          Token::new(TokenType::Int, "10"),
          10,
        ))),
      ),
      (
        "foobar",
        Some(Expression::Integer(Integer::new(
          Token::new(TokenType::Int, "838383"),
          838383,
        ))),
      ),
      ("a", None),
      (
        "b",
        Some(Expression::Identifier(Identifier::new(
          Token::new(TokenType::Ident, "c"),
          "c".into(),
        ))),
      ),
      (
        "z",
        Some(Expression::Boolean(Boolean::new(
          Token::new(TokenType::True, "true"),
          true,
        ))),
      ),
    ];
    for (i, (ident, exp)) in expected.iter().enumerate() {
      let stmt = &program.statements()[i];
      assert!(test_let_statement(stmt, ident, exp), "test[{}]", i);
    }
  }

  #[test]
  fn crab_parser_return_statements() {
    let input = r#"
      return 5;
      return true;;
      return 993322;
      return;
      return abc;
      return false;
    "#;

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 6, "statement length");

    let expected = [
      Some(Expression::Integer(Integer::new(
        Token::new(TokenType::Int, "5"),
        5,
      ))),
      Some(Expression::Boolean(Boolean::new(
        Token::new(TokenType::True, "true"),
        true,
      ))),
      Some(Expression::Integer(Integer::new(
        Token::new(TokenType::Int, "993322"),
        993322,
      ))),
      None,
      Some(Expression::Identifier(Identifier::new(
        Token::new(TokenType::Ident, "abc"),
        "abc".into(),
      ))),
      Some(Expression::Boolean(Boolean::new(
        Token::new(TokenType::False, "false"),
        false,
      ))),
    ];
    for (i, exp) in expected.iter().enumerate() {
      let stmt = &program.statements()[i];
      assert!(test_return_statement(stmt, exp), "test[{}]", i);
    }
  }

  #[test]
  fn crab_parser_integer_expression() {
    let input = "5;";

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 1, "statement length");

    assert!(test_expression_statement(
      &program.statements()[0],
      &Expected::Integer(5),
    ));
  }

  #[test]
  fn crab_parser_boolean_expression() {
    let input = ";true; false;;";

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 2, "statement length");

    assert!(
      test_expression_statement(&program.statements()[0], &Expected::Boolean(true),),
      "test[1]"
    );
    assert!(
      test_expression_statement(&program.statements()[1], &Expected::Boolean(false),),
      "test[2]"
    );
  }

  #[test]
  fn crab_parser_string_expression() {
    let input = "'hello world'";

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 1, "statement length");

    assert!(
      test_expression_statement(
        &program.statements()[0],
        &Expected::String("hello world".into())
      ),
      "statement value"
    );
  }

  #[test]
  fn crab_parser_identifier_expression() {
    let input = "foobar;";

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 1, "statement length");

    assert!(test_expression_statement(
      &program.statements()[0],
      &Expected::Identifier("foobar".into()),
    ));
  }

  #[test]
  fn crab_parser_prefix_expression() {
    let tests = [
      ("!5;", Expected::PrefixInteger("!".into(), 5)),
      ("-15;", Expected::PrefixInteger("-".into(), 15)),
      ("!a;", Expected::PrefixIdentifier("!".into(), "a".into())),
      ("-a", Expected::PrefixIdentifier("-".into(), "a".into())),
      ("!true", Expected::PrefixBoolean("!".into(), true)),
      ("!false", Expected::PrefixBoolean("!".into(), false)),
    ];

    for (input, expected) in tests {
      let mut parser = CrabParser::from(input);
      let program = parser.parse_program();

      test_parser_errors(&parser);
      assert_eq!(program.statements().len(), 1, "statement length");

      assert!(test_expression_statement(
        &program.statements()[0],
        &expected
      ));
    }
  }

  #[test]
  fn crab_parser_infix_expression() {
    let tests = [
      ("5 + 5", Expected::InfixInteger(5, "+".into(), 5)),
      ("5 - 5", Expected::InfixInteger(5, "-".into(), 5)),
      ("5 * 5", Expected::InfixInteger(5, "*".into(), 5)),
      ("5 / 5", Expected::InfixInteger(5, "/".into(), 5)),
      ("5 > 5", Expected::InfixInteger(5, ">".into(), 5)),
      ("5 < 5", Expected::InfixInteger(5, "<".into(), 5)),
      ("5 == 5", Expected::InfixInteger(5, "==".into(), 5)),
      ("5 != 5", Expected::InfixInteger(5, "!=".into(), 5)),
      (
        "a + a",
        Expected::InfixIdentifier("a".into(), "+".into(), "a".into()),
      ),
      (
        "a - a",
        Expected::InfixIdentifier("a".into(), "-".into(), "a".into()),
      ),
      (
        "a * a",
        Expected::InfixIdentifier("a".into(), "*".into(), "a".into()),
      ),
      (
        "a / a",
        Expected::InfixIdentifier("a".into(), "/".into(), "a".into()),
      ),
      (
        "a > a",
        Expected::InfixIdentifier("a".into(), ">".into(), "a".into()),
      ),
      (
        "a < a",
        Expected::InfixIdentifier("a".into(), "<".into(), "a".into()),
      ),
      (
        "a == a",
        Expected::InfixIdentifier("a".into(), "==".into(), "a".into()),
      ),
      (
        "a != a",
        Expected::InfixIdentifier("a".into(), "!=".into(), "a".into()),
      ),
      (
        "true == true",
        Expected::InfixBoolean(true, "==".into(), true),
      ),
      (
        "true != false",
        Expected::InfixBoolean(true, "!=".into(), false),
      ),
      (
        "false == false",
        Expected::InfixBoolean(false, "==".into(), false),
      ),
    ];

    for (input, expected) in tests {
      let mut parser = CrabParser::from(input);
      let program = parser.parse_program();

      test_parser_errors(&parser);
      assert_eq!(program.statements().len(), 1, "statement length");

      assert!(test_expression_statement(
        &program.statements()[0],
        &expected
      ));
    }
  }

  #[test]
  fn crab_parser_if_expression() {
    let tests = [
      (
        "let a = if (x < y) { z }",
        Expected::IfIdentifier("x".into(), "<".into(), "y".into(), "z".into(), None),
      ),
      (
        "let a = if x == y { z; }",
        Expected::IfIdentifier("x".into(), "==".into(), "y".into(), "z".into(), None),
      ),
      (
        "let a = if (x < y) { a } else { b }",
        Expected::IfIdentifier(
          "x".into(),
          "<".into(),
          "y".into(),
          "a".into(),
          Some("{ b; }".into()),
        ),
      ),
      (
        "let a = if x == y { a; } else { b; true; };",
        Expected::IfIdentifier(
          "x".into(),
          "==".into(),
          "y".into(),
          "a".into(),
          Some("{ b; true; }".into()),
        ),
      ),
      (
        "let a = if x != y { z; } else if (a > b) { c }",
        Expected::IfIdentifier(
          "x".into(),
          "!=".into(),
          "y".into(),
          "z".into(),
          Some("if (a > b) { c; }".into()),
        ),
      ),
      (
        "let a = if x != y { z } else if (a > b) { c } else { return d };",
        Expected::IfIdentifier(
          "x".into(),
          "!=".into(),
          "y".into(),
          "z".into(),
          Some("if (a > b) { c; } else { return d; }".into()),
        ),
      ),
    ];

    for (i, (input, exp)) in tests.iter().enumerate() {
      let mut parser = CrabParser::from(*input);
      let program = parser.parse_program();

      test_parser_errors(&parser);
      assert_eq!(
        program.statements().len(),
        1,
        "test[{}] statement length",
        i
      );

      assert!(
        test_expression_statement(&program.statements()[0], exp),
        "test[{}]",
        i
      );
    }
  }

  #[test]
  fn crab_parser_if_statements() {
    let input = r#"
      let a = if true { 10 }
      true
    "#;
    let mut parser = CrabParser::from(input);
    let _ = parser.parse_program();

    assert_eq!(parser.errors.len(), 1, "error len");
    assert_eq!(
      parser.errors[0], "expected next token to be SEMICOLON, got BOOLEAN(true)",
      "if expression requires semi",
    );

    let input = r#"
      if true { 10 }
      true
    "#;
    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 2, "statement length");
    assert!(
      matches!(program.statements()[0], Statement::If(_)),
      "if statement"
    );
    assert!(
      matches!(program.statements()[1], Statement::Expression(_)),
      "expr statement"
    );
  }

  #[test]
  fn crab_parser_function_expression() {
    let tests = [
      (
        "fn(x, y) { x + y }",
        Expected::Function(vec!["x".into(), "y".into()], "{ (x + y); }".into()),
      ),
      ("fn() {}", Expected::Function(vec![], "{}".into())),
      (
        "fn(x) {}",
        Expected::Function(vec!["x".into()], "{}".into()),
      ),
      (
        "fn(x, y, z) {};",
        Expected::Function(vec!["x".into(), "y".into(), "z".into()], "{}".into()),
      ),
    ];

    for (i, (input, exp)) in tests.iter().enumerate() {
      let mut parser = CrabParser::from(*input);
      let program = parser.parse_program();

      test_parser_errors(&parser);
      assert_eq!(
        program.statements().len(),
        1,
        "test[{}] statement length",
        i
      );

      assert!(
        test_expression_statement(&program.statements()[0], exp),
        "test[{}]",
        i
      );
    }
  }

  #[test]
  fn parser_call_expression() {
    let (input, expected) = (
      "add(1, 2 * 3, 4 + 5);",
      Expected::Call(
        "add".into(),
        vec![
          Expected::Integer(1),
          Expected::InfixInteger(2, "*".into(), 3),
          Expected::InfixInteger(4, "+".into(), 5),
        ],
      ),
    );

    let mut parser = CrabParser::from(input);
    let program = parser.parse_program();

    test_parser_errors(&parser);
    assert_eq!(program.statements().len(), 1, "statement length");

    assert!(test_expression_statement(
      &program.statements()[0],
      &expected,
    ));
  }

  #[test]
  fn crab_parser_block_expression() {
    let tests = [
      ("{ x };", Expected::Block("x".into())),
      ("let a = { y; };", Expected::Block("y".into())),
    ];

    for (i, (input, exp)) in tests.iter().enumerate() {
      let mut parser = CrabParser::from(*input);
      let program = parser.parse_program();

      test_parser_errors(&parser);
      assert_eq!(
        program.statements().len(),
        1,
        "test[{}] statement length",
        i
      );

      assert!(
        test_expression_statement(&program.statements()[0], exp),
        "test[{}]",
        i
      );
    }
  }

  #[test]
  fn crab_parser_precedence() {
    let tests = [
      ("-a * b;", "((-a) * b);"),
      ("!-a;", "(!(-a));"),
      ("a + b + c;", "((a + b) + c);"),
      ("a + b - c;", "((a + b) - c);"),
      ("a * b * c;", "((a * b) * c);"),
      ("a * b / c;", "((a * b) / c);"),
      ("a + b / c;", "(a + (b / c));"),
      ("a + b * c + d / e - f;", "(((a + (b * c)) + (d / e)) - f);"),
      ("3 + 4; -5 * 5;", "(3 + 4); ((-5) * 5);"),
      ("5 > 4 == 3 < 4;", "((5 > 4) == (3 < 4));"),
      ("5 < 4 != 3 > 4;", "((5 < 4) != (3 > 4));"),
      (
        "3 + 4 * 5 == 3 * 1 + 4 * 5",
        "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));",
      ),
      (
        "3 + 4 * 5 == 3 * 1 + 4 * 5",
        "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));",
      ),
      ("true;", "true;"),
      ("false;", "false;"),
      ("3 > 5 == false;", "((3 > 5) == false);"),
      ("3 < 5 == true;", "((3 < 5) == true);"),
      ("!true + 5;", "((!true) + 5);"),
      ("!false + 5 * 3;", "((!false) + (5 * 3));"),
      ("1 + (2 + 3) + 4;", "((1 + (2 + 3)) + 4);"),
      ("(5 + 5) * 2", "((5 + 5) * 2);"),
      ("2 / (5 + 5)", "(2 / (5 + 5));"),
      ("-(5 + 5);", "(-(5 + 5));"),
      ("!(true == true)", "(!(true == true));"),
      ("a + { 5*2; 0 } * c", "(a + ({ (5 * 2); 0; } * c));"),
      ("a + add(b * c) + d;", "((a + add((b * c))) + d);"),
      (
        "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8));",
        "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)));",
      ),
      (
        "add(a + b + c * d / f + g)",
        "add((((a + b) + ((c * d) / f)) + g));",
      ),
      ("nil + 1 * nil > true", "((nil + (1 * nil)) > true);"),
    ];

    for (i, (input, output)) in tests.iter().enumerate() {
      let mut parser = CrabParser::from(*input);
      let program = parser.parse_program();

      test_parser_errors(&parser);
      assert_eq!(&program.to_string(), output, "test[{}]", i);
    }
  }

  #[test]
  fn crab_parser_error_handling() {
    let tests = [
      (
        "if (true { a }",
        vec!["expected next token to be RPAREN, got LBRACE({)"],
      ),
      (
        "if true) { a }",
        vec![
          "expected next token to be LBRACE, got RPAREN())",
          "no prefix parse function for RPAREN())",
        ],
      ),
      (
        "if { true } { false }",
        vec!["if condition must not be a block expression"],
      ),
      (
        "if (true) a else { b }",
        vec![
          "expected next token to be LBRACE, got IDENTIFIER(a)",
          "expected next token to be SEMICOLON, got ELSE(else)",
          "no prefix parse function for ELSE(else)",
        ],
      ),
      (
        "if (true) { a } else b",
        vec!["if else must be followed by a block or another if"],
      ),
    ];

    for (i, (input, errors)) in tests.iter().enumerate() {
      let mut parser = CrabParser::from(*input);
      parser.parse_program();

      assert_eq!(
        parser.errors.len(),
        errors.len(),
        "test[{}-1] error count: {:?}",
        i,
        parser.errors,
      );
      for (j, err) in errors.iter().enumerate() {
        assert_eq!(parser.errors[j], *err, "test[{}-{}-2] error value", i, j);
      }
    }
  }
}
