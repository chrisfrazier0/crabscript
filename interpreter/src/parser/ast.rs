use crate::lexer::token::Token;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
  Program(Program),
  Statement(Statement),
  Expression(Expression),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
  Let(LetStatement),
  Return(ReturnStatement),
  Expression(ExpressionStatement),
  If(IfExpression),
  Block(BlockExpression),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
  Nil(Nil),
  Integer(Integer),
  Boolean(Boolean),
  String(StringValue),
  Identifier(Identifier),
  Prefix(Box<PrefixExpression>),
  Infix(Box<InfixExpression>),
  If(Box<IfExpression>),
  Function(FunctionExpression),
  Call(Box<CallExpression>),
  Block(BlockExpression),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Alternative {
  If(Box<IfExpression>),
  Block(BlockExpression),
}

impl fmt::Display for Node {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Program(a) => a.fmt(f),
      Self::Statement(a) => a.fmt(f),
      Self::Expression(a) => a.fmt(f),
    }
  }
}

impl fmt::Display for Statement {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Let(a) => a.fmt(f),
      Self::Return(a) => a.fmt(f),
      Self::Expression(a) => a.fmt(f),
      Self::If(a) => a.fmt(f),
      Self::Block(a) => a.fmt(f),
    }
  }
}

impl fmt::Display for Expression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Nil(a) => a.fmt(f),
      Self::Integer(a) => a.fmt(f),
      Self::Boolean(a) => a.fmt(f),
      Self::String(a) => a.fmt(f),
      Self::Identifier(a) => a.fmt(f),
      Self::Prefix(a) => a.fmt(f),
      Self::Infix(a) => a.fmt(f),
      Self::If(a) => a.fmt(f),
      Self::Function(a) => a.fmt(f),
      Self::Call(a) => a.fmt(f),
      Self::Block(a) => a.fmt(f),
    }
  }
}

impl fmt::Display for Alternative {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::If(a) => a.fmt(f),
      Self::Block(a) => a.fmt(f),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Program {
  statements: Vec<Statement>,
}

impl fmt::Display for Program {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut out = vec![];
    for stmt in &self.statements {
      out.push(stmt.to_string());
    }
    write!(f, "{}", out.join(" "))
  }
}

impl Program {
  pub fn new(statements: Vec<Statement>) -> Self {
    Self { statements }
  }

  pub fn statements(&self) -> &Vec<Statement> {
    &self.statements
  }

  pub fn push_statement(&mut self, stmt: Statement) {
    self.statements.push(stmt)
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetStatement {
  token: Token,
  name: Identifier,
  value: Option<Expression>,
}

impl fmt::Display for LetStatement {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let value = self
      .value
      .as_ref()
      .map(|v| v.to_string())
      .unwrap_or("nil".to_string());
    write!(f, "let {} = {};", self.name, value)
  }
}

impl LetStatement {
  pub fn new(token: Token, name: Identifier, value: Option<Expression>) -> Self {
    Self { token, name, value }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn name(&self) -> &Identifier {
    &self.name
  }

  pub fn value(&self) -> &Option<Expression> {
    &self.value
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStatement {
  token: Token,
  value: Option<Expression>,
}

impl fmt::Display for ReturnStatement {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let value = self
      .value
      .as_ref()
      .map(|v| v.to_string())
      .unwrap_or("nil".to_string());
    write!(f, "return {};", value)
  }
}

impl ReturnStatement {
  pub fn new(token: Token, value: Option<Expression>) -> Self {
    Self { token, value }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn value(&self) -> &Option<Expression> {
    &self.value
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpressionStatement {
  token: Token,
  expr: Expression,
}

impl fmt::Display for ExpressionStatement {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{};", self.expr)
  }
}

impl ExpressionStatement {
  pub fn new(token: Token, expr: Expression) -> Self {
    Self { token, expr }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn expr(&self) -> &Expression {
    &self.expr
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Nil {
  token: Token,
}

impl fmt::Display for Nil {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "nil")
  }
}

impl Nil {
  pub fn new(token: Token) -> Self {
    Self { token }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Integer {
  token: Token,
  value: i32,
}

impl fmt::Display for Integer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.value.fmt(f)
  }
}

impl Integer {
  pub fn new(token: Token, value: i32) -> Self {
    Self { token, value }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn value(&self) -> i32 {
    self.value
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Boolean {
  token: Token,
  value: bool,
}

impl fmt::Display for Boolean {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.value.fmt(f)
  }
}

impl Boolean {
  pub fn new(token: Token, value: bool) -> Self {
    Self { token, value }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn value(&self) -> bool {
    self.value
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StringValue {
  token: Token,
  value: String,
}

impl fmt::Display for StringValue {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.value.fmt(f)
  }
}

impl StringValue {
  pub fn new(token: Token, value: String) -> Self {
    Self { token, value }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn value(&self) -> &str {
    &self.value
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
  token: Token,
  value: String,
}

impl fmt::Display for Identifier {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.value.fmt(f)
  }
}

impl Identifier {
  pub fn new(token: Token, value: String) -> Self {
    Self { token, value }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn value(&self) -> &str {
    &self.value
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpression {
  token: Token,
  op: String,
  right: Expression,
}

impl fmt::Display for PrefixExpression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({}{})", self.op, self.right)
  }
}

impl PrefixExpression {
  pub fn new(token: Token, op: String, right: Expression) -> Self {
    Self { token, op, right }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn op(&self) -> &str {
    &self.op
  }

  pub fn right(&self) -> &Expression {
    &self.right
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InfixExpression {
  token: Token,
  left: Expression,
  op: String,
  right: Expression,
}

impl fmt::Display for InfixExpression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({} {} {})", self.left, self.op, self.right)
  }
}

impl InfixExpression {
  pub fn new(token: Token, left: Expression, op: String, right: Expression) -> Self {
    Self {
      token,
      left,
      op,
      right,
    }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn left(&self) -> &Expression {
    &self.left
  }

  pub fn op(&self) -> &str {
    &self.op
  }

  pub fn right(&self) -> &Expression {
    &self.right
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpression {
  token: Token,
  condition: Expression,
  consequence: BlockExpression,
  alternative: Option<Alternative>,
}

impl fmt::Display for IfExpression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut out = format!("if {} {}", self.condition, self.consequence);
    if let Some(alt) = &self.alternative {
      out.push_str(&format!(" else {}", alt));
    }
    write!(f, "{}", out)
  }
}

impl IfExpression {
  pub fn new(
    token: Token,
    condition: Expression,
    consequence: BlockExpression,
    alternative: Option<Alternative>,
  ) -> Self {
    Self {
      token,
      condition,
      consequence,
      alternative,
    }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn condition(&self) -> &Expression {
    &self.condition
  }

  pub fn consequence(&self) -> &BlockExpression {
    &self.consequence
  }

  pub fn alternative(&self) -> &Option<Alternative> {
    &self.alternative
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionExpression {
  token: Token,
  parameters: Vec<Identifier>,
  body: BlockExpression,
}

impl fmt::Display for FunctionExpression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let params = self
      .parameters
      .iter()
      .map(|p| p.to_string())
      .collect::<Vec<String>>()
      .join(", ");
    write!(f, "fn({}) {}", params, self.body)
  }
}

impl FunctionExpression {
  pub fn new(token: Token, parameters: Vec<Identifier>, body: BlockExpression) -> Self {
    Self {
      token,
      parameters,
      body,
    }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn parameters(&self) -> &Vec<Identifier> {
    &self.parameters
  }

  pub fn body(&self) -> &BlockExpression {
    &self.body
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpression {
  token: Token,
  function: Expression,
  arguments: Vec<Expression>,
}

impl fmt::Display for CallExpression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let args = self
      .arguments
      .iter()
      .map(|p| p.to_string())
      .collect::<Vec<String>>()
      .join(", ");
    write!(f, "{}({})", self.function, args)
  }
}

impl CallExpression {
  pub fn new(token: Token, function: Expression, arguments: Vec<Expression>) -> Self {
    Self {
      token,
      function,
      arguments,
    }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn function(&self) -> &Expression {
    &self.function
  }

  pub fn arguments(&self) -> &Vec<Expression> {
    &self.arguments
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockExpression {
  token: Token,
  statements: Vec<Statement>,
}

impl fmt::Display for BlockExpression {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut out = vec![];
    for stmt in &self.statements {
      out.push(stmt.to_string());
    }
    if out.is_empty() {
      write!(f, "{{}}")
    } else {
      write!(f, "{{ {} }}", out.join(" "))
    }
  }
}

impl BlockExpression {
  pub fn new(token: Token, statements: Vec<Statement>) -> Self {
    Self { token, statements }
  }

  pub fn token(&self) -> &Token {
    &self.token
  }

  pub fn statements(&self) -> &Vec<Statement> {
    &self.statements
  }

  pub fn push_statement(&mut self, stmt: Statement) {
    self.statements.push(stmt)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::lexer::token::TokenType;

  fn is_normal<T: Sized + Send + Sync + Unpin>() {}

  #[test]
  fn ast_normal_types() {
    is_normal::<Node>();
    is_normal::<Program>();
    is_normal::<Statement>();
    is_normal::<Expression>();
    is_normal::<LetStatement>();
    is_normal::<ReturnStatement>();
    is_normal::<ExpressionStatement>();
    is_normal::<Nil>();
    is_normal::<Integer>();
    is_normal::<Boolean>();
    is_normal::<Identifier>();
    is_normal::<PrefixExpression>();
    is_normal::<InfixExpression>();
    is_normal::<IfExpression>();
    is_normal::<FunctionExpression>();
    is_normal::<CallExpression>();
    is_normal::<BlockExpression>();
  }

  #[test]
  fn ast_program_to_string() {
    let program = Program::new(vec![Statement::Let(LetStatement::new(
      Token::new(TokenType::Let, "let"),
      Identifier::new(Token::new(TokenType::Ident, "myVar"), "myVar".into()),
      Some(Expression::Identifier(Identifier::new(
        Token::new(TokenType::Ident, "anotherVar"),
        "anotherVar".into(),
      ))),
    ))]);

    assert_eq!(program.to_string(), "let myVar = anotherVar;");

    let program = Program::new(vec![Statement::Return(ReturnStatement::new(
      Token::new(TokenType::Return, "return"),
      Some(Expression::Nil(Nil::new(Token::new(TokenType::Nil, "nil")))),
    ))]);

    assert_eq!(program.to_string(), "return nil;")
  }
}
