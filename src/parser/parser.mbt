pub struct Parser{
  input : Array[@lex.Token]
  mut curPos : Int
  output : @types.Syntax
} derive(Show)

fn isMatchId(self : Parser) -> Bool{ //fn add(x,y)
  match self.input[self.curPos] {
    @lex.Token::IDENTIFIER(_) => true
    _ => false
  }
}
pub fn getAst(self : Parser) -> @types.Syntax {
  self.parseProg()
  //let prog = self.parseProg()
  //println(prog)
}

fn parseProg(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} in parseProg Entry")
  let prog : @types.Syntax = parseTopLevel(self)
  // while self.input[self.curPos] == @lex.Token::FN || self.input[self.curPos] == @lex.Token::LET {
  //   prog.push(parseTopLevel(self))
  //   println("\{self.curPos} in parseProg parse back")
  //   if (self.curPos == self.input.length()-1){
  //     break
  //   }
  //   self.curPos+=1
  // }
  prog
}

//prog := let x : Int = 1;let x... ;fn add();fn main(){add(x,y)};Unit

fn Parser::parseTopLevel(self : Parser) -> @types.Syntax {
  match self.input[self.curPos] {
    @lex.Token::LET => parseTopLetDecl(self)
    @lex.Token::FN => parseTopLevelFnDecl(self)
    _ => {
      println("Parse error in TopLevel!")
      panic()
    }
  }
}

fn Parser::parseTopLetDecl(self : Parser) -> @types.Syntax{  //let name : Type = _ ;stmt 
  self.curPos+=1
  let mut letName = ""
  match self.input[self.curPos]{
    @lex.Token::IDENTIFIER(s) => {letName = s;self.curPos+=1}
    _ => {println("Excepted an identifier in TopLetDecl!"); panic()}
  }
  if self.input[self.curPos]!= @lex.Token::COLON{
    println("Excepted ':' in TopLetDecl!"); panic()
  }
  self.curPos+=1
  let ty = parseType(self)
  self.curPos+=1
  if self.input[self.curPos]!= @lex.Token::ASSIGN{
    println("Excepted '=' in TopLetDecl!"); panic()
  }
  self.curPos+=1
  let e = parseExpr(self)
  self.curPos+=1
  if self.input[self.curPos]!= @lex.Token::SEMICOLON{
    println("Excepted ';' at the end of TopLetDecl!"); panic()
  }
  self.curPos+=1
  if (self.curPos >= self.input.length()){
    return @types.Let((letName,ty),e,Unit)
  }
  let toplev = parseTopLevel(self)
  return @types.Let((letName,ty),e,toplev)
}

fn Parser::parseTopLevelFnDecl(self : Parser) -> @types.Syntax{
  self.curPos+=1
  match self.input[self.curPos]{
    @lex.IDENTIFIER("main") | @lex.IDENTIFIER("init") => parseMainFnDecl(self)
    @lex.IDENTIFIER(_) => parseTopFnDecl(self)
    _ => {
      println("Parse error in TopLevelFnDecl!")
      panic()
    }
  }
}

fn Parser::parseMainFnDecl(self : Parser) -> @types.Syntax{
  match self.input[self.curPos]{
    @lex.IDENTIFIER(s) => {
      self.curPos+=1
      let fb = parseFnBody(self)
      let fun = @types.Fundef::{name:(s,Fun([],Unit)),args:[],body:fb}
      self.curPos+=1
      if (self.input[self.curPos] != @lex.Token::SEMICOLON) {
        println("Expected ';' in TopFnDecl!")
        panic()
      }
      self.curPos+=1
      if (self.curPos >= self.input.length()){
        return @types.LetRec(fun,@types.Syntax::Unit)
      }
      let top = parseTopLevel(self)
      @types.LetRec(fun,top)
    }
    _ => panic()
  }
}

fn Parser::parseTopFnDecl(self : Parser) -> @types.Syntax {
  let mut name = ""
  match self.input[self.curPos]{
    @lex.Token::IDENTIFIER(s) => name = s
    _ => panic()
  }
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::LPAREN) {
    println("Expected '(' after parameters in TopFnDecl!")
    panic()
  }
  self.curPos+=1
  let mut pl : Array[(String, @types.Type)] = []
  if (self.input[self.curPos] == @lex.Token::RPAREN) {// 空参数列表
    self.curPos+=1
  } else {
    pl = parseParamList(self)     // 非空参数列表
    if (self.input[self.curPos] != @lex.Token::RPAREN) {
        println( "Expected ')' after parameters in TopFnDecl!")
        panic()
    }
    self.curPos+=1
  }
  if (self.input[self.curPos] != @lex.Token::ARROW) {// 返回类型
    println("Expected '->' in TopFnDecl!")
    panic()
  } 
  self.curPos+=1
  let retty = parseType(self)
  self.curPos+=1
  let fb = parseFnBody(self)
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::SEMICOLON) {
    println("Expected ';' in TopFnDecl!")
    panic()
  }
  let argty:Array[@types.Type] = []
  for i in pl{
    argty.push(i.1)
  }
  let funty : @types.Type = Fun(argty,retty)
  let fun = @types.Fundef::{name : (name,funty),args : pl,body :fb}
  self.curPos+=1
  if (self.curPos >= self.input.length()){
    return @types.LetRec(fun,@types.Syntax::Unit)
  }
  let top = parseTopLevel(self)
  @types.LetRec(fun,top)
}


fn Parser::parseParamList(self : Parser) -> Array[(String, @types.Type)]{
  let paramList : Array[(String, @types.Type)] = []
  let p = parseParam(self)
  paramList.push(p)
  self.curPos+=1
  while (self.input[self.curPos] == @lex.Token::COMMA){
      self.curPos+=1
      paramList.push(parseParam(self))
      self.curPos+=1
  }
  paramList
}

fn Parser::parseParam(self : Parser) -> (String,@types.Type){
  match self.input[self.curPos] {
    @lex.IDENTIFIER(s) => {
      self.curPos+=1
      let ta = parseTypeAnnotation(self)
      (s,ta)
    }
    _ => {
      println("Parse error in Param (excepted an identifier)!")
      panic()
    }
  }
}

fn Parser::parseFnBody(self : Parser) -> @types.Syntax{
  if (self.input[self.curPos] != @lex.Token::LCURLYBRACKET){
    println("Excepted '{' in FnBody!")
    panic()
  }
  let stmt = parseStmt(self)
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::RCURLYBRACKET){
      println("Excepted '}' in FnBody!")
      panic()
  }
  stmt
}
fn Parser::parseNontopFnDecl(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} parseNontopFnDecl entry ")
  self.curPos+=1
  let mut name = ""
  match self.input[self.curPos]{
    @lex.Token::IDENTIFIER(s) => name = s
    _ => {
      println("Excepted an Identifier in NontopFnDecl")
      panic()
    } 
  }
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::LPAREN){
    println("Excepted '(' in NontopFnDecl")
    panic()
  }
  self.curPos+=1
  let mut pl : Array[(String, @types.Type)] = []
  if (self.input[self.curPos] == @lex.Token::RPAREN) {// 空参数列表
    self.curPos+=1
  } else {
    pl = parseNontopParamList(self)   // 非空参数列表
    //println("\{self.curPos} \{self.input[self.curPos]} after parameters ")
    //self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::RPAREN) {
        println( "Expected ')' after parameters in NontopFnDecl!")
        panic()
    }
    self.curPos+=1
  }
  let mut retty :@types.Type = @types.Type::Var({val:None})
  if (self.input[self.curPos] == @lex.Token::ARROW) {
    self.curPos+=1
    retty = parseType(self)
    self.curPos+=1
  } 
  //self.curPos+=1
  let body = parseFnBody(self)
  let argTy = []
  for i in pl{
    argTy.push(i.1)
  }
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::SEMICOLON) {
    println( "Expected ';' at the end of NontopFnDecl!")
    panic()
  }
  let stmt = parseStmt(self)
  let fun = @types.Fundef::{name : (name,Fun(argTy,retty)), args:pl, body:body}
  @types.LetRec(fun,stmt)
}

fn Parser::parseNontopParamList(self : Parser) -> Array[(String,@types.Type)] {
  let paramList : Array[(String, @types.Type)] = []
  let p = parseNontopParam(self)
  paramList.push(p)
  self.curPos+=1
  while (self.input[self.curPos] == @lex.Token::COMMA){
      self.curPos+=1
      paramList.push(parseNontopParam(self))
      self.curPos+=1
  }
  paramList
}

fn Parser::parseNontopParam(self : Parser) -> (String,@types.Type){
  match self.input[self.curPos] {
    @lex.IDENTIFIER(s) => {
      let backPoint = self.curPos
      self.curPos+=1
      let mut t : @types.Type= @types.Type::Var({val:None})
      if (self.input[self.curPos] == @lex.Token::COLON){
        t = parseTypeAnnotation(self)
      }
      else {self.curPos = backPoint}
      (s,t)
    }
    _ => {
      println("Parse error in parseNontopParam (excepted an identifier)!")
      panic()
    }
  }
}

fn Parser::parseStmt(self : Parser) -> @types.Syntax{
	let backPoint = self.curPos;
	self.curPos+=1
  //println("\{self.curPos} \{self.input[self.curPos]} in parseStmt")
  if (self.input[self.curPos] == @lex.Token::LET){
    self.curPos+=1
    if (self.input[self.curPos] == @lex.Token::LPAREN){
        return parseLetTupleStmt(self)
    }
    return parseLetStmt(self)
  }
  if (self.input[self.curPos] == @lex.Token::FN){
    return parseFnDeclStmt(self)
  }
  //区分assign_stmt和expr_stmt需要回溯Token
  // arr[i] = 1;stmt     arr[i]
  
  let mut flag = false
  if (true) {
    while (self.input[self.curPos] != @lex.RBRACKET && //]
    self.input[self.curPos] != @lex.LCURLYBRACKET && //{
    self.input[self.curPos] != @lex.SEMICOLON){ //;
      self.curPos+=1
    } 
    if (self.input[self.curPos] == @lex.Token::RBRACKET &&
    (self.input[self.curPos+1] == @lex.ASSIGN ||
    self.input[self.curPos+1] == @lex.LBRACKET)){
      flag = true
    }
    else {flag = false}
  }
  //println("\{self.input[self.curPos]} in parseStmt")
  self.curPos = backPoint
  self.curPos+=1
  if (flag){
      return parseAssignStmt(self)
  }
  //println("\{self.input[self.curPos]} in parseStmt")
  return parseExpr(self)
}


fn Parser::parseLetTupleStmt(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in LetTupleStmt")
  self.curPos+=1
  let arrId : Array[String] = []
  match self.input[self.curPos] {
    @lex.Token::IDENTIFIER(s) => arrId.push(s)
    _ => {
      //println("Excepted an identifier in LetTupleStmt!")
      panic()
    }
  }
  self.curPos+=1
  while (self.input[self.curPos] == @lex.Token::COMMA){
    self.curPos+=1
    match self.input[self.curPos] {
      @lex.Token::IDENTIFIER(s1) => arrId.push(s1)
      _ => {
        //println("Excepted an identifier in LetTupleStmt!")
        panic()
      }
    }
    self.curPos+=1
  }
  if (self.input[self.curPos] != @lex.Token::RPAREN){
    //println("Excepted ')' in LetTupleStmt!")
    panic()
  }
  self.curPos+=1
  let mut ty = @types.Type::Var({val:None})   //let x : Var{None} = 1
  if (self.input[self.curPos] == @lex.Token::COLON){
    ty = parseTypeAnnotation(self)
    self.curPos+=1
  }
  if (self.input[self.curPos] != @lex.Token::ASSIGN){
    //println("Excepted '=' in LetTupleStmt!")
    panic()
  }
  self.curPos+=1
  let e = parseExpr(self)
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::SEMICOLON){
    //println("Excepted ';' in LetTupleStmt!")
    panic()
  }
  let arrST = []
    match ty {
      Tuple(at) => for i=0;i<arrId.length();i=i+1{
                    arrST.push((arrId[i],at[i]))
                  }
      _ => for i=0;i<arrId.length();i=i+1{
                    arrST.push((arrId[i],ty))
            }
    }
  
  //self.curPos+=1
  let stmt = parseStmt(self)
  return LetTuple(arrST,e,stmt)  
}

fn Parser::parseLetStmt(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in LetStmt")
  let mut name = ""
  match self.input[self.curPos]{
    @lex.Token::IDENTIFIER(s) => name = s
    _ => {
      //println("Excepted an identifier in LetStmt!")
      panic()
    }
  }
  let mut ty : @types.Type = @types.Type::Var({val:None})
  self.curPos+=1
  if (self.input[self.curPos] == @lex.Token::COLON){
      self.curPos+=1
      ty = parseType(self)
      self.curPos+=1
  }
  //println("\{self.curPos} \{self.input[self.curPos]}")
  if (self.input[self.curPos] != @lex.Token::ASSIGN){
      //println("Excepted '=' in LetStmt!")
      panic()
  }
  self.curPos+=1
  let e = parseExpr(self)
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::SEMICOLON){
      //println("Excepted ';' in LetStmt!")
      panic()
  }
  //println("\{self.curPos} \{self.input[self.curPos]} before next stmt in LetStmt")
  //self.curPos+=1
  let stmt = parseStmt(self)
  return Let((name,ty),e,stmt)
}

fn Parser::parseTypeAnnotation(self : Parser) -> @types.Type{
  if (self.input[self.curPos] != @lex.Token::COLON){
      //println("\{self.curPos} \{self.input[self.curPos]} in Ta")
      //println("Excepted ':' in TypeAnnotation!")
      panic()
  }
  self.curPos+=1
  let ty = parseType(self);
  return ty
}

fn Parser::parseFnDeclStmt(self : Parser) -> @types.Syntax{
  parseNontopFnDecl(self)
}

fn Parser::parseAssignStmt(self : Parser) -> @types.Syntax{
  //println("\{self.input[self.curPos]} in AssignStmt Entry")
  let ge = parseGetOrApplyLevelExpr(self)
  //println("\{self.input[self.curPos]} in AssignStmt after ge")
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::ASSIGN){
      //println("Excepted '=' in AssignStmt!")
      panic()
  }
  self.curPos+=1
  let e = parseExpr(self)
  self.curPos+=1
  if (self.input[self.curPos] != @lex.Token::SEMICOLON){
      //println("Excepted ';' in AssignStmt!")
      panic()
  }
  //self.curPos+=1
  let stmt = parseStmt(self)
  match ge {
    Get(arr,idx) => Let(("",Unit),Put(arr,idx,e),stmt)
    _ => panic()
  }
}

fn Parser::parseExpr(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in parseExpr Entry")
  let aleL = parseAddSubLevelExpr(self)
  //println("\{self.curPos} \{self.input[self.curPos]} in parseExpr back")
  let backPoint = self.curPos
  self.curPos+=1
  match self.input[self.curPos] {
    @lex.Token::EQ => {
      self.curPos+=1
      let aleR = parseAddSubLevelExpr(self)
      Eq(aleL,aleR)
    }
    @lex.Token::LE => {
      self.curPos+=1
      let aleR = parseAddSubLevelExpr(self)
      LE(aleL,aleR)
    }
    _ => {
      self.curPos = backPoint;
      aleL
    }
  }
}

fn token2op(tok : @lex.Token) -> @types.Op{
  match tok {
    @lex.Token::ADD => @types.Op::Add
    @lex.Token::SUB => @types.Op::Sub
    @lex.Token::MUL => @types.Op::Mul
    @lex.Token::DIV => @types.Op::Div
    _ => panic()
  }
}

//因为该语法分析器采用的是递归下降，所以要消除原来的左递归语法：
// expr: // not associative
// 	add_sub_level_expr '==' add_sub_level_expr
// 	| add_sub_level_expr '<=' add_sub_level_expr
// 	| add_sub_level_expr;

// add_sub_level_expr: // left associative  <-左递归
// 	add_sub_level_expr '+' mul_div_level_expr
// 	| add_sub_level_expr '-' mul_div_level_expr
// 	| mul_div_level_expr;

// =>  修改之后：

// add_sub_level_expr: mul_div_level_expr add_sub_level_expr_tail;// left associative  
// add_sub_level_expr_tail:
//     '+' mul_div_level_expr add_sub_level_expr_tail
// 	| '-' mul_div_level_expr add_sub_level_expr_tail
// 	| ε;

// mul_div_level_expr: // left associative  <-左递归
// 	mul_div_level_expr '*' if_level_expr
// 	| mul_div_level_expr '/' if_level_expr
// 	| if_level_expr;
//  =>  修改之后：
// mul_div_level_expr: if_level_expr mul_div_level_expr_tail;// left associative  
// mul_div_level_expr_tail:
//     '*' if_level_expr mul_div_level_expr_tail
// 	| '/' if_level_expr mul_div_level_expr_tail
// 	| ε;
// if_level_expr: get_or_apply_level_expr | if_expr;
// if_expr: 'if' expr block_expr ('else' block_expr)?;

// get_or_apply_level_expr: <-左递归
// 	value_expr # value_expr_
// 	// x[y]
// 	| get_or_apply_level_expr '[' expr ']' # get_expr_
// 	// f(x, y)
// 	| get_or_apply_level_expr '(' (expr (',' expr)*)? ')' # apply_expr;
// =>  修改之后：
// get_or_apply_level_expr:
//     value_expr get_or_apply_level_expr_tail;

// get_or_apply_level_expr_tail:
//       '[' expr ']' get_or_apply_level_expr_tail
//     | '(' (expr (',' expr)*)? ')' get_or_apply_level_expr_tail
//     | ε;
fn Parser::parseAddSubLevelExpr(self : Parser) -> @types.Syntax{
  //None的具体值放在了类型推导，目前就用None
  //因为是左结合性，读同一优先级的子表达式会被合并到左边
  //println("\{self.curPos} \{self.input[self.curPos]} in parseAddSubLevelExpr Entry")
  let mut lhs = parseMulDivLevelExpr(self)
  let mut m = @types.Syntax::Unit
  let backPoint = self.curPos
  self.curPos+=1
  match self.input[self.curPos]{
    @lex.Token::ADD | @lex.Token::SUB => {
      while self.input[self.curPos] == @lex.Token::ADD ||
        self.input[self.curPos] == @lex.Token::SUB {
        let op = token2op(self.input[self.curPos])
        self.curPos+=1
        m = parseMulDivLevelExpr(self)
        lhs = @types.Syntax::Prim(lhs,m,op,kind=None)
        self.curPos+=1
      }
      self.curPos-=1 //这里要回退一个单词是因为上面的while在读到非‘+’‘-’的时候已经多读了一位
      lhs
    }
    _ => { self.curPos = backPoint; lhs} //没读到‘+’‘-’，表明是乘除一级的表达式
  }
}

fn Parser::parseMulDivLevelExpr(self : Parser) -> @types.Syntax{///none的判断同上
  //println("\{self.curPos} \{self.input[self.curPos]} in parseMulDivLevelExpr Entry")
  let mut lhs = parseIfLevelExpr(self)
  let mut ifl = @types.Syntax::Unit
  let backPoint = self.curPos
  self.curPos+=1
  match self.input[self.curPos]{
    @lex.Token::MUL | @lex.Token::DIV => {
      while self.input[self.curPos] == @lex.Token::MUL ||
        self.input[self.curPos] == @lex.Token::DIV {
        let op = token2op(self.input[self.curPos])
        self.curPos+=1
        ifl = parseIfLevelExpr(self)
        lhs = @types.Syntax::Prim(lhs,ifl,op,kind=None)
        self.curPos+=1
      }
      self.curPos-=1
      lhs
    }
    _ => { self.curPos = backPoint; lhs }
  }
}
fn Parser::parseIfLevelExpr(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in parseIfLevelExpr Entry")
    if (self.input[self.curPos] == @lex.Token::IF){
        return parseIfExpr(self)
    }
   parseGetOrApplyLevelExpr(self)
}
fn Parser::parseIfExpr(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in parseIfExpr Entry")
    self.curPos+=1
    let e = parseExpr(self)
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::LCURLYBRACKET){
      //println("Excepted '{' in IfExpr's if branch")
      panic()
    }
    let be = parseBlockExpr(self)
    //println("\{self.curPos} \{self.input[self.curPos]} in parseIfExpr if branch back")
    let backPoint = self.curPos
    self.curPos+=1
    if (self.input[self.curPos] == @lex.Token::ELSE){
        self.curPos+=1
        let be1 = parseBlockExpr(self)
        return If(e,be,be1)
    }
    else {
        self.curPos = backPoint;
        return If(e,be,Unit)
    }
}
fn Parser::parseGetOrApplyLevelExpr(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in parseGetOrApplyLevelExpr Entry")
  let mut ve = parseValueExpr(self)
  self.curPos+=1
  while self.input[self.curPos] == @lex.Token::LBRACKET ||
  self.input[self.curPos] == @lex.Token::LPAREN {
    match self.input[self.curPos] {
      @lex.Token::LBRACKET => {
        let ein = parseGetExpr(self)
        ve = @types.Syntax::Get(ve,ein)
        self.curPos+=1
      }
      @lex.Token::LPAREN => {
        let earr = parseApplyExpr(self)
        ve = @types.Syntax::App(ve,earr)
        self.curPos+=1
      }
      _ => {panic()}
    }
  }
  self.curPos-=1
  //println("\{self.curPos} \{self.input[self.curPos]} in parseGetOrApplyLevelExpr b4 ve")
  ve
}
fn Parser::parseGetExpr(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in parseGetExpr Entry")
    self.curPos+=1
    let e = parseExpr(self)
    self.curPos+=1
    //println("\{self.curPos} \{self.input[self.curPos]} in parseGetExpr after exp")
    if (self.input[self.curPos] != @lex.Token::RBRACKET){
        //println("Excepted ']' in GetExpr")
        panic()
    }
    e
}

fn Parser::parseApplyExpr(self : Parser) -> Array[@types.Syntax]{ //EmptyApplyExpr和NonemptyApplyExpr放在一起
    //println("\{self.input[self.curPos]} in parseApplyExpr Entry")
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::RPAREN){
        let arrExpr : Array[@types.Syntax] = []
        //self.curPos+=1
        arrExpr.push(parseExpr(self))
        self.curPos+=1
        while (self.input[self.curPos] == @lex.Token::COMMA){
            self.curPos+=1
            arrExpr.push(parseExpr(self))
            self.curPos+=1
        }
        if (self.input[self.curPos] != @lex.Token::RPAREN){
          //println("Excepted ')' in NonemptyApplyExpr")
          panic()
        }
        return arrExpr
    }
    []
}
// fn Parser::parseEmptyApplyExpr(self : Parser){
//     //
// }
// fn Parser::parseNonemptyApplyExpr(self : Parser){
//     //
// }
fn Parser::parseValueExpr(self : Parser) -> @types.Syntax{
    // unit_expr和tuple_type要区分开，需要多看一个Token
    //int_expr,floating_point_expr区分开，也需要多看一个token
    //block_expr和前面的fn_body是一样的
  let backPoint = self.curPos
  //println("\{backPoint} in parseValueExpr Entry")
  match self.input[self.curPos] {
    @lex.Token::LPAREN => {
      self.curPos+=1
      if (self.input[self.curPos] == @lex.Token::RPAREN){ 
          return Unit     //unit_expr
      }
      let e = parseExpr(self)
      self.curPos+=1
      if (self.input[self.curPos] == @lex.Token::RPAREN){
        return e
      }
      self.curPos = backPoint
      //self.curPos+=1
      parseTupleExpr(self)   //tuple_expr
    }
    @lex.Token::LCURLYBRACKET => parseBlockExpr(self)
    @lex.Token::TRUE => Bool(true)
    @lex.Token::FALSE => Bool(false)
    @lex.Token::SUB => parseNegExpr(self)
    @lex.Token::NOT => parseNotExpr(self)
    @lex.Token::ARRAY => parseArrayMakeExpr(self)
    @lex.Token::IDENTIFIER(s) => Var(s)
    @lex.Token::NUMBER(n1) => {
      self.curPos+=1
      if (self.input[self.curPos] == @lex.Token::DOT){
          self.curPos+=1
          match self.input[self.curPos] {
            @lex.Token::NUMBER(n2) => { 
              let d = @strconv.parse_double?(n1.to_string() + "." + n2.to_string()).unwrap()
              return Double(d) //1.1
            }
            _ => return Double(n1.to_double()) //1.
          }      
      }
      self.curPos = backPoint
      Int(n1); //1
    }
    _ => { //println("UnKnown ValueExp!"); 
    panic() }
  }
}
// fn Parser::parseUnitExpr(){
//     //
// }
fn Parser::parseTupleExpr(self : Parser) -> @types.Syntax{
    let arrExp : Array[@types.Syntax] = []
    self.curPos+=1
    //println("\{self.curPos} \{self.input[self.curPos]} in parseTupleExpr Entry")
    arrExp.push(parseExpr(self))
    self.curPos+=1
    while (self.input[self.curPos] == @lex.Token::COMMA){
        self.curPos+=1
        arrExp.push(parseExpr(self))
        self.curPos+=1
    }
    if (self.input[self.curPos] != @lex.Token::RPAREN){
        //println("Excepted ')' in TupleExpr!")
        panic()
    }
    if (arrExp.length()==1){
      //println("1-tuple is not allowed!")
      panic()
    }
    Tuple(arrExp)
}
fn Parser::parseBlockExpr(self : Parser) -> @types.Syntax{
  //println("\{self.curPos} \{self.input[self.curPos]} in parseBlockExpr Entry")
    //self.curPos+=1
    let stmt = parseStmt(self)
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::RCURLYBRACKET){
        //println("Excepted '}' in BlockExpr!");
        panic()
    }
    stmt
}

fn Parser::parseNegExpr(self : Parser) -> @types.Syntax{///check
    self.curPos+=1
    Neg(parseValueExpr(self),kind=None)
}

fn Parser::parseNotExpr(self : Parser) -> @types.Syntax{
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::LPAREN){
        //println("Excepted '(' in NotExpr!");
        panic()
    }
    self.curPos+=1
    let e = parseExpr(self);
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::RPAREN){
        //println("Excepted ')' in NotExpr!");
        panic()
    }
    Not(e)
}
fn Parser::parseArrayMakeExpr(self : Parser) -> @types.Syntax{
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::COLON){
        //println("Excepted ':' in ArrayMakeExpr!");
        panic()
    }
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::COLON){
        //println("Excepted ':' in ArrayMakeExpr!");
        panic()
    }
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::IDENTIFIER("make")){
        //println("Excepted 'make' in ArrayMakeExpr!");
        panic()
    }
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::LPAREN){
        //println("Excepted '(' in ArrayMakeExpr!");
        panic()
    }
    self.curPos+=1
    let e1 = parseExpr(self);
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::COMMA){
        //println("Excepted ',' in ArrayMakeExpr!");
        panic()
    }
    self.curPos+=1
    let e2 = parseExpr(self);
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::RPAREN){
        //println("Excepted ')' in ArrayMakeExpr!");
        panic()
    }
    Array(e1,e2)
}

fn Parser::parseType(self : Parser) -> @types.Type{
  match self.input[self.curPos] {
    @lex.Token::UNIT => @types.Type::Unit
    @lex.Token::BOOL => @types.Type::Bool
    @lex.Token::INT => @types.Type::Int
    @lex.Token::DOUBLE => @types.Type::Double
    @lex.Token::ARRAY => parseArrayType(self)
    @lex.Token::LPAREN => {
      let tupleType : Array[@types.Type] = []
      self.curPos+=1
      tupleType.push(parseType(self));
      self.curPos+=1
      while (self.input[self.curPos] == @lex.Token::COMMA){
          self.curPos+=1
          tupleType.push(parseType(self));
          self.curPos+=1
      }
      if (self.input[self.curPos] != @lex.Token::RPAREN){ 
          //println("Excepted ')' in tuple_type or function_type!")
          panic()
      }
      let backPoint = self.curPos;
      self.curPos+=1 
      if (self.input[self.curPos] != @lex.Token::ARROW){
          self.curPos = backPoint;
          return Tuple(tupleType)  //tuple_type
      }
      self.curPos+=1
      let returnType = parseType(self);
      Fun(tupleType,returnType);  //function_type
    }
    _ => { //println("Unknown type!"); 
    panic() }
  }
}
fn Parser::parseArrayType(self : Parser) -> @types.Type{
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::LBRACKET){
        //println("Excepted '[' in ArrayType!")
        panic()
    }
    self.curPos+=1
    let elemType = parseType(self);
    self.curPos+=1
    if (self.input[self.curPos] != @lex.Token::RBRACKET){
        //println("Excepted ']' in ArrayType!")
        panic()
    }
    Array(elemType);
}

// fn main{
//   let arr = []
//   let fileCont = @fs.read_to_string("ParingTest/nested_fns.mbt")
//   let lex : @lex.Lexer = {input:fileCont,readPoint:0,output:arr}
//   let prog = @types.Syntax::Unit
//   let parser : Parser = {input:lex.getAllTokens(),curPos:0,output:prog}
//   println(parser.getAst())
// }