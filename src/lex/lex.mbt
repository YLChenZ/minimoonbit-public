pub enum Token {
  TRUE
    FALSE;
    UNIT;
    BOOL;
    INT;
    DOUBLE;
    ARRAY;
    NOT;
    IF;
    ELSE;
    FN;
    LET;
    NUMBER(Int);
    IDENTIFIER(String);
    DOT;  //'.'
    ADD;
    SUB;
    MUL;
    DIV;
    ASSIGN; //'='
    EQ;//'=='
    LE;//'<='
    LPAREN;//'('
    RPAREN;//')'
    LBRACKET;//'['
    RBRACKET;//']'
    LCURLYBRACKET;//'{'
    RCURLYBRACKET;//'}'
    ARROW;//'->'
    COLON;//':'
    SEMICOLON;//';'
    COMMA;//','
    UNKNOWN
}  derive(Show,Eq)


pub struct Lexer {
  input : String;
  mut readPoint : Int;
  output : Array[Token]
}

fn isDigital(c : Char) -> Bool { //判断字符是不是数字字符
  let s : String = "0123456789"
  s.contains_char(c)
} 

fn isSymble(c : Char) -> Bool{//判断字符是不是分隔符
  let s = "()[]{}:;,"
  s.contains_char(c)
}

fn isLetter(c : Char) -> Bool{//判断字符是不是字母
  let n = c.to_int()
  (n <= 90 && n>= 65) || (n <= 122 && n>= 97) || c == '_'
}
fn isOp(c : Char) -> Bool{ //判断字符是不是操作符，注意：有的操作符不止一个字符，像'=='，'<='，'->'，需要回溯
  let s = "+-*/=<."
  s.contains_char(c) 
}

fn isSpace(c : Char) -> Bool{//判断字符是不是空白符
  c == ' ' || c == '\n' || c == '\r' || c == '\t'
}
fn skipSpace(self : Lexer) -> Unit{ //跳过空白符
  if self.readPoint >= self.input.length()-1{
    return
  }
  while isSpace(self.input[self.readPoint]){
    self.readPoint += 1
  }
  return
}

fn skipComment(self : Lexer) -> Unit{  // 和 /
  let backPoint = self.readPoint
  if (self.input[self.readPoint] == '/'){
    self.readPoint+=1
    if (self.input[self.readPoint] == '/'){
      while true {
        if (self.input[self.readPoint] == '\n' || self.input[self.readPoint] == '\r'){
          break
        }
        self.readPoint+=1
      }
      return
    }
    self.readPoint = backPoint
    return
  }
}
fn getId(self : Lexer) -> Unit{ //解析标识符，并且进一步区分出关键词
  if self.readPoint >= self.input.length(){
    return
  }
  let mut res = ""
  while isLetter(self.input[self.readPoint]) || isDigital(self.input[self.readPoint]){
    res += self.input[self.readPoint].to_string()
    self.readPoint += 1
  }
  match res {
    "true" => self.output.push(Token::TRUE)
    "false" => self.output.push(Token::FALSE)
    "Unit" => self.output.push(Token::UNIT)
    "Bool" => self.output.push(Token::BOOL)
    "Int" => self.output.push(Token::INT)
    "Double" => self.output.push(Token::DOUBLE)
    "Array" => self.output.push(Token::ARRAY)
    "not" => self.output.push(Token::NOT)
    "if" => self.output.push(Token::IF)
    "else" => self.output.push(Token::ELSE)
    "fn" => self.output.push(Token::FN)
    "let" => self.output.push(Token::LET)
    _ => self.output.push(Token::IDENTIFIER(res))
  }
}

fn getNum(self : Lexer) -> Unit{ //解析数字字符串，注意是字符串
  if self.readPoint >= self.input.length(){
    return
  }
  let mut res = ""
  while isDigital(self.input[self.readPoint]){
    res += self.input[self.readPoint].to_string()
    self.readPoint += 1
  }
  self.output.push(Token::NUMBER(@strconv.parse_int?(res).unwrap()))
}


fn getSymbol(self : Lexer) -> Unit{ //解析分隔符
  if self.readPoint >= self.input.length(){
    return
  }
  match self.input[self.readPoint]{
    '(' => self.output.push(Token::LPAREN)
    ')' => self.output.push(Token::RPAREN)
    '[' => self.output.push(Token::LBRACKET)
    ']' => self.output.push(Token::RBRACKET)
    '{' => self.output.push(Token::LCURLYBRACKET)
    '}' => self.output.push(Token::RCURLYBRACKET)
    ':' => self.output.push(Token::COLON)
    ';' => self.output.push(Token::SEMICOLON)
    ',' => self.output.push(Token::COMMA)
     _ => ()
  }
  self.readPoint += 1
}

fn getOp(self : Lexer) -> Unit { //解析操作符
  if self.readPoint >= self.input.length(){
    return
  }
  match self.input[self.readPoint]{ // - 和 ->
    '+' => self.output.push(Token::ADD)
    '-' =>  {
            if self.input[self.readPoint+1] == '>'{
              self.output.push(Token::ARROW)
              self.readPoint += 1
            }
            else  {self.output.push(Token::SUB)}
            }     
    '*' => self.output.push(Token::MUL)
    '/' => self.output.push(Token::DIV)
    '=' => {
            if self.input[self.readPoint+1] == '='{  // = 和 ==
              self.output.push(Token::EQ)
              self.readPoint += 1
            }
            else { self.output.push(Token::ASSIGN)}
            }
    '<' => {
            if self.input[self.readPoint+1] == '='{ // <=    <
              self.output.push(Token::LE)
              self.readPoint += 1
            }
            else  {self.output.push(Token::UNKNOWN)}
            }
    '.' => self.output.push(Token::DOT)  //  1.0   
    _ => ()
  }
  self.readPoint += 1
}

fn Lexer::getToken(self : Lexer) -> Unit{ //生成Token
  if self.readPoint >= self.input.length(){
    return
  }
  skipSpace(self)
  skipComment(self)
  if (isDigital(self.input[self.readPoint])){
    return getNum(self)
  }
  if (isOp(self.input[self.readPoint])){
    return getOp(self)
  }
  if (isLetter(self.input[self.readPoint])){
    return getId(self)
  }
  if (isSymble(self.input[self.readPoint])){
    return getSymbol(self)
  }
  self.readPoint += 1
  //println("Unknown character!")
}

pub fn getAllTokens(self : Lexer) -> Array[Token]{ //获得所有的Token
  while self.readPoint < self.input.length(){
    //println(self.readPoint)
    self.getToken()
  }
  self.output
}

// fn main{
//   let arr = []
//   let fileCont = @fs.read_to_string("test/test_src/ack.mbt")
//   let lex : Lexer = {input:fileCont,readPoint:0,output:arr}
//   let toks = lex.getAllTokens()
//   println(toks)
// }

