/// Preprocesses the syntax tree, extracting the contents of functions `main` and `init` to top-level.
/// 把main或者init的内容提到外面
pub fn KnfEnv::syntax_preprocess(
  self : KnfEnv,
  s : @types.Syntax
) -> @types.Syntax {
  match s {
    LetRec(fundef,rest) => match fundef.name.0 {
        "main" | "init" => fundef.body
        _ => LetRec(fundef,syntax_preprocess(self,rest))
    }
    Let((str,ty),s1,s2) => Let((str,ty),s1,syntax_preprocess(self,s2))
    _ => panic()
  }
}

// fn main{
//   let arr = []
//   let fileCont = @fs.read_to_string("test/test_src/adder.mbt")
//   let lex : @lex.Lexer = {input:fileCont,readPoint:0,output:arr}
//   let tokens = lex.getAllTokens();
//   let prog = @types.Syntax::Unit
//   let parser : @parser.Parser = {input:tokens,curPos:0,output:prog}
//   let ast = parser.getAst()
//   println(ast)
//   let typing_ast = @typing.typing(ast)
//   println(typing_ast)
//   let preS = syntax_preprocess(new(@immut/hashmap.new()),typing_ast)
//   println(typing_ast)
//   println(preS)
//   let knf = to_knf(new(@immut/hashmap.new()),preS)
//   println(typing_ast)
//   println(knf)
// }
