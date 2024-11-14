let ext_fun = ["read_int","print_int","read_char","print_char","print_endline","int_of_float","float_of_int","truncate",
"floor","abs_float","sqrt","sin","cos","atan"]


fn op_to_js(op : @types.Op) -> String{
  match op {
    Add => "+"
    Sub => "-"
    Mul => "*"
    Div => "/"
  }
}

fn arr_to_js(arr : Array[String]) -> String{
  let mut s = ""
  for j=0;j<arr.length();j=j+1 {
    if j == arr.length() - 1 {
      s = s + arr[j]
    }
    else {
      s = s + arr[j]+ ","
    }
  }
  s
}
fn fundef_to_js(fun : @types.Fundef) -> String {
  let flag = is_recursive(fun)
  let argName = fun.args.map(fn {e=>e.0})
  let mut first_part = ""
  let fun_body = funbody_to_js(fun.body)

  match fun.name.0{
    "main" | "init" => {
      first_part = "export default function " + fun.name.0
    }
    _ => {
      first_part = "function " + fun.name.0
    }
  }
  if flag {
    let new_name = fun.name.0+"0"
    first_part = "const " + new_name + "="
    let tr_opt = "const trampoline = f => (...args) => {\n let result = f(...args);\n while (typeof result === 'function') {\nresult = result();\n}\nreturn result;\n}\n"+
                        "const \{fun.name.0} = trampoline(\{new_name});\n"
    first_part + "(" + arr_to_js(argName) +")" + " => "+"{\n" + fun_body.replace_all(old=fun.name.0,new=new_name).replace_all(old="return \{new_name}",new= "return () => \{new_name}") + "\n}\n" + tr_opt
  } else {
    first_part + "(" + arr_to_js(argName) +")" + "{\n" + fun_body + "\n}\n"
  }
}

fn funbody_to_js(body : @types.Syntax) -> String{
  match body{
    Let((name,_),v,b) => {
      let mut name_js = ""
      let v_js = to_js(v,false)
      let b_js = funbody_to_js(b)
      if name == "_" {
        name_js = "_" + counter.val.to_string()
        counter.val+=1
      }
      else {name_js = name}
      if name == ""{
        v_js + "\n" + b_js
      }
      else {
        "let " + name_js + " = " + v_js + "\n" + b_js
      }
    }
    If(cond,b1,b2) => {
      let part1 = "if "+ "(" + to_js(cond,false) + ")" + "{\n" + funbody_to_js(b1) + "\n}\n"
      match b2 {
        Unit => part1
        _ => part1 + "else " + "{\n" + funbody_to_js(b2) + "\n}\n" 
      }
    }
    LetTuple(arrn2t,s1,s2) => {
      let t = arr_to_js(arrn2t.map(fn {
          e=>match e.0 {
            "_" => {let res = "_" + counter.val.to_string();counter.val +=1;res}
            _ => e.0
          }
          })) 
      "let " + "[" + t + "]" + " = " +  to_js(s1,false) + "\n" + funbody_to_js(s2)
    }
    LetRec(fundef,rest) => {
      let fundef_js = fundef_to_js(fundef)
      let rest_js = funbody_to_js(rest)
      fundef_js + rest_js
    }
    _ => "return " + to_js(body,true)
  }
}

let counter : Ref[Int] = {val:1}
pub fn to_js(ast : @types.Syntax, is_last : Bool) -> String {
  match ast {
    Unit => ""
    Bool(b) => b.to_string()
    Int(i) => i.to_string()
    Double(d) => d.to_string()
    Var(s) => s
    Tuple(arr) => {
      "[" + arr_to_js(arr.map(fn {e => to_js(e,false)})) + "]"
    } 
    Not(s) => "!" + "(" + to_js(s,false) + ")"
    Array(s1,s2) => {
      let e = to_js(s2,false)
      "Array("+ to_js(s1,false) + ")" + ".fill("+ e +")"
    }
    Neg(s,..) => "-" + "(" + to_js(s,false) + ")"
    App(f,arg) => {
      let mut fun_name = to_js(f,false)
      if ext_fun.contains(fun_name){
        fun_name = "minimbt_"+fun_name
      }
      fun_name + "(" + arr_to_js(arg.map(fn {
        e => match e {
          If(cond,b1,b2) => "("+ to_js(cond,false) + "?" + to_js(b1,false) + ":" + to_js(b2,false) +")"
          _ => to_js(e,false)
        }
        })) + ")"
    }
    Get(name,idx) => {
      to_js(name,false) +"[" + to_js(idx,false) + "]"
    }
    If(cond,b1,b2) => {
      let part1 = "if "+ "(" + to_js(cond,false) + ")" + "{\n" + to_js(b1,false) + "\n}\n"
      match b2 {
        Unit => part1
        _ => part1 + "else " + "{\n" + to_js(b2,false) + "\n}\n" 
      }
    } 
    Prim(l,r,op,..) =>  {
      match (l,r) {
        (If(cond1,b1,b2),If(cond2,b3,b4)) => {
          "("+ to_js(cond1,false) + "?" + to_js(b1,false) + ":" + to_js(b2,false) +")" + op_to_js(op) +
          "("+ to_js(cond2,false) + "?" + to_js(b3,false) + ":" + to_js(b4,false) +")"
        }
        (If(cond1,b1,b2),_) => {
          "("+ to_js(cond1,false) + "?" + to_js(b1,false) + ":" + to_js(b2,false) +")" + op_to_js(op) +
          to_js(r,false)
        }
        (_,If(cond2,b3,b4)) => {
          to_js(l,false) + op_to_js(op) +
          "("+ to_js(cond2,false) + "?" + to_js(b3,false) + ":" + to_js(b4,false) +")"
        }
        (_,_) => "("+ to_js(l,false) + op_to_js(op) + to_js(r,false) +")"
      }
    }
    Eq(l,r) => to_js(l,false) + "==" + to_js(r,false)
    LE(l,r) => to_js(l,false) + "<=" + to_js(r,false)
    Let((str,_),s1,s2) => {
      let mut name = ""
      if str == "_"{
        name = "_" + counter.val.to_string()
        counter.val+=1
      }
      else {name = str}
      if str == "" {
        to_js(s1,false) + "\n" + to_js(s2,false)
      }
      else {
        "let " + name + " = " + to_js(s1,false) + "\n" + to_js(s2,false)
      }
    }
    LetRec(fundef,s) => {
      let fundef_part = fundef_to_js(fundef)
      let rest_part = to_js(s,false)
      
          fundef_part+rest_part
    }
    LetTuple(arrn2t,s1,s2) => {
      let t = arr_to_js(arrn2t.map(fn {
          e=>match e.0 {
            "_" => {"_" + counter.val.to_string()}
            _ => e.0
          }
          })) 
      counter.val +=1
      "let " + "[" + t + "]" + " = " +  to_js(s1,false) + "\n" + to_js(s2,false)
    }
    Put(s1,s2,s3) => {
      to_js(s1,false) + "[" + to_js(s2,false) + "]" +"="+ to_js(s3,false) + ";"
    }
  }
}

fn is_recursive(fun : @types.Fundef) -> Bool{
  let rec_name = fun.name.0
  match fun.body{
    App(_,_) => app_rec_name(fun.body,rec_name)
    Let(_,s1,s2) => app_rec_name(s1,rec_name) || app_rec_name(s2,rec_name)
    If(cond,b1,b2) => app_rec_name(cond,rec_name) || app_rec_name(b1,rec_name) || app_rec_name(b2,rec_name)
    _ => false
  }
}

fn app_rec_name(ast : @types.Syntax, name : String) -> Bool {
  match ast{
    App(Var(s),args) => name == s || args.map(fn {e => app_rec_name(e,name)}).contains(true)
    _ => false
  }
}

// fn main{
//   let arr = []
//   let fileCont = @fs.read_to_string("./test/test_src/adder.mbt")
//   let lex : @lex.Lexer = {input:fileCont,readPoint:0,output:arr}
//   let tokens = lex.getAllTokens();
//   let prog = @types.Syntax::Unit
//   let parser : @parser.Parser = {input:tokens,curPos:0,output:prog}
//   let ast = parser.getAst()
//   println(ast)
//   let typing_ast = @typing.typing(ast)
//   println(typing_ast)
//   let js = to_js(typing_ast)
//   println(js)
//   @fs.write_to_string("./src/js/adder.mjs",js)
// }