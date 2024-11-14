// fn main{
//   let arr = []
//   let fileCont = @fs.read_to_string("test/test_src/matmul-flat.mbt")
//   let lex : @lex.Lexer = {input:fileCont,readPoint:0,output:arr}
//   let tokens = lex.getAllTokens();
//   let prog = @types.Syntax::Unit
//   let parser : @parser.Parser = {input:tokens,curPos:0,output:prog}
//   let ast = parser.getAst()
//   println(ast)
//   println(typing(ast))
// }

//归一化完成typing
pub fn unify(t1 : @types.Type,t2 : @types.Type) -> Unit {  //Var(Var(None)) ,Int => None => Int 
  let t1 = t1.rep()
  let t2 = t2.rep()
  if physical_equal(t1,t2) {return}
  match (t1,t2) {
    (Int,Int) | (Unit,Unit) | (Double,Double) | (Bool,Bool) => ()
    (Var(t),ty) | (ty,Var(t)) => {
      match t.val {
        None => {
          check_self_ref(t1,ty)
          t.val = Some(ty)
        }
        Some(typ) => unify(typ,ty)
      }
    }
    //handle function tuple and array types.
    (@types.Fun(xs, x), @types.Fun(ys, y)) => {
      for i = 0;i<xs.length();i=i+1{
        unify(xs[i],ys[i])
      }
      unify(x,y)
    }
    (@types.Type::Tuple(xs), @types.Type::Tuple(ys)) => {
      for i = 0;i<xs.length();i=i+1{
        unify(xs[i],ys[i])
      }
    }
    (@types.Type::Array(x),@types.Type::Array(y)) => unify(x,y)
    _ => @util.die("Can't unify")
  }
}

fn check_self_ref(t1 : @types.Type,t2 : @types.Type) -> Unit{
  match (t1,t2) {
    (Var(ty1),Var(ty2)) => {
      if physical_equal(t1,t2) {@util.die("check_self_ref between Tvars")}
      else {check_self_ref(ty1.val.unwrap(),ty2.val.unwrap())}
    }
    (@types.Type::Array(Var(t)),Var(ty)) |  (Var(ty),@types.Type::Array(Var(t))) => {
      if physical_equal(t,ty) {@util.die("check_self_ref between Tvar and Array[TVar]")} 
      else { check_self_ref(t.val.unwrap(),ty.val.unwrap()) }
    }
    (@types.Type::Fun(xs,x),Var(ty)) |  (Var(ty),@types.Type::Fun(xs,x)) => {
      for i in xs{
        match i {
          Var(t) => if physical_equal(t,ty) {
            @util.die("check_self_ref between Tvar and Fun[TVar]")
          }
          else {check_self_ref(ty.val.unwrap(),t.val.unwrap())}
          _ => ()
        }
      }
      match x {
          Var(t) => if physical_equal(t,ty) {
            @util.die("check_self_ref between Tvar and Fun[TVar]")
          }
          else {check_self_ref(ty.val.unwrap(),t.val.unwrap())}
          _ => ()
        }
    }
    (@types.Type::Tuple(xs),Var(ty)) |  (Var(ty),@types.Type::Tuple(xs)) => {
      for i in xs{
        match i {
          Var(t) => if physical_equal(t,ty) {
            @util.die("check_self_ref between Tvar and Fun[TVar]")
          }
          else {check_self_ref(ty.val.unwrap(),i)}
          _ => ()
        }
      }
    }
    _ => ()
  }
}

//infer
pub let extenv : Map[String,@types.Type] = {
  "read_int" : Fun([],Unit),
  "print_int" : Fun([Int],Unit),
  "read_char" : Fun([],Int),
  "print_char" : Fun([Int],Unit),
  "print_endline" : Fun([],Unit),
  "int_of_float" : Fun([Double],Int),
  "float_of_int" : Fun([Int],Double),
  "truncate" : Fun([Double],Int),
  "floor" : Fun([Double],Double),
  "abs_float" : Fun([Double],Double),
  "sqrt" : Fun([Double],Double),
  "sin" : Fun([Double],Double),
  "cos" : Fun([Double],Double),
  "atan" : Fun([Double],Double),
}

pub type LocalCtx @immut/hashmap.T[String,@types.Type]

pub fn infer(ctx : LocalCtx,e : @types.Syntax) -> @types.Type{
  match e {
    Int(_) => Int
    Bool(_) => Bool
    Double(_) => Double
    Unit => Unit
    Var(s) => match ctx._[s] {
      Some(t) => t
      None => match extenv[s] {
        Some(t) => t
        None => { 
          let ty :@types.Type = Var({val:None})
          extenv[s] = ty
          ty
        }
      }
    }
    Tuple(arrSyn) => Tuple(arrSyn.map(fn (syn){infer(ctx,syn)}))
    Neg(syn,..) as neg => {
      //println("Enter Neg")
      let ty = infer(ctx,syn)
      match ty {
        Int | Double => {neg.kind = Some(@types.type2kind(ty));ty}
        _ => @util.die("The operand of Neg is not a int or double value")
      }
    }
    Not(syn) => {
      //println("Enter Not")
      unify(Bool,infer(ctx,syn)) //Var(Some(Bool)) 
      Bool
    }
    Array(n,syn) => {
      //println("Enter Array")
      unify(infer(ctx,n),Int)
      Array(infer(ctx,syn))
    }
    Prim(lhs,rhs,_,..) as p => {
      //println("Enter Prim")
      //println(ctx._)
      //println((lhs,rhs))
      let l = infer(ctx,lhs)
      let r = infer(ctx,rhs)
      //println("lhs : \{l}, rhs : \{r}")
      //unify(l,r)
      //println("lhs : \{l}, rhs : \{r}")
      match (l,r){  //x + 1 => Type(x) = Int   //x+y  => Int + Int
        (Int,Int) | (Double,Double) => {p.kind= Some(@types.type2kind(l));l}
        (Var(t),Int) | (Var(t),Double) => {t.val = Some(r); p.kind= Some(@types.type2kind(r));r}
        (Int,Var(t)) | (Double,Var(t)) => {t.val = Some(l); p.kind= Some(@types.type2kind(l));l}
        (Var(lt),Var(rt)) => match (lt.val,rt.val) {
          (None,None) => {p.kind= Some(@types.type2kind(Int));Int}
          (None,Some(t)) | (Some(t),None) => {unify(l,r);p.kind= Some(@types.type2kind(t));t}
          (Some(t1),Some(t2)) => {unify(t1,t2);p.kind= Some(@types.type2kind(t1));t1}
        }
        _ => @util.die("The lhs and rhs of Prim is not same (int or double)")
      }
    }
    
    Eq(lhs,rhs) | LE(lhs,rhs)=> {
      //println("Enter Eq or Le")
      let l = infer(ctx,lhs)
      let r = infer(ctx,rhs)
      unify(l,r)
      Bool
    }
    Get(arr,n) => {
      //println("Enter Get")
      let t_arr = infer(ctx,arr)
      let t_n = infer(ctx,n)
      let t = @types.Type::Var({val:None})
      unify(Array(t),t_arr)
      unify(Int,t_n)
      ////println(t)
      t
    }
    App(f,args) => {
      //println("Enter App")
      let ret_ty = @types.Type::Var({val:None})
      let f_ty = infer(ctx,f)
      //println(f_ty)
      let args_ty = []
      for a in args{
        args_ty.push(infer(ctx,a))
      }
      //println(args_ty)
      unify(f_ty, Fun(args_ty,ret_ty))
      ret_ty.rep()
    }
    If(c,b1,b2) => {
      //println("Enter If")
      unify(infer(ctx,c),Bool)
      let t_b1 = infer(ctx,b1)
      let t_b2 = infer(ctx,b2)
      unify(t_b1,t_b2)
      t_b1
    }
    Put(arr,idx,syn) => {  //注意第一个是get; get = s1;s2,这个不对，已将赋值表达式转化成let表达式 _[_] = _ 
    // => let _ : Unit = ..;stmt
      //println("Enter Put")
      let t_arr = infer(ctx,arr)
      let t_idx = infer(ctx,idx)
      let t_syn = infer(ctx,syn)
      unify(t_arr,Array(t_syn))
      unify(t_idx,Int)
      //println("here in put get unify succeed")
      Unit
    }
    Let((v,ty),e1,s1) => {  //let x : Int = 1;s1
      //println("Enter Let")
      let t_e1 = infer(ctx,e1)
      unify(t_e1,ty)
      //println((t_e1,ty))
      let newctx = ctx._.add(v,t_e1)
      infer(newctx,s1)
    }
    LetTuple(arr,s1,s2) => { 
      //println("Enter LetTuple")
      let t_tuple = @types.Type::Tuple(arr.map(fn{t=>t.1}))
      let t_s1 = infer(ctx,s1)
      unify(t_tuple,t_s1)
      let mut new_ctx = ctx
      for i in arr{
        new_ctx = ctx._.add(i.0,i.1)
      }
      infer(new_ctx,s2)
    }
    LetRec({name:(f,t),args,body},rest) => {  //fn adder(x,y) {x+y};stmt
      //println("Enter LetRec")
      let env_f = ctx._.add(f,t)
      //println(env_f)
      let args_ty = args.map(fn {(_,t)=>t})
      let mut env_args = env_f
      for arg in args{
        env_args = env_args.add(arg.0,arg.1)
      }
      let body_ty = infer(env_args,body)
      unify(t,Fun(args_ty,body_ty))
      infer(env_f,rest)
    }
  }
}

fn deref_type(t : @types.Type) -> @types.Type {
  match t {
    Fun(params,ret) => Fun(params.map(fn{t=>deref_type(t)}),deref_type(ret))
    Tuple(arrTy) => Tuple(arrTy.map(fn{t=>deref_type(t)}))
    Array(t) => Array(deref_type(t))
    Var(t) => match t.val {
      Some(ty) => {
        let typ = deref_type(ty)
        t.val = Some(typ)
        typ 
      }
      None => {
        t.val = Some(Unit)
        Unit
      } 
    }
    ty => ty
  }
}

fn deref_syntax(syntax:@types.Syntax) -> @types.Syntax{
  match syntax {
    Tuple(arr_syn) => Tuple(arr_syn.map(fn{t=>deref_syntax(t)}))
    Not(syn) => Not(deref_syntax(syn))
    Array(s1,s2) => Array(deref_syntax(s1),deref_syntax(s2))
    Neg(s,~kind) => Neg(deref_syntax(s),~kind)
    App(s,arr_s) => App(deref_syntax(s),arr_s.map(fn{t=>deref_syntax(t)}))
    Get(s1,s2) => Get(deref_syntax(s1),deref_syntax(s2))
    If(e,s1,s2) => If(deref_syntax(e),deref_syntax(s1),deref_syntax(s2))
    Prim(l,h,op,~kind) => Prim(deref_syntax(l),deref_syntax(h),op,~kind)
    Eq(l,h) => Eq(deref_syntax(l),deref_syntax(h))
    LE(l,h) => LE(deref_syntax(l),deref_syntax(h))
    Let((str,ty),s1,s2) => Let((str,deref_type(ty)),deref_syntax(s1),deref_syntax(s2))
    LetRec({name:(str,ty),args,body},s) => LetRec({name:(str,deref_type(ty)),args:args.map(fn{(s,t)=>(s,deref_type(t))}),body:deref_syntax(body)},deref_syntax(s))
    LetTuple(arr,s1,s2) => LetTuple(arr.map(fn{(s,t)=>(s,deref_type(t))}),deref_syntax(s1),deref_syntax(s2))
    Put(s1,s2,s3) => Put(deref_syntax(s1),deref_syntax(s2),deref_syntax(s3))
    _ => syntax
  }
}

pub fn typing(e : @types.Syntax) -> @types.Syntax {
  unify(Unit, infer(@immut/hashmap.new(),e))
  for ext_f,ext_t in extenv {
    extenv[ext_f] = deref_type(ext_t)
  }
  deref_syntax(e)
}

