pub typealias LocalEnv = @immut/hashmap.T[Name, LowType]

//将Type转换成Lowtype
fn type_lowType(t : Type,fv : Array[Name]) -> LowType{ 
  match t {
    Unit => Unit
    Int => Int
    Bool => Bool
    Double => Double
    Fun(argt,rett) => match fv {
      [] => DirectFn(argt.map(fn {ty=>type_lowType(ty,fv)}),type_lowType(rett,fv))
      _ => ClosureFn(argt.map(fn {ty=>type_lowType(ty,fv)}),type_lowType(rett,fv))
    }
    Tuple(arrT) => Tuple(arrT.map(fn {ty=>type_lowType(ty,fv)}))
    Array(ty) => Array(type_lowType(ty,fv))
    Ptr => Ptr
    Var(_) => panic()
  }
}

//计算Expr中的自由变量
pub fn free_vars(e:Expr) -> @immut/sorted_set.T[Name]{
  match e {
    Unit | Int(_) | Double(_) | ExternalArray(_)=> @immut/sorted_set.new()
    Neg(n) | FNeg(n) | Var(n) => @immut/sorted_set.singleton(n)
    Add(l,r) | Sub(l,r) | Mul(l,r) | Div(l,r) | FAdd(l,r) |
     FSub(l,r) | FMul(l,r) | FDiv(l,r) | ArrayGet(l,r)=> @immut/sorted_set.of([l,r])
    IfEq(n1,n2,e1,e2) | IfLe(n1,n2,e1,e2)=> {
      let fv_e1 = free_vars(e1)
      let fv_e2 = free_vars(e2)
      fv_e1.union(fv_e2).union(@immut/sorted_set.of([n1,n2]))
    }
    Let((n,_),e1,e2) => {
      let fv_e1 = free_vars(e1)
      let fv_e2 = free_vars(e2)
      fv_e1.union(fv_e2.remove(n))
    }
    MakeClosure((n, _), {name,actual_free_vars}, e) => {
      let fv_e = free_vars(e)
      fv_e.union(@immut/sorted_set.from_array(actual_free_vars)).remove(n)
    }
    CallClosure(n, arrN) => {@immut/sorted_set.from_array(arrN).add(n)}
    CallDirect(_, arrN) | MakeTuple(arrN)=> @immut/sorted_set.from_array(arrN)
    LetTuple(arrN2lt, n, e) => {  //let (x,y,z) : (Int,..) = (1,2,3) ; e
      let fv_e = free_vars(e)
      let arrN = arrN2lt.map(fn {t => t.0})
      fv_e.diff(@immut/sorted_set.from_array(arrN)).add(n)
    }
    ArrayPut(n1, n2, n3) => @immut/sorted_set.of([n1,n2,n3])  //_[_] = _
  }
}

let toplevel_funs : Ref[Array[FuncDef]] = {val:[]} //用来保存Program结构体中的所有函数，即fundefs的内容

//注意：给类型为Map的变量赋值一个Map之后，在变量上的改动会影响到原Map
fn knf2expr(knf : @knf.Knf,
  env : Map[String, Type],
  no_free_var_funs : Array[Name]
  ) -> Expr{
  match knf {
    Unit => Unit
    Int(i) => Int(i)
    Double(d) => Double(d)
    Neg(n) => Neg(n)
    Add(l,r) => Add(l,r)
    Sub(l,r) => Sub(l,r)
    Mul(l,r) => Mul(l,r)
    Div(l,r) => Div(l,r)
    FNeg(f) => FNeg(f)
    FAdd(l,r) => FAdd(l,r)
    FSub(l,r) => FSub(l,r)
    FMul(l,r) => FMul(l,r)
    FDiv(l,r) => FDiv(l,r)
    IfEq(n1,n2,k1,k2) => 
      IfEq(n1,n2,knf2expr(k1,env,no_free_var_funs),knf2expr(k2,env,no_free_var_funs))
    IfLe(n1,n2,k1,k2) => 
      IfLe(n1,n2,knf2expr(k1,env,no_free_var_funs),knf2expr(k2,env,no_free_var_funs))
    Let((n,t),k1,k2) => {
      //println("Enter Let")
      let old_env = env
      env.set(n.to_string(),t)
      let e1 = knf2expr(k1,old_env,no_free_var_funs)
      let e2 = knf2expr(k2,env,no_free_var_funs)
      Let((n,type_lowType(t,free_vars(e1).to_array())),e1,e2)
    }
    Var(n) => Var(n)
    LetRec({name,ty,args,body},k) => {  
      //println("Enter LetRec")
      let funs_back_point = toplevel_funs
      //println(env.size())
      env.set(name.to_string(),ty)
      for arg in args {
        env.set(arg.0.to_string(),arg.1)
      }
      //println("here1")
      let mut new_nfvf = no_free_var_funs.copy()
      new_nfvf.push(name)
      let mut body_expr = knf2expr(body,env,new_nfvf)
      let argN = args.map(fn {t => t.0})
      let fv = free_vars(body_expr).diff(@immut/sorted_set.from_array(argN)).to_array()
      //println("here2")
      if fv != [] {
        toplevel_funs.val = funs_back_point.val
        body_expr = knf2expr(body,env,no_free_var_funs)
        new_nfvf = no_free_var_funs
      }
      //println("here3")
      let new_fv = free_vars(body_expr).diff(@immut/sorted_set.from_array(argN).add(name)).to_array()
      let fv_ty = new_fv.map(fn{t=>(t,type_lowType(env[t.to_string()].unwrap(),new_fv))})
      let push_fun = {
        name:name.to_string(),
        old_name:name,
        is_closure: not(new_fv.is_empty()),
        ty:type_lowType(ty,new_fv),
        args : args.map(fn {t=>(t.0,type_lowType(t.1,new_fv))}),
        formal_free_vars : fv_ty,
        body : body_expr
      }
      toplevel_funs.val.push(push_fun)
      let k_exp = knf2expr(k,env,new_nfvf)
      //println("here4")
      //println(free_vars(k_exp))
      if free_vars(k_exp).contains(name) {
        MakeClosure((name, type_lowType(ty,new_fv)), {name:name.to_string(),actual_free_vars:new_fv}, k_exp)
      }
      else {k_exp}
    }
    Apply(f,arrN) => if no_free_var_funs.contains(f) {
      CallDirect(f.to_string(), arrN)
    } else { CallClosure(f,arrN) }
    Tuple(arrN) => MakeTuple(arrN)
    LetTuple(arrN2T,n,k) => {
      let env_arr = env.to_array()
      env_arr.append(arrN2T.map(fn {t=>(t.0.to_string(),t.1)}))
      let new_env = Map::from_array(env_arr)
      LetTuple(arrN2T.map(fn {t=>(t.0,type_lowType(t.1,[]))}),n,knf2expr(k,new_env,no_free_var_funs))
    }
    Get(n1,n2) => ArrayGet(n1,n2)
    Put(n1,n2,n3) => ArrayPut(n1,n2,n3)
    ExternalArray(n) => ExternalArray(n.to_string())
    ExternalFunctionApplication(s,arrN) => CallDirect(s,arrN)
  }
}

//最后带闭包的IR，是由多个函数以及一个Expr组成，Expr的值，即为函数所返回的值
pub fn knf_program_to_closure(
  prog : @knf.Knf,
  extern_env : Map[String, Type]
) -> Program {
  toplevel_funs.val = []
  let e = knf2expr(prog,extern_env,[])
  {fundefs:toplevel_funs.val,body:e}
}

