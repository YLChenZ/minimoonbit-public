enum IdOrImm {
  V(String)
  C(Int)
}derive (Show)

enum Instr {
  Ans(Exp)
  Let((String,@closure.LowType),Exp,Instr)
}derive (Show)

enum Exp {
  Nop
  Li(Int)
  La(String)
  Mov(String)
  Neg(String)
  Add(String,IdOrImm)
  Sub(String,IdOrImm)
  Mul(String,IdOrImm)
  Div(String,IdOrImm)
  Sll(String,IdOrImm)
  Srl(String,IdOrImm)
  Sra(String,IdOrImm)
  Ld(String,IdOrImm)
  St(String,String,IdOrImm)
  FMovD(String)
  FNegD(String)
  FAddD(String,String)
  FSubD(String,String)
  FMulD(String,String)
  FDivD(String,String)
  LdDF(String,IdOrImm)
  StDF(String,String,IdOrImm)
  Comment(String)

  IfEq(String,IdOrImm,Instr,Instr)
  IfLe(String,IdOrImm,Instr,Instr)
  IfGe(String,IdOrImm,Instr,Instr)
  IfFEq(String,String,Instr,Instr)
  IfFLe(String,String,Instr,Instr)
  
  CallCls(String,Array[String],Array[String])
  CallDir(String,Array[String],Array[String])
  Save(String,String)
  Restore(String)
}derive (Show)

struct Fundef {
  name : String
  args : Array[String]
  fargs : Array[String]
  body : Instr
  ret : @closure.LowType
}derive (Show)

struct Prog {
  ftable : Array[(String,Double)]
  funlist : Array[Fundef]
  body : Instr
}derive (Show)

let counter : Ref[Int] = {val:0}
fn gen_tmp() -> String{
  let val = counter.val
  counter.val+=1
  "tmp\{val}"
}

fn gen_id(s : String) -> String{
  let val = counter.val
  counter.val+=1
  "\{s}\{val}"
}
fn fletd(x : String,e : Exp,i : Instr) -> Instr{
  Let((x,Double),e,i)
}

fn seq(e : Exp,i : Instr) -> Instr{
  Let((gen_tmp(),Unit),e,i)
}

pub let allregs = ["zero", "ra", "sp",  "gp", "tp", "t0", "t1", "t2", "s0", 
    "s1", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "s2", "s3", "s4", 
    "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]

pub let all_tmp_regs : Array[String] = reg_temp_list.map(Reg::to_string)
pub let all_arg_regs : Array[String] = reg_arg_list.map(Reg::to_string)
pub let all_saved_regs : Array[String] = reg_saved_list.map(Reg::to_string)
pub let all_caller_saved_regs : Array[String] = all_arg_regs + all_tmp_regs
pub let all_callee_saved_regs : Array[String] = all_saved_regs
pub let all_allocatable_regs : Array[String] = all_caller_saved_regs +
  all_callee_saved_regs + ["s11"]
pub let allfregs = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
    "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
    "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
    "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
pub let all_tmp_fregs : Array[String] = freg_temp_list.map(FReg::to_string)
pub let all_arg_fregs : Array[String] = freg_arg_list.map(FReg::to_string)
pub let all_saved_fregs : Array[String] = freg_saved_list.map(FReg::to_string)
pub let all_caller_saved_fregs: Array[String] = all_arg_fregs + all_tmp_fregs
pub let all_callee_saved_fregs : Array[String] = all_saved_fregs
pub let all_allocatable_fregs : Array[String] = all_caller_saved_fregs +
  all_callee_saved_fregs
pub let all_allocatable_fregs_for_double : Array[String] = ["fa0", "fa2", "fa4",
    "fa6","ft0", "ft2", "ft4", "ft6","ft8", "ft10",
    "fs0",  "fs2", "fs4", "fs6",
    "fs8", "fs10"]

pub let co_freg_table : @immut/hashmap.T[String,String] = {let mut map = @immut/hashmap.new()
  for i = 0,j=1;i<allfregs.length();i=i+2,j=j+2 {
    map = map.add(allfregs[i],allfregs[j])
  }
  map
}

pub fn co_freg(freg : String) -> String {
  co_freg_table[freg].unwrap()
}
let regsp = "sp"
let regra = "ra"
let regfp = "fp"
let reghp = "hp"
let reggp = "gp"
let regcl = "s11"
let regrt = "a0"
let regswp = "t6"
let fregrt = "fa0"
let fregswp = "ft11"
fn is_reg(r : String) -> Bool {
  allfregs.contains(r) || allregs.contains(r) || r == "hp"
}



fn remove_and_uniq(xs : @immut/sorted_set.T[String],zs : Array[String]) -> Array[String] {
  match zs {
    [] => []
    [x,..] => {
      let t = zs.copy()
      let _ = t.remove(0)
      if xs.contains(x) {
        remove_and_uniq(xs,t)
      }
      else {
        [x] + remove_and_uniq(xs.add(x),t)
      }
    }
  }
}

fn fv_id_or_imm(iom : IdOrImm) -> Array[String] {
  match iom {
    V(s) => [s]
    _ =>[]
  }
}
fn fv_ins(instr : Instr) -> Array[String]{
  match instr{
    Ans(exp) => fv_exp(exp)
    Let((x,_),e,i) => fv_exp(e)+remove_and_uniq(@immut/sorted_set.singleton(x),fv_ins(i))
  }
}

fn fv_instr(instr : Instr) -> Array[String] {
  remove_and_uniq(@immut/sorted_set.new(),fv_ins(instr))
}
fn fv_exp(exp : Exp) -> Array[String]{
  match exp {
    Nop | Li(_) | La(_) | Comment(_) | Restore(_) => []
    Mov(x) | Neg(x) | FMovD(x) | FNegD(x) | Save(x,_) => [x]
    Add(x,y) | Sub(x,y) | Mul(x,y) | Div(x,y) | Sll(x,y) | Srl(x,y) | 
    Sra(x,y) | Ld(x,y) | LdDF(x,y) => [x] + fv_id_or_imm(y)
    St(x,y,z) | StDF(x,y,z) => [x,y]+fv_id_or_imm(z)
    FAddD(x,y) | FSubD(x,y) | FMulD(x,y) | FDivD(x,y) => [x,y]
    IfEq(x,y,i1,i2) | IfLe(x,y,i1,i2) | IfGe(x,y,i1,i2) => 
      [x] + fv_id_or_imm(y)+ remove_and_uniq(@immut/sorted_set.new(),fv_ins(i1)+fv_ins(i2))
    IfFEq(x,y,i1,i2) | IfFLe(x,y,i1,i2) => 
      [x,y] + remove_and_uniq(@immut/sorted_set.new(),fv_ins(i1)+fv_ins(i2))
    CallCls(x,ys,zs) => [x] + ys + zs
    CallDir(_,ys,zs) => ys + zs
  }
}

fn concat(i1 : Instr,xt : (String,@closure.LowType),i2 : Instr) -> Instr {
  match i1 {
    Ans(exp) => Let(xt,exp,i2)
    Let(yt,exp,i) => Let(yt,exp,concat(i,xt,i2))
  }
}

fn align(i : Int) -> Int{
  if i%8 == 0{
    i
  }
  else {i+4}
}

let data : Ref[Array[(String,Double)]]= {val:[]}

fn classify[T](
  xts : Array[(String,@closure.LowType)],
  init : T,
  addf : (T,String) -> T,
  addi : (T,String,@closure.LowType) -> T
  ) -> T {
    Array::fold_left(xts,~init=init, fn (acc,e){
      match e.1 {
        Unit => acc
        Double => addf(acc,e.0)
        _ => addi(acc,e.0,e.1)
      }
    })
  }

fn separate(xts : Array[(String,@closure.LowType)]) -> (Array[String],Array[String]) {
  classify(xts,([],[]),fn {(i,d),x => {(i,d+[x])}},fn {(i,d),x,_ => {(i+[x],d)}})
}

fn expand[T](
  xts : Array[(String,@closure.LowType)],
  init : (Int,T),
  addf : (String,Int,T) -> T,
  addi : (String,@closure.LowType,Int,T) -> T
  ) -> (Int,T) {
    classify(xts,init,
    fn {(offset,acc),x => {
      let offset = align(offset)
      (offset+8,addf(x,offset,acc))
    }},
    fn {(offset,acc),x,t => {
      (offset+4,addi(x,t,offset,acc))
    }})
  }

pub fn closure_ir_to_instr(
  env : @immut/hashmap.T[String,@closure.LowType],
  expr: @closure.Expr
  ) -> Instr{
    match expr{
      Unit => Ans(Nop)
      Int(i) => Ans(Li(i))
      Double(d) => {
        let mut label = ""
        let l = data.val.search_by(fn{e => e.1 == d})
        match l {
          Some(la) => {
            label = data.val[la].0
          }
          None => {
            let la = gen_id("l")
            data.val = [(la,d)]+ data.val
            label = la
          }
        }
        let x = gen_id("l")
        Let((x,Int),La(label),Ans(LdDF(x,C(0))))
      }
      Neg(n) => Ans(Neg(n.to_string()))
      Add(x,y) => Ans(Add(x.to_string(),V(y.to_string())))
      Sub(x,y) => Ans(Sub(x.to_string(),V(y.to_string())))
      Mul(x,y) => Ans(Mul(x.to_string(),V(y.to_string())))
      Div(x,y) => Ans(Div(x.to_string(),V(y.to_string())))
      FNeg(n) => Ans(FNegD(n.to_string()))
      FAdd(x,y) => Ans(FAddD(x.to_string(),y.to_string()))
      FSub(x,y) => Ans(FSubD(x.to_string(),y.to_string()))
      FMul(x,y) => Ans(FMulD(x.to_string(),y.to_string()))
      FDiv(x,y) => Ans(FDivD(x.to_string(),y.to_string()))
      IfEq(x,y,e1,e2) => {
        //println("Enter IfEq")
        match env[x.to_string()].unwrap() {
          Bool | Int => Ans(IfEq(x.to_string(),V(y.to_string()),closure_ir_to_instr(env,e1),closure_ir_to_instr(env,e2)))
          Double => Ans(IfFEq(x.to_string(),y.to_string(),closure_ir_to_instr(env,e1),closure_ir_to_instr(env,e2)))
          _ => panic()
        }
      }
      IfLe(x,y,e1,e2) => {
        //println("Enter IfLe")
        match env[x.to_string()].unwrap() {
          Bool | Int => Ans(IfLe(x.to_string(),V(y.to_string()),closure_ir_to_instr(env,e1),closure_ir_to_instr(env,e2)))
          Double => Ans(IfFLe(x.to_string(),y.to_string(),closure_ir_to_instr(env,e1),closure_ir_to_instr(env,e2)))
          _ => panic()
        }
      }
      Let((n,lt),e1,e2) => {
        //println("Enter Let")
        let new_env = env.add(n.to_string(),lt)
        let i1 = closure_ir_to_instr(env,e1)
        let i2 = closure_ir_to_instr(new_env,e2)
        concat(i1,(n.to_string(),lt),i2)
      }
      Var(n) => {
        //println("Enter Var")
        match env[n.to_string()].unwrap(){
          Unit => Ans(Nop)
          Double => Ans(FMovD(n.to_string()))
          _ => Ans(Mov(n.to_string()))
        }
      }
      MakeClosure((n,lt),{name:nm,actual_free_vars:fvar},e) => {
        //println("Enter MakeClosure")
        let i = closure_ir_to_instr(env.add(n.to_string(),lt),e)
        let (offset,store_fv) = expand(
          fvar.map(fn {el => (el.to_string(),env[el.to_string()].unwrap())}),
          (4,i),
          fn {el,offset,store_fv => seq(StDF(el,n.to_string(),C(offset)),store_fv)},
          fn {el,_,offset,store_fv => seq(St(el,n.to_string(),C(offset)),store_fv)})
        let la = gen_id("l")
        Let((n.to_string(),lt), Mov(reggp),
          Let((reggp,Int),Add(reggp,C(align(offset))),
            Let((la,Int),La(nm._),seq(St(la,n.to_string(),C(0)),store_fv))))
      }
      CallClosure(n,arrn) => {
        //println("Enter CallClosure \{n} \{arrn} \{env}")
        let arrnm = arrn.map(fn{e => e.to_string()})
        let (i,d) = separate(arrnm.map(fn {ele => (ele,env[ele].unwrap())}))
        Ans(CallCls(n.to_string(),i,d))
      }
      CallDirect(la,arrn) => {
        //println("Enter CallDirect")
        //let arrnm = arrn.map(fn{e => e.to_string()})
        //println("here")
        let (i,d) = separate(arrn.map(fn {ele => (ele.to_string(),env[ele.to_string()].unwrap())}))
        //println("here")
        Ans(CallDir(la._,i,d))
      }
      MakeTuple(arrn) => {
        //println("Enter MakeTuple")
        let t = gen_id("t")
        let (offset,store) = expand(
          arrn.map(fn{e => (e.to_string(),env[e.to_string()].unwrap())}),
          (0,Ans(Mov(t))),
          fn{e,offset,store=>seq(StDF(e,t,C(offset)),store)},
          fn{e,_,offset,store=>seq(St(e,t,C(offset)),store)})
        Let((t,Tuple(arrn.map(fn{e=>env[e.to_string()].unwrap()}))),Mov(reggp),/////////////
          Let((reggp,Int),Add(reggp,C(align(offset))),store))
      }
      LetTuple(arrnlt,v,e) => {
        //println("Enter LetTuple")
        let s = @closure.free_vars(e).map(fn {e=>e.to_string()})
        let mut new_env = env
        for i in arrnlt{
          new_env = new_env.add(i.0.to_string(),i.1)
        }
        let (offset,load) = expand(
          arrnlt.map(fn {e=>(e.0.to_string(),e.1)}),
          (0,closure_ir_to_instr(new_env,e)),
          fn{e,offset,load=>{
            if not(s.contains(e)) {
              load
            }
            else {
              fletd(e,LdDF(v.to_string(),C(offset)),load)
            }
          }},
          fn{e,t,offset,load=>{
            if not(s.contains(e)) {
              load
            }
            else {
              Let((e,t),Ld(v.to_string(),C(offset)),load)
            }
          }})
        load
      }
      ArrayGet(nm,idx) => {
        //println("Enter ArrayGet")
        let offset = gen_id("o")
        match env[nm.to_string()].unwrap() {
          Array(Unit) => Ans(Nop)
          Array(Double) => Let((offset,Int),Sll(idx.to_string(),C(3)),Ans(LdDF(nm.to_string(),V(offset))))
          Array(_) => Let((offset,Int),Sll(idx.to_string(),C(2)),Ans(Ld(nm.to_string(),V(offset))))
          _ => panic()
        }
      }
      ArrayPut(nm,idx,v) => {
        //println("Enter ArrayPut")
        let offset = gen_id("o")
        match env[nm.to_string()].unwrap() {
          Array(Unit) => Ans(Nop)
          Array(Double) => Let((offset,Int),Sll(idx.to_string(),C(3)),Ans(StDF(v.to_string(),nm.to_string(),V(offset))))
          Array(_) => Let((offset,Int),Sll(idx.to_string(),C(2)),Ans(St(v.to_string(),nm.to_string(),V(offset))))
          _ => panic()
        }
      }
      ExternalArray(l) => Ans(La(l._))
    }
}

pub fn fun_to_fun(fun : @closure.FuncDef) -> Fundef {
  let (i,d) = separate(fun.args.map(fn {e => (e.0.to_string(),e.1)}))
  let mut env = @immut/hashmap.new().add(fun.name._,fun.ty)
  for i in fun.args{
    env = env.add(i.0.to_string(),i.1)
  }
  for j in fun.formal_free_vars{
    env = env.add(j.0.to_string(),j.1)
  }
  //println(env)
  let nm = fun.name._
  let (offset,load) = expand(
    fun.formal_free_vars.map(fn {e=>(e.0.to_string(),e.1)}),
    (4,closure_ir_to_instr(env,fun.body)),
    fn {e,offset,load=>fletd(e,LdDF(nm,C(offset)),load)},
    fn {e,t,offset,load=>Let((e,t),Ld(nm,C(offset)),load)}
  )
  match fun.ty {
    ClosureFn(_,t) | DirectFn(_,t)=> {name:nm,args:i,fargs:d,body:load,ret:t}
    _ => panic()
  }
}

pub fn prog_to_prog(prog:@closure.Program) -> Prog{
  data.val = []
  let fundefs = prog.fundefs.map(fun_to_fun)
  //println("Prog fundefs parse succeed!")
  let body = closure_ir_to_instr(@immut/hashmap.new(),prog.body)
  //println("Prog body parse succeed!")
  {ftable:data.val,funlist:fundefs,body:body}
}

