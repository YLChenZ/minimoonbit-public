enum AllocResult {
  Alloc(String)
  Spill(String)
} derive (Show)

typealias RegEnv = @immut/hashmap.T[String,String]
// 定义辅助函数 `target_args`，处理 `Call` 指令中的参数寄存器目标化
fn target_args(src: String, all: Array[String], n: Int, ys: Array[String]) -> Array[String] {
  //println("Enter target_args \{src} \{all} \{n} \{ys}")
    let mut result = []
    if ys == [] {
      result = []
    }
    else {
      let ys_t = ys.copy()
      let _ = ys_t.remove(0)
      if ys[0] == src {
        let res = target_args(src,all,n+1,ys_t)
        result = [all[n]]+res
      }
      else {
        result = target_args(src,all,n+1,ys_t)
      }
    }
    result
}

// 定义 `target` 函数，用于实现寄存器的目标化
fn target(src: String, dest: (String, @closure.LowType), instr: Instr) -> (Bool, Array[String]) {
  //println("Enter target \{src} \{dest} \{instr}")
  match instr {
    Ans(exp) => target_prime(src, dest, exp)
    Let((x, t), exp, e) => {
        let (c1, rs1) = target_prime(src, (x,t), exp)
        if c1 {
            return (true, rs1)
        }
        let (c2, rs2) = target(src, dest, e)
        (c2, rs1+rs2)
    }
  }
}

// 定义 `target_prime` 函数，用于实现寄存器目标化和合并操作的具体逻辑
fn target_prime(src: String, dest : (String,@closure.LowType), exp: Exp) -> (Bool, Array[String]) {
  //println("Enter target_prime \{src} \{dest} \{exp}")
    match exp {
      Mov(x) => {
        //println("Enter \{exp} in target_prime")
        if x == src && is_reg(dest.0) {
          assert_not_eq?(dest.1,Unit).unwrap()
          assert_not_eq?(dest.1,Double).unwrap()
          (false, [dest.0])
        }
        else {(false, [])}
      }
      FMovD(x) => {
        //println("Enter \{exp} in target_prime")
        if x == src && is_reg(dest.0){
          assert_eq?(dest.1,Double).unwrap()
          (false, [dest.0])
        }
        else {(false, [])}
      }
      IfEq(_, _, e1, e2) | IfLe(_, _, e1, e2) | IfGe(_, _, e1, e2) |
      IfFEq(_, _, e1, e2) | IfFLe(_, _, e1, e2) => {
        //println("Enter \{exp} in target_prime")
          let (c1, rs1) = target(src, dest, e1)
          let (c2, rs2) = target(src, dest, e2)
          (c1 && c2, rs1+rs2)
      }
      CallCls(x, ys, zs) => {
        //println("Enter \{exp} in target_prime")
          let args_regs = target_args(src, all_allocatable_regs, 0, ys)
          let fregs_args = target_args(src, all_allocatable_fregs_for_double, 0, zs)
          let cl_reg = if x == src { [regcl] } else { [] }
          (true, args_regs+fregs_args+cl_reg)
      }
      CallDir(_, ys, zs) => {
        //println("Enter \{exp} in target_prime")
          let args_regs = target_args(src, all_allocatable_regs, 0, ys)
          let fregs_args = target_args(src, all_allocatable_fregs_for_double, 0, zs)
          //println("\{args_regs} \{fregs_args}")
          (true, args_regs+fregs_args)
      }
      _ => (false, [])
  }
}

pub fn alloc(
  dest: (String,@closure.LowType),
  cont:Instr, regenv:RegEnv,
  x:String, t:@closure.LowType) -> AllocResult {
    //println("Enter alloc \{dest} \{cont} \{x} \{t} \{regenv}")
   assert_eq?(regenv[x],None).unwrap()
  let all = match t {
    Unit => ["zero"]
    Double => all_allocatable_fregs_for_double
    _ => all_allocatable_regs
  }
  if all == ["zero"] {
    return Alloc("zero")
  }
  if is_reg(x) {
    return Alloc(x)
  }
  else {
    let free = fv_instr(cont)
    let (c,prefer) = target(x,dest,cont)
    //println((c,prefer))
    //println(regenv)
    let live : @immut/sorted_set.T[String]= free.copy().fold(fn {
        live,y => {
          if is_reg(y) {
            live.add(y)
          }
          else {
            match regenv.find(y) {
              Some(res) => {live.add(res)}
              None => live
            }
          }
        }
      },init=@immut/sorted_set.new())
      //println(regenv)
    let r = (prefer+all).copy().search_by(fn {e=>not(live.contains(e))})
    match r {
      Some(idx) => {
        //println(regenv)
        //println(Alloc((prefer+all)[idx]))
        return Alloc((prefer+all)[idx])
      }
      None => {
        let y = free.rev().search_by(fn {e=> {
          not(is_reg(e)) &&
          match regenv[e] {
            Some(res) => all.contains(res)
            None => false
          }
        }})
        return Spill(free.rev()[y.unwrap()])
      }
    }
  }
}


pub fn add(x: String,r: String,regenv: RegEnv) -> RegEnv {
  if is_reg(x) {
    assert_eq?(x,r).unwrap()
    regenv
  }
  else {
    regenv.add(x,r)
  }
}

type! NoReg(String,@closure.LowType) derive (Show)
pub fn find(x:String,t:@closure.LowType,regenv:RegEnv) -> String!NoReg {
  //println("Enter find \{x} \{t} \{regenv}")
  if is_reg(x) {
    x
  }
  else {
    match regenv[x]{
      Some(res) => res
      None => {//println("raise NoReg in \{x}");
      raise NoReg((x,t))}
    }
  }
}

pub fn find_prime(x:IdOrImm,regenv:RegEnv) -> IdOrImm!NoReg{
  match x {
    V(x) => V(find!(x,Int,regenv))
    c => c
  }
}

pub fn instr_reg_alloc(
  dest :(String,@closure.LowType),
  cont : Instr,
  regenv : RegEnv,
  instr : Instr) -> (Instr,RegEnv) {
    match instr {
      Ans(exp) => {//println("Enter \{instr} in instr_reg_alloc");
      spill_to_reg(dest,cont,regenv,exp)}
      Let(xt,exp,i) => {
        //println("Enter \{instr} in instr_reg_alloc")
        //println("\{regenv} in instr_reg_alloc")
        assert_eq?(regenv[xt.0],None).unwrap()
        //println("Here1 in instr_reg_alloc")
        let cont_prime = concat(i,dest,cont)
        let (i1,regenv1) = spill_to_reg(xt,cont_prime,regenv,exp)
        //println("Here2 in instr_reg_alloc")
        //println(regenv1)
        match alloc(dest,cont_prime,regenv1,xt.0,xt.1){
          Spill(y) => {
            //println("Here3 in instr_reg_alloc")
            let r = regenv1[y].unwrap()
            let regenv_t = add(xt.0,r,regenv1.remove(y))
            let (i2,regenv2) = instr_reg_alloc(dest,cont,regenv_t,i)
            let save = match regenv[y] {
              Some(res) => Save(res,y)
              None => Nop
            }
            (seq(save,concat(i1,(r,xt.1),i2)),regenv2)
          }
          Alloc(r) => {
            //println("Here4 in instr_reg_alloc")
            //println(regenv1)
            let (i2,regenv2) = instr_reg_alloc(dest,cont,add(xt.0,r,regenv1),i)
            //println("Here5 in instr_reg_alloc")
            (concat(i1,(r,xt.1),i2),regenv2)
          }
        }
      }
    }
  }

pub fn spill_to_reg(
  dest : (String,@closure.LowType),
  cont : Instr,
  regenv : RegEnv,
  exp : Exp) -> (Instr,RegEnv) {
    try instr_reg_alloc_prime!(dest,cont,regenv,exp) catch {
      NoReg((x,t)) => {//println("After raise NoReg");
      instr_reg_alloc(dest,cont,regenv,Let((x,t),Restore(x),Ans(exp)))}
    } else {
      _ => {//println("No NoReg in spill_to_reg")
      //println(regenv)
      instr_reg_alloc_prime?(dest,cont,regenv,exp).unwrap()}
    }
}

pub fn instr_reg_alloc_prime(
  dest : (String,@closure.LowType),
  cont : Instr,
  regenv : RegEnv,
  exp : Exp) -> (Instr,RegEnv)!NoReg {
    match exp {
      Nop | Li(_) | La(_) | Comment(_) | Restore(_) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(exp),regenv)}
      Mov(x) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Mov(find!(x,Int,regenv))),regenv)}
      Neg(x) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Neg(find!(x,Int,regenv))),regenv)}
      Add(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Add(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      Sub(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Sub(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      Mul(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Mul(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      Div(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Div(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      Sll(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Sll(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      Ld(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(Ld(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      St(x,y,z) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(St(find!(x,Int,regenv),find!(y,Int,regenv),find_prime!(z,regenv))),regenv)}
      FMovD(x) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(FMovD(find!(x,Double,regenv))),regenv)}
      FNegD(x) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(FNegD(find!(x,Double,regenv))),regenv)}
      FAddD(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(FAddD(find!(x,Double,regenv),find!(y,Double,regenv))),regenv)}
      FSubD(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(FSubD(find!(x,Double,regenv),find!(y,Double,regenv))),regenv)}
      FMulD(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(FMulD(find!(x,Double,regenv),find!(y,Double,regenv))),regenv)}
      FDivD(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(FDivD(find!(x,Double,regenv),find!(y,Double,regenv))),regenv)}
      LdDF(x,y) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(LdDF(find!(x,Int,regenv),find_prime!(y,regenv))),regenv)}
      StDF(x,y,z) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      (Ans(StDF(find!(x,Double,regenv),find!(y,Int,regenv),find_prime!(z,regenv))),regenv)}
      IfEq(x,y,i1,i2) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_if!(dest,cont,regenv,exp,
                                  fn{instr1,instr2=>IfEq(find!(x,Int,regenv),find_prime!(y,regenv),instr1,instr2)},i1,i2)}
      IfLe(x,y,i1,i2) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_if!(dest,cont,regenv,exp,
                                  fn{instr1,instr2=>IfLe(find!(x,Int,regenv),find_prime!(y,regenv),instr1,instr2)},i1,i2)}
      IfGe(x,y,i1,i2) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_if!(dest,cont,regenv,exp,
                                  fn{instr1,instr2=>IfGe(find!(x,Int,regenv),find_prime!(y,regenv),instr1,instr2)},i1,i2)}
      IfFEq(x,y,i1,i2) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_if!(dest,cont,regenv,exp,
                                  fn{instr1,instr2=>IfFEq(find!(x,Double,regenv),find!(y,Double,regenv),instr1,instr2)},i1,i2)}
      IfFLe(x,y,i1,i2) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_if!(dest,cont,regenv,exp,
                                  fn{instr1,instr2=>IfFLe(find!(x,Double,regenv),find!(y,Double,regenv),instr1,instr2)},i1,i2)}                                                        
      CallCls(x,ys,zs) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_call!(dest,cont,regenv,exp,fn{ys,zs=>CallCls(find!(x,Int,regenv),ys,zs)},ys,zs)}
      CallDir(l,ys,zs) => {//println("Enter \{exp} in instr_reg_alloc_prime");
      instr_reg_alloc_call!(dest,cont,regenv,exp,fn{ys,zs=>CallDir(l,ys,zs)},ys,zs)}
      Save(_) => panic()
      _ => panic()
    }
  }

pub fn instr_reg_alloc_if(
  dest : (String,@closure.LowType),
  cont : Instr,
  regenv : RegEnv,
  exp : Exp,
  constr : (Instr,Instr) -> Exp!NoReg,
  i1 : Instr,i2 : Instr) -> (Instr,RegEnv)!NoReg {
    let (i_1,regenv1) = instr_reg_alloc(dest,cont,regenv,i1)
    let (i_2,regenv2) = instr_reg_alloc(dest,cont,regenv,i2)
    let t = fv_instr(cont)
    let regenv3 = t.copy().fold(fn (regenv:RegEnv,x){
      if is_reg(x) {
        regenv
      }
      else {
        let r1 = regenv1[x]
        let r2 = regenv2[x]
        match (r1,r2) {
          (Some(res1),Some(res2)) => {
            if res1 == res2 {
              regenv.add(x,res1)
            }
            else {regenv}
          }
          _ => regenv
        }
      }
    },init=@immut/hashmap.new())
    let i = t.copy().fold(fn {e,x => {
      if x == dest.0 || regenv.find(x)==None || regenv3.find(x)!=None {e}
      else {seq(Save(regenv[x].unwrap(),x),e)}
    }},init=Ans(constr!(i_1,i_2)))
    (i,regenv3)
  }

pub fn instr_reg_alloc_call(
  dest : (String,@closure.LowType),
  cont : Instr,
  regenv : RegEnv,
  exp : Exp,
  constr : (Array[String],Array[String]) -> Exp!NoReg,
  ys : Array[String],zs : Array[String]) -> (Instr,RegEnv)!NoReg {
    //println(regenv)
    let t = fv_instr(cont)
    let i = t.copy().fold(fn {
      e,x => {
        if x == dest.0 || regenv[x]==None {
          e
        } else {
          seq(Save(regenv[x].unwrap(),x),e)
        }
      }
    }, init = (Ans(constr!(ys.map(fn{y=>find?(y,Int,regenv).unwrap()}),zs.map(fn{z=>find?(z,Double,regenv).unwrap()})))))
    (i,regenv)
  }

pub fn fundef_reg_alloc(fun : Fundef) -> Fundef {
  //println("Start in fundef_reg_alloc")
  let regenv = @immut/hashmap.new().add(fun.name,regcl)
  let (i,arg_regs,regenv1) = fun.args.copy().fold(fn (t:(Int,Array[String],RegEnv),y){
    {
      let (i,arg_regs,regenv) = t
      let r = all_allocatable_regs[i]
      let mut new_regenv = regenv
      //println("Get regs in fundef_reg_alloc")
      assert_false?(is_reg(y)).unwrap()
      new_regenv = regenv.add(y,r)
      (i+1,arg_regs+[r],new_regenv)
    }
  },init = (0,[],regenv))
  let (d,farg_regs,regenv2) = fun.fargs.copy().fold(fn (t:(Int,Array[String],RegEnv),z) {
    {
      let (d,farg_regs,regenv) = t
      let fr = all_allocatable_fregs_for_double[d]
      let mut new_regenv = regenv
      //println("Get fregs in fundef_reg_alloc")
      assert_false?(is_reg(z)).unwrap()
      new_regenv = regenv.add(z,fr)
      (d+1,farg_regs+[fr],new_regenv)
    }
  },init = (0,[],regenv1))
  // //println(regenv2)
  let a = match fun.ret {
    Unit => gen_tmp()
    Double => all_allocatable_fregs_for_double[0]
    _ => all_allocatable_regs[0]
  }
  let (i,regenv3) = instr_reg_alloc((a,fun.ret),Ans(Mov(a)),regenv2,fun.body)
  // //println(regenv3)
  //println("End in fundef_reg_alloc")
  {name:fun.name,args:arg_regs,fargs:farg_regs,body:i,ret:fun.ret}
}

pub fn prog_alloc_reg(prog:Prog) -> Prog{
  let fundefs = prog.funlist.map(fundef_reg_alloc)
  //println("Prog fundefs parse succeed!")
  let (i,regenv)= instr_reg_alloc((gen_tmp(),Unit),Ans(Nop),@immut/hashmap.new(),prog.body)
  //println("Prog body parse succeed!")
  {ftable:prog.ftable,funlist:fundefs,body:i}
}

enum Dest{
  Tail
  NonTail(String)
} derive(Show)

let stackset :Ref[@immut/sorted_set.T[String]]= {val:@immut/sorted_set.new()}
let stackmap :Ref[Array[String]]= {val:[]}

pub fn save(x : String) -> Unit {
  stackset.val = stackset.val.add(x)
  if not(stackmap.val.contains(x)) {
    stackmap.val.push(x)
  }
}

pub fn savef(x : String) -> Unit {
  stackset.val = stackset.val.add(x)
  if not(stackmap.val.contains(x)) {
    let pad = if stackmap.val.length()%2==0 {
      []
    } else {[gen_tmp()]}
    stackmap.val = stackmap.val+pad+[x,x]
  }
}

pub fn locate(x:String) -> Array[Int] {
  fn loc(xs:Array[String]) -> Array[Int] {
    match xs {
      [] => []
      _ => {
        let zs = xs.copy()
        let _ = zs.remove(0)
        let t = loc(zs).map(fn{x=>x+1})
        if x == xs[0] {
          [0]+t
        }
        else {t}
      }
    }
  }
  loc(stackmap.val)
}

pub fn offset(x:String) -> Int {
  4*locate(x)[0]
}

pub fn stacksize () -> Int {
  align(4*(stackmap.val.length()+1))
}

pub fn shuffle(sw : String,xys:Array[(String,String)]) -> Array[(String,String)] {
  let xys = xys.filter(fn {x=>x.0!=x.1})
  let fst_xys = xys.map(fn {x => x.0})
  let xys = xys.filter(fn {x=>fst_xys.contains(x.1)})
  let acyc = xys.filter(fn {x=>not(fst_xys.contains(x.1))})
  match (xys,acyc) {
    ([],[]) => []
    ([(x,y),_],[]) => [(y,sw),(x,y)] + shuffle(sw,xys.map(fn {
      (y1,z) => if y == y1 {
        (sw,z)
      } else {(y1,z)}
    }))
    _ => acyc + shuffle(sw,xys)
  } 
}


let str_to_reg : Map[String,Reg]= {"zero":Zero,"ra":Ra,"sp":Sp,  "gp":Gp, "tp":Tp, "t0":T0, "t1":T1, "t2":T2, "fp":Fp, 
    "s1" : S1, "a0":A0, "a1":A1, "a2":A2, "a3":A3, "a4":A4, "a5":A5, "a6":A6, "a7":A7, "s2":S2, "s3":S3, "s4":S4, 
    "s5":S5, "s6":S6, "s7":S7, "s8":S8, "s9":S9, "s10":S10, "s11":S11, "t3":T3, "t4":T4, "t5":T5, "t6":T6}
let str_to_freg : Map[String,FReg] = {"ft0":Ft0, "ft1":Ft1, "ft2":Ft2, "ft3":Ft3, "ft4":Ft4, "ft5":Ft5, "ft6":Ft6, "ft7":Ft7,
    "fs0":Fs0, "fs1":Fs1, "fa0":Fa0, "fa1":Fa1, "fa2":Fa2, "fa3":Fa3, "fa4":Fa4, "fa5":Fa5,
    "fa6":Fa6, "fa7":Fa7, "fs2":Fs2, "fs3":Fs3, "fs4":Fs4, "fs5":Fs5, "fs6":Fs6, "fs7":Fs7,
    "fs8":Fs8, "fs9":Fs9, "fs10":Fs10, "fs11":Fs11, "ft8":Ft8, "ft9":Ft9, "ft10":Ft10, "ft11":Ft11}
fn idorimm_to_reg(idorimm : IdOrImm) -> Reg{
  match idorimm {
    V(s) => str_to_reg[s].unwrap()
    _ => panic()
  }
}

fn idorimm_to_freg(idorimm : IdOrImm) -> FReg{
  match idorimm {
    V(s) => str_to_freg[s].unwrap()
    _ => panic()
  }
}

pub fn emit_instr_rvasm(dest:Dest,instr:Instr) -> Array[RvAsm]{
  match instr {
    Ans(exp) => emit_exp_rvasm(dest,exp)
    Let((x,t),exp,i) => {
      //println(dest)
      let asm_hd = emit_exp_rvasm(NonTail(x),exp)
      let asm_tail = emit_instr_rvasm(dest,i)
      asm_hd + asm_tail
    }
  }
}
pub fn emit_exp_rvasm(dest : Dest,exp : Exp) -> Array[RvAsm] {
  match (dest,exp) {
    (NonTail(_),Nop) => []
    (NonTail(x),Li(i)) => [Li(str_to_reg[x].unwrap(),i.to_string())]
    (NonTail(x),La(s)) => [La(str_to_reg[x].unwrap(),s.to_string())]
    (NonTail(x),Mov(y)) => {if x == y { [] }else {[Mv(str_to_reg[x].unwrap(),str_to_reg[y].unwrap())]}}
    (NonTail(x),Neg(y)) => [Neg(str_to_reg[x].unwrap(),str_to_reg[y].unwrap())]
    (NonTail(x),Add(y,z)) => match z {
      V(_) => [Add(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),idorimm_to_reg(z))]
      C(i) => [Addi(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),i)]
    }
    (NonTail(x),Sub(y,z)) => match z {
      V(_) => [Sub(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),idorimm_to_reg(z))]
      C(i) => [Addi(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),-i)]
    }
    (NonTail(x),Mul(y,z)) => match z {
      V(_) => [Mul(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),idorimm_to_reg(z))]
      C(i) => @util.die("Mul's right is imm")
    }
    (NonTail(x),Div(y,z)) => match z {
      V(_) => [Div(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),idorimm_to_reg(z))]
      C(i) => @util.die("Div's right is imm")
    }
    (NonTail(x),Sll(y,z)) => match z {
      V(_) => [Sll(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),idorimm_to_reg(z))]
      C(i) => [Slli(str_to_reg[x].unwrap(),str_to_reg[y].unwrap(),i)]
    }
    (NonTail(x),Ld(y,z)) => match z {
      V(_) => @util.die("Ld's offset is reg")
      C(i) => [Lw(str_to_reg[x].unwrap(),{base:str_to_reg[y].unwrap(),offset:i})]
    }
    (NonTail(_),St(x,y,z)) => match z {
      V(_) => @util.die("St's offset is reg")
      C(i) => {//println("expAsmSt here");
      [Sw(str_to_reg[x].unwrap(),{base:str_to_reg[y].unwrap(),offset:i})]}
    }
    (NonTail(x),FMovD(y)) => {if x == y { [] }else {
      [FmvD(str_to_freg[x].unwrap(),str_to_freg[y].unwrap()),
      FmvD(str_to_freg[co_freg(x)].unwrap(),str_to_freg[co_freg(y)].unwrap())]
    }}
    (NonTail(x),FNegD(y)) => {if x == y { [] }else {
      [FnegD(str_to_freg[x].unwrap(),str_to_freg[y].unwrap()),
      FmvD(str_to_freg[co_freg(x)].unwrap(),str_to_freg[co_freg(y)].unwrap())]
    }}
    (NonTail(x),FAddD(y,z)) => [FaddD(str_to_freg[x].unwrap(),str_to_freg[y].unwrap(),str_to_freg[z].unwrap())]
    (NonTail(x),FSubD(y,z)) => [FsubD(str_to_freg[x].unwrap(),str_to_freg[y].unwrap(),str_to_freg[z].unwrap())]
    (NonTail(x),FMulD(y,z)) => [FmulD(str_to_freg[x].unwrap(),str_to_freg[y].unwrap(),str_to_freg[z].unwrap())]
    (NonTail(x),FDivD(y,z)) => [FdivD(str_to_freg[x].unwrap(),str_to_freg[y].unwrap(),str_to_freg[z].unwrap())]
    (NonTail(x),LdDF(y,z)) => match z {
      V(_) => @util.die("LdDF's offset is reg")
      C(i) => [Fld(str_to_freg[x].unwrap(),{base:str_to_reg[y].unwrap(),offset:i})]
    }
    (NonTail(_),StDF(x,y,z)) => match z {
      V(_) => @util.die("StDF's offset is reg")
      C(i) => [Fsd(str_to_freg[x].unwrap(),{base:str_to_reg[y].unwrap(),offset:i})]
    }
    (NonTail(_),Comment(s)) => [Comment(s)]
    (NonTail(_),Save(x,y)) => {
      let b = stackset.val.contains(y)
      let b1 = all_allocatable_regs.contains(x)
      let b2 = all_allocatable_fregs_for_double.contains(x)
      if b1 && not(b) {
        //println("here1")
        save(y)
        [Sd(str_to_reg[x].unwrap(),{base:str_to_reg[regsp].unwrap(),offset:offset(y)})]
      }
      else if b2 && b{
        //println("here2")
        savef(y)
        [Fsd(str_to_freg[x].unwrap(),{base:str_to_reg[regsp].unwrap(),offset:offset(y)})]
      }
      else {assert_true?(b).unwrap();[]}
    }
    (NonTail(x),Restore(y)) => {
      
      if all_allocatable_regs.contains(x) {
        //println("here3 \{x} \{y}")
        // let stack_back = stackmap.val
        // save(y)
        // //println("\{stackmap.val}")
        let offset = offset(y)
        // stackmap.val = stack_back
        [Ld(str_to_reg[x].unwrap(),{base:str_to_reg[regsp].unwrap(),offset:offset})]
      }
      else {
        //println("here4 \{x} \{y}")
        assert_true?(all_allocatable_fregs_for_double.contains(x)).unwrap()
        // savef(y)
        [Fld(str_to_freg[x].unwrap(),{base:str_to_reg[regsp].unwrap(),offset:offset(y)})]
      }
    }
    (Tail,Nop|St(_)|StDF(_)|Comment(_)|Save(_) as exp) => {
      let rs1 = emit_exp_rvasm(NonTail(gen_tmp()),exp)
      rs1
    }
    (Tail,Li(_)|La(_)|Mov(_)|Neg(_)|Add(_)|Sub(_)|Mul(_)|Div(_)|Sll(_)|Ld(_) as exp) => {
      let rs1 = emit_exp_rvasm(NonTail(all_allocatable_regs[0]),exp)
      rs1
    }
    (Tail,FMovD(_)|FNegD(_)|FAddD(_)|FSubD(_)|FMulD(_)|FDivD(_)|LdDF(_) as exp) => {
      let rs1 = emit_exp_rvasm(NonTail(all_allocatable_fregs_for_double[0]),exp)
      rs1
    }
    (Tail,Restore(x) as exp) => {
      match locate(x) {
        [i] => emit_exp_rvasm(NonTail(all_allocatable_regs[0]),exp)
        [i,j] => {
          if i+1 == j {
            emit_exp_rvasm(NonTail(all_allocatable_fregs_for_double[0]),exp)
          }
          else {[]}
        }
        _ => {assert_true?(false).unwrap();[]}
      }
    }
    (Tail,IfEq(x,y,e1,e2)) => emit_instr_tail_if_rvasm(x,("",y),e1,e2,"beq")
    (Tail,IfLe(x,y,e1,e2)) => emit_instr_tail_if_rvasm(x,("",y),e1,e2,"ble")
    (Tail,IfGe(x,y,e1,e2)) => emit_instr_tail_if_rvasm(x,("",y),e1,e2,"bge")
    (Tail,IfFEq(x,y,e1,e2)) => emit_instr_tail_if_rvasm(x,(y,V("")),e1,e2,"beqf")
    (Tail,IfFLe(x,y,e1,e2)) => emit_instr_tail_if_rvasm(x,(y,V("")),e1,e2,"blef")
    (NonTail(z),IfEq(x,y,e1,e2)) => emit_instr_nontail_if_rvasm(dest,x,("",y),e1,e2,"beq")
    (NonTail(z),IfLe(x,y,e1,e2)) => emit_instr_nontail_if_rvasm(dest,x,("",y),e1,e2,"ble")
    (NonTail(z),IfGe(x,y,e1,e2)) => emit_instr_nontail_if_rvasm(dest,x,("",y),e1,e2,"bge")
    (NonTail(z),IfFEq(x,y,e1,e2)) => emit_instr_nontail_if_rvasm(dest,x,(y,V("")),e1,e2,"beqf")
    (NonTail(z),IfFLe(x,y,e1,e2)) => emit_instr_nontail_if_rvasm(dest,x,(y,V("")),e1,e2,"blef")
    (Tail,CallCls(x,ys,zs)) => {
      let args = emit_fun_args([(x,regcl)],ys,zs)
      let t1 : RvAsm = Ld(str_to_reg[regswp].unwrap(),{base:str_to_reg[regcl].unwrap(),offset:0})
      let t2 = Jr(str_to_reg[regswp].unwrap())
      args+[t1,t2]
    }
    (Tail,CallDir(x,ys,zs)) => {
      //println("expAsmCallDirTail here")
      let args = emit_fun_args([],ys,zs)
      println(args)
      let t :RvAsm = Call(Label(x))
      args+[t]
    }
    (NonTail(a),CallCls(x,ys,zs)) => {
      //println("expAsmCallCls \{x} here1")
      let args = emit_fun_args([(x,regcl)],ys,zs)
      let ss = stacksize()
      let t1 = Sd(Ra,{base:Sp,offset:(ss-4)})
      let t2 :RvAsm = Ld(str_to_reg[regswp].unwrap(),{base:str_to_reg[regcl].unwrap(),offset:0})
      let t3 = Jr(str_to_reg[regswp].unwrap())
      let t4 = Addi(Sp,Sp,ss)
      let t5 :RvAsm = Addi(Sp,Sp,-ss)
      let t6 :RvAsm = Ld(Ra,{base:Sp,offset:ss-4})
      let mut t7 : Array[RvAsm] = []
      //println("expAsmCallCls here2")
      if all_allocatable_regs.contains(a) && a != all_allocatable_regs[0] {
        t7 = [Mv(str_to_reg[all_allocatable_regs[0]].unwrap(),str_to_reg[a].unwrap())]
      }
      else if all_allocatable_fregs_for_double.contains(a) && a != all_allocatable_fregs_for_double[0] {
        let tt1 = FmvD(str_to_freg[all_allocatable_fregs_for_double[0]].unwrap(),str_to_freg[a].unwrap())
        let tt2 = FmvD(str_to_freg[co_freg(all_allocatable_fregs_for_double[0])].unwrap(),str_to_freg[co_freg(a)].unwrap())
        t7 = [tt1,tt2]
      }
      else {t7 = []}
      args+[t1,t2,t3,t4,t5,t6]+t7
    }
    (NonTail(a),CallDir(x,ys,zs)) => {
      // //println("expAsmCallDir \{x} here1")
      let args = emit_fun_args([],ys,zs)
      let ss = stacksize()
      // println(ss)
      let t3 : RvAsm = Call(x)
      let mut t7 : Array[RvAsm] = []
      //println("expAsmCallDir here2")
      if all_allocatable_regs.contains(a) && a != all_allocatable_regs[0] {
        t7 = [Mv(str_to_reg[all_allocatable_regs[0]].unwrap(),str_to_reg[a].unwrap())]
      }
      else if all_allocatable_fregs_for_double.contains(a) && a != all_allocatable_fregs_for_double[0] {
        let tt1 = FmvD(str_to_freg[all_allocatable_fregs_for_double[0]].unwrap(),str_to_freg[a].unwrap())
        let tt2 = FmvD(str_to_freg[co_freg(all_allocatable_fregs_for_double[0])].unwrap(),str_to_freg[co_freg(a)].unwrap())
        t7 = [tt1,tt2]
      }
      //println("expAsmCallDir here3")
      args+[t3]+t7
    }
    _ => panic()
  }
}

let label_counter : Ref[Int] = {val:0}
pub fn emit_instr_tail_if_rvasm(x : String,y : (String,IdOrImm),i1 : Instr,i2 : Instr,b : String) -> Array[RvAsm] {
  let mut res = []
  // let b_then = RvAsm::Label(gen_id(b+"_then"+label_counter.val.to_string()))
  let b_else = gen_id(b+"_else"+label_counter.val.to_string())
  // let b_next = RvAsm::Label(gen_id(b+"_next"+label_counter.val.to_string()))
  label_counter.val += 1
  let stackset_back = stackset.val
  let i1_asm = emit_instr_rvasm(Tail,i1)
  stackset.val = stackset_back
  let i2_asm = emit_instr_rvasm(Tail,i2)
  match b {
    "beq" => {res = res + [Bne(str_to_reg[x].unwrap(),idorimm_to_reg(y.1),b_else)]}
    "ble" => {res = res + [Bgt(str_to_reg[x].unwrap(),idorimm_to_reg(y.1),b_else)]}
    "bge" => {res = res + [Blt(str_to_reg[x].unwrap(),idorimm_to_reg(y.1),b_else)]}
    "beqf" => {res = res + [FeqD(str_to_reg["a7"].unwrap(),str_to_freg[x].unwrap(),str_to_freg[y.0].unwrap()),
                            Beq(str_to_reg["a7"].unwrap(),Zero,b_else)]}
    "blef" => {res = res + [FleD(str_to_reg["a7"].unwrap(),str_to_freg[x].unwrap(),str_to_freg[y.0].unwrap()),
                            Beq(str_to_reg["a7"].unwrap(),Zero,b_else)]}
    _ => panic()
  }
  res = res + i1_asm + [Label(b_else)] + i2_asm
  res
}

pub fn emit_instr_nontail_if_rvasm(dest:Dest,x : String,y : (String,IdOrImm),i1 : Instr,i2 : Instr,b : String) -> Array[RvAsm] {
  let mut res = []
  // let b_then = RvAsm::Label(gen_id(b+"_then"+label_counter.val.to_string()))
  let b_else = gen_id(b+"_else"+label_counter.val.to_string())
  let b_next = gen_id(b+"_next"+label_counter.val.to_string())
  label_counter.val += 1
  let stackset_back = stackset.val
  let i1_asm = emit_instr_rvasm(dest,i1)
  let stackset1 = stackset.val
  stackset.val = stackset_back
  let i2_asm = emit_instr_rvasm(dest,i2)
  match b {
    "beq" => {res = res + [Bne(str_to_reg[x].unwrap(),idorimm_to_reg(y.1),b_else)]}
    "ble" => {res = res + [Bgt(str_to_reg[x].unwrap(),idorimm_to_reg(y.1),b_else)]}
    "bge" => {res = res + [Blt(str_to_reg[x].unwrap(),idorimm_to_reg(y.1),b_else)]}
    "beqf" => {res = res + [FeqD(str_to_reg["a7"].unwrap(),str_to_freg[x].unwrap(),str_to_freg[y.0].unwrap()),
                            Beq(str_to_reg["a7"].unwrap(),Zero,b_else)]}
    "blef" => {res = res + [FleD(str_to_reg["a7"].unwrap(),str_to_freg[x].unwrap(),str_to_freg[y.0].unwrap()),
                            Beq(str_to_reg["a7"].unwrap(),Zero,b_else)]}
    _ => panic()
  }
  //println(b_else)
  res = res + i1_asm + [J(b_next),Label(b_else)] + i2_asm + [Label(b_next)]
  let stackset2 = stackset.val
  stackset.val = stackset1.inter(stackset2)
  res
}

pub fn emit_fun_args(x_reg_cl : Array[(String,String)],ys: Array[String],zs: Array[String]) -> Array[RvAsm] {
  let (i,yrs) = ys.fold(fn {
    (i,yrs),y => (i+1,[(y,all_allocatable_regs[i])]+yrs)
  },init = (0,x_reg_cl))
  let t1 = shuffle(regswp,yrs).map(fn {(y,r) => Mv(str_to_reg[y].unwrap(),str_to_reg[r].unwrap())})
  let (d,zfrs) = zs.fold(fn {
    (d,zfrs),z => (d+1,[(z,all_allocatable_fregs_for_double[d])]+zfrs)
  },init = (0,[]))
  let t2 = shuffle(fregswp,zfrs).map(fn {(z,fr) => [FmvD(str_to_freg[z].unwrap(),str_to_freg[fr].unwrap()),
  FmvD(str_to_freg[co_freg(z)].unwrap(),str_to_freg[co_freg(fr)].unwrap())]})
  let mut res = []
  for i in t2 {
    res = res + i
  }
  t1+res
}

pub fn emit_fundef(fundef:Fundef) -> AssemblyFunction {
  let mut export = false
  if fundef.name.starts_with("minimbt_") {
    export = true
  }
  let args_size = fundef.args.length()*4
  let fargs_size = fundef.fargs.length()*8
  let pre_size = args_size + fargs_size + 16
  let pre_size = align(pre_size)
  let pre = [Addi(Sp,Sp,-pre_size),
             Sd(Ra,{base:Sp,offset:(pre_size-8)}),
             Sd(Fp,{base:Sp,offset:(pre_size-16)}),
             Addi(Fp,Sp,pre_size)]
  stackset.val = @immut/sorted_set.new()
  stackmap.val = []
  let end :Array[RvAsm] = 
    [ Ld(Ra,{base:Sp,offset:pre_size-8}),
      Ld(Fp,{base:Sp,offset:pre_size-16}),
      Addi(Sp,Sp,pre_size),Ret]
  let body = emit_instr_rvasm(Tail,fundef.body)
  {name:fundef.name,export:export,body:pre+body+end}
}