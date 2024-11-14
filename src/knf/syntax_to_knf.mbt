pub typealias LocalEnv = @immut/hashmap.T[String, Type]

struct KnfEnv {
  mut counter : Int
  externals : @immut/hashmap.T[String, Type]
}

pub fn KnfEnv::new(externals : @immut/hashmap.T[String, Type]) -> KnfEnv {
  { counter: 1, externals }
}

pub fn KnfEnv::init_counter_from_existing(
  self : KnfEnv,
  existing : Knf
) -> Unit {
  self.counter = knf_max_counter(existing) + 1
}

fn KnfEnv::new_temp(self : KnfEnv) -> Name {
  let temp = Name::slot_only(self.counter)
  self.counter += 1
  temp
}

fn KnfEnv::new_named_temp(self : KnfEnv, name : Name) -> Name {
  let counter = self.counter
  self.counter += 1
  { ..name, slot: counter }
}
//insert_let插入let表达式，knf会涉及到很多对中间结果的保存，使用let表达式可以完成这个目的
//比如：abc都是常量
//let x = 1 + 2 + 3 ; stmt=>
//let _1 = 1 in let _2 = 2 in let _3 = 3 in let x = _1 + _2 + _3 ; stmt
//可以观察到最后部分与原表达式结构保持一致，只是中间结果用了不同临时变量来保存
fn insert_let(self : KnfEnv,s: @types.Syntax,t : @types.Type,f : (Name) -> Knf)  -> Knf{
  match s {
    Var(str) => {
      let x = @types.from_string?(str).unwrap()
      f(x)
    }
    _ => {
      let x = self.new_temp()
      let k = to_knf(self,s)
      Let((x,t),k,f(x))
    }
  }
}
pub fn KnfEnv::to_knf(self : KnfEnv, s : @types.Syntax) -> Knf { // !Failure
  match s {
    Unit => Unit
    Int(i) => Int(i)
    Double(d) => Double(d)
    Bool(b) => if b {Int(1)} else {Int(0)}
    Var(s) => Var(@types.from_string?(s).unwrap())
    Not(s) => to_knf(self,If(s,Bool(false),Bool(true)))
    Eq(s1,s2) => to_knf(self,If(Eq(s1,s2),Bool(true),Bool(false))) //if s1 ==s2 {true} else {false}
    LE(s1,s2) => to_knf(self,If(LE(s1,s2),Bool(true),Bool(false))) //if s1 <=s2 {true} else {false}
    Neg(syn,~kind) => { 
      match kind {
        Some(Int) => { insert_let(self,syn,Int,fn{t=>Neg(t)})}  
        Some(Double) => { insert_let(self,syn,Double,fn{t=>FNeg(t)})}
        _ => panic()
      }
    }
    Prim(lhs,rhs,op,~kind) => {  //1+2  let _1 = 1 in let _2 = 2 in Add(_1,_2)
      //println("Enter Prim")
      match kind {
        Some(Int) => match op{
          Add => insert_let(self,lhs,Int,fn{x=>insert_let(self,rhs,Int,fn{y=>Add(x,y)})})
          Sub => insert_let(self,lhs,Int,fn{x=>insert_let(self,rhs,Int,fn{y=>Sub(x,y)})})
          Mul => insert_let(self,lhs,Int,fn{x=>insert_let(self,rhs,Int,fn{y=>Mul(x,y)})})
          Div => insert_let(self,lhs,Int,fn{x=>insert_let(self,rhs,Int,fn{y=>Div(x,y)})})
        }
        Some(Double) => match op{
          Add => insert_let(self,lhs,Double,fn{x=>insert_let(self,rhs,Int,fn{y=>FAdd(x,y)})})
          Sub => insert_let(self,lhs,Double,fn{x=>insert_let(self,rhs,Int,fn{y=>FSub(x,y)})})
          Mul => insert_let(self,lhs,Double,fn{x=>insert_let(self,rhs,Int,fn{y=>FMul(x,y)})})
          Div => insert_let(self,lhs,Double,fn{x=>insert_let(self,rhs,Int,fn{y=>FDiv(x,y)})})
        }
        _ => panic()
      }
    }
    If(cond,b1,b2) => {
      //println("Enter If")
      match cond {
        Eq(lhs,rhs) => {
          let lt = @typing.infer(self.externals,lhs).rep()
          let rt = @typing.infer(self.externals,lhs).rep()
          insert_let(self,lhs,lt,fn{x=>insert_let(self,rhs,rt,fn{y=>IfEq(x,y,to_knf(self,b1),to_knf(self,b2))})})
        }
        LE(lhs,rhs) => {
          let lt = @typing.infer(self.externals,lhs).rep()
          let rt = @typing.infer(self.externals,lhs).rep()
          insert_let(self,lhs,lt,fn{x=>insert_let(self,rhs,rt,fn{y=>IfLe(x,y,to_knf(self,b1),to_knf(self,b2))})})
        }
        ///////这里还缺少情况cond=true or flase，还可以是cond=not exp
        Not(b) => to_knf(self,If(b,b2,b1))
        _ => to_knf(self,If(Eq(cond,Bool(false)),b2,b1))
      }
    }
    Let((s,ty),s1,s2) => {
      //println("Enter Let")
      let nm = @types.name_only(s) //???为什么name_only是正确的，而from_string就报错了
      let env = self.externals.add(s,ty)
      Let((nm,ty),to_knf(self,s1),to_knf({counter:self.counter,externals:env},s2))
    }
    LetRec({name:(nm,ty),args,body},s) => {
      //println("Enter LetRec")
      let fun_nm = @types.from_string?(nm).unwrap()
      let mut env_body = self.externals.add(nm,ty)
      let env_fun=self.externals.add(nm,ty)
      let fun_args=args.map(fn { t=> {
        env_body = env_body.add(t.0,t.1)
        let x = @types.from_string?(t.0).unwrap()
        (x,t.1)}})
      let fun_body = to_knf({counter:self.counter,externals:env_body},body)
      let after = to_knf({counter:self.counter,externals:env_fun},s)
      LetRec({name:fun_nm,ty:ty,args:fun_args,body:fun_body},after)
    }
    Tuple(arr_s) => {
      //println("Enter Tuple")
      let s0 = arr_s.copy()
      fn get_arr_nm(nm:Array[Name],s:Array[@types.Syntax]) { //这里我从尾部到头部取元组（pop）
        let ss = s.pop()
        match ss {
          None => Tuple(nm)
          Some(ss) => {
            let ty = @typing.infer(self.externals,ss).rep()
            insert_let(self,ss,ty,fn {t=>{nm.insert(0,t);get_arr_nm(nm,s)}}) //在生成对应的knf的时候，我每次都将新元素插到第一个位置，来保证最后结果的顺序是正确的
          }
        }
      }
      get_arr_nm([],s0)
    }
    LetTuple(arr_s_ty,s1,s2) => {
      //println("Enter LetTuple")
      let mut env_tuple = self.externals
      for i in arr_s_ty{
        env_tuple = env_tuple.add(i.0,i.1)
      }
      //println(env_tuple)
      let after = to_knf({counter:self.counter,externals:env_tuple},s2)
      //println(after)
      let arr_nm_ty = arr_s_ty.map(fn{t => {
        let nm = @types.name_only(t.0)
        //println(nm)
        (nm,t.1)
      }})
      //println(arr_nm_ty)
      let ty_tuple = @typing.infer(self.externals,s1).rep()
      //println("here")
      insert_let(self,s1,ty_tuple,fn {t=>LetTuple(arr_nm_ty,t,after)})//////////////
    }
    Get(s1, s2) => {
      //println("Enter Get")
      let ty_s1 = @typing.infer(self.externals,s1).rep()
      let ty_s2 = @typing.infer(self.externals,s2).rep()
      insert_let(self,s1,ty_s1,fn {x=>insert_let(self,s2,ty_s2,fn{y=>Get(x,y)})})
    }
    Put(s1, s2, s3) => {
      //println("Enter Put")
      let ty_s1 = @typing.infer(self.externals,s1).rep()
      let ty_s2 = @typing.infer(self.externals,s2).rep()
      let ty_s3 = @typing.infer(self.externals,s3).rep()
      insert_let(self,s1,ty_s1,fn{
        x=>insert_let(self,s2,ty_s2,fn{
          y=>insert_let(self,s3,ty_s3,fn{
            z=>Put(x,y,z)})})})
    }
    App(s,arr_s) => {
      //println("Enter App")
      let s0 = arr_s.copy()
      match s {
        Var(f) => {
          if @typing.extenv.contains(f) {
            //println("here")
            fn get_arr_nm(nm:Array[Name],s:Array[@types.Syntax]) { //这里我从尾部到头部取元组
              let ss = s.pop()
              match ss {
                None => ExternalFunctionApplication("minimbt_"+f,nm)
                Some(ss) => {
                  let ty = @typing.infer(self.externals,ss).rep()
                  insert_let(self,ss,ty,fn {t=>{nm.insert(0,t);get_arr_nm(nm,s)}}) //在生成对应的knf的时候，我每次都将新元素插到第一个位置，来保证最后结果的顺序是正确的
                }
              }
            }
            //println("here10")
            get_arr_nm([],s0)
          }
          else {
            //println("here")
            let ty_s = @typing.infer(self.externals,s).rep()
            insert_let(self,s,ty_s,fn { f => {
              fn get_arr_nm(nm:Array[Name],s:Array[@types.Syntax]) { //这里我从尾部到头部取元组
                let ss = s.pop()
                match ss {
                  None => Apply(f,nm)
                  Some(ss) => {
                    let ty = @typing.infer(self.externals,ss).rep()
                    insert_let(self,ss,ty,fn {t=>{nm.insert(0,t);get_arr_nm(nm,s)}}) //在生成对应的knf的时候，我每次都将新元素插到第一个位置，来保证最后结果的顺序是正确的
                  }
                }
              }
              get_arr_nm([],s0)
            }})
          }
        }
        _ => {
          let ty_s = @typing.infer(self.externals,s).rep()
          insert_let(self,s,ty_s,fn { f => {
            fn get_arr_nm(nm:Array[Name],s:Array[@types.Syntax]) { //这里我从尾部到头部取元组
              let ss = s.pop()
              match ss {
                None => Apply(f,nm)
                Some(ss) => {
                  let ty = @typing.infer(self.externals,ss).rep()
                  insert_let(self,ss,ty,fn {t=>{nm.insert(0,t);get_arr_nm(nm,s)}}) //在生成对应的knf的时候，我每次都将新元素插到第一个位置，来保证最后结果的顺序是正确的
                }
              }
            }
            get_arr_nm([],s0)
          }})
        }
      }
    }
    Array(s1,s2) => {
      //println("Enter Array")
      let ty_s1 = @typing.infer(self.externals,s1).rep()
      let ty_s2 = @typing.infer(self.externals,s2).rep()
      insert_let(self,s1,ty_s1,fn {arr => 
        insert_let(self,s2,ty_s2,fn {index => 
          match ty_s2{
            Int => ExternalFunctionApplication("minimbt_create_array",[arr,index])
            Double => ExternalFunctionApplication("minimbt_create_float_array",[arr,index])
            _ => ExternalFunctionApplication("minimbt_create_ptr_array",[arr,index])
          }
        })
      })
    }
  }
}