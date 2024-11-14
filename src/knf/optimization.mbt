pub fn KnfEnv::opt_pass(self : KnfEnv, knf : Knf) -> Knf {
  let a_c = alpha_conversion(self,knf,@immut/hashmap.new())
  a_c
}

pub fn free_vars(knf:Knf) -> @immut/sorted_set.T[Name] {
  match knf {
    Unit | Int(_) | Double(_) | ExternalArray(_)=> @immut/sorted_set.new()
    Neg(n) | FNeg(n) | Var(n) => @immut/sorted_set.singleton(n)
    Add(l,r) | Sub(l,r) | Mul(l,r) | Div(l,r) | FAdd(l,r) |
     FSub(l,r) | FMul(l,r) | FDiv(l,r) | Get(l,r)=> @immut/sorted_set.of([l,r])
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
    LetRec({name,ty,args,body},k) => {
      let fv_body = free_vars(body) 
      let fv_k = free_vars(k)
      let argsN = args.map(fn {t=>t.0})
      let fact_fv = fv_body.diff(@immut/sorted_set.from_array(argsN))
      fv_k.union(fact_fv).diff(@immut/sorted_set.of([name]))
    }
    LetTuple(arrN2T,n,k) => {
      let arrN = arrN2T.map(fn {t=>t.0})
      free_vars(k).diff(@immut/sorted_set.from_array(arrN)).add(n)
    }
    Apply(n,arrN) => {arrN.push(n); @immut/sorted_set.from_array(arrN)}
    Tuple(arrN) | ExternalFunctionApplication(_,arrN) => @immut/sorted_set.from_array(arrN)
    Put(n1,n2,n3) => @immut/sorted_set.of([n1,n2,n3])
  }
}

fn find(k : Name,env : @immut/hashmap.T[Name,Name]) -> Name{
  match env.find(k){
    Some(n) => n
    None => k 
  }
}
pub fn alpha_conversion(self:KnfEnv,knf : Knf, env : @immut/hashmap.T[Name,Name]) -> Knf {
  match knf {
    Unit => Unit
    Int(i) => Int(i)
    Double(d) => Double(d)
    Neg(n) => Neg(find(n,env))
    FNeg(n) => FNeg(find(n,env))
    Add(l,r) => Add(find(l,env),find(r,env))
    Sub(l,r) => Sub(find(l,env),find(r,env))
    Mul(l,r) => Mul(find(l,env),find(r,env))
    Div(l,r) => Div(find(l,env),find(r,env))
    FAdd(l,r) => FAdd(find(l,env),find(r,env))
    FSub(l,r) => FSub(find(l,env),find(r,env))
    FMul(l,r) => FMul(find(l,env),find(r,env))
    FDiv(l,r) => FDiv(find(l,env),find(r,env))
    IfEq(l,r,b1,b2) => IfEq(find(l,env),find(r,env),alpha_conversion(self,b1,env),alpha_conversion(self,b2,env))
    IfLe(l,r,b1,b2) => IfLe(find(l,env),find(r,env),alpha_conversion(self,b1,env),alpha_conversion(self,b2,env))
    Let((n,t),k1,k2) => {
      let n1 = new_named_temp(self,n)
      let new_env = env.add(n,n1)
      Let((n1,t),alpha_conversion(self,k1,env),alpha_conversion(self,k2,new_env))
    }
    Var(n) => Var(find(n,env))
    LetRec({name,ty,args,body},k) => {
      let env_name = env.add(name,new_named_temp(self,name))
      let argsN = args.map(fn {t => t.0})
      let mut new_env = env_name
      for i in argsN{
        new_env = new_env.add(i,new_named_temp(self,i))
      }
      LetRec({name:find(name,env_name),
              ty : ty,
              args: args.map(fn {(n,t)=>(find(n,new_env),t)}),
              body: alpha_conversion(self,body,new_env)},
              alpha_conversion(self,k,env_name))
    }
    LetTuple(arrN2T,n,k) => {
      let arrN = arrN2T.map(fn {t=>t.0})
      let mut new_env = env
      for i in arrN{
        new_env = new_env.add(i,new_named_temp(self,i))
      }
      LetTuple(arrN2T.map(fn {(n,t)=>(find(n,new_env),t)}),find(n,env),alpha_conversion(self,k,new_env))
    }
    Apply(f,arrN) => Apply(find(f,env),arrN.map(fn{t=>find(t,env)}))
    Tuple(arrN) => Tuple(arrN.map(fn{t=>find(t,env)}))
    Get(arr,idx) => Get(find(arr,env),find(idx,env))
    Put(n1,n2,n3) => Put(find(n1,env),find(n2,env),find(n3,env))
    ExternalArray(n) => ExternalArray(n)
    ExternalFunctionApplication(s,arrN) => ExternalFunctionApplication(s,arrN.map(fn{t=>find(t,env)}))
  }
}