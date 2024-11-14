pub enum Syntax {
  Unit
  Bool(Bool) // true false
  Int(Int) // int
  Double(Double) // double
  Var(String) // _
  Tuple(Array[Syntax]) // (_, _, _)
  Not(Syntax) // not(_)  
  Array(Syntax, Syntax) // Array::make(n, e)  [e,e,..,e] n个
  Neg(Syntax, mut ~kind : Kind?) // -_  -2
  App(Syntax, Array[Syntax]) // _(_, _, _) or _()
  Get(Syntax, Syntax) // _[_]   arr[i]
  If(Syntax, Syntax, Syntax) // if _ { _ } else { _ }
  Prim(Syntax, Syntax, Op, mut ~kind : Kind?) // _ + - * / _   1+2    1*3
  Eq(Syntax, Syntax) // _==_  
  LE(Syntax, Syntax) // _<=_
  Let((String, Type), Syntax, Syntax) // let _: _ = _; _   let x : Int = 3;syntax
  LetRec(Fundef, Syntax) // fn f() {} ; _
  LetTuple(Array[(String, Type)], Syntax, Syntax) // let (_ , _) : (_, _)= _; _   let (x,y,z) : (Int,Int,Int) = (1,2,3);Syntax
  Put(Syntax, Syntax, Syntax) // _[_] = _    arr[i] = 3  // let "" : Unit = arr[i] = 3; stmt
} derive(Show)

//make_adder(x){fn adder(y) {x+y};{adder;x;y} }
//11.11
//Array::make(n,e) 
pub enum Kind {
  Int
  Double
} derive(Show, Eq)

pub enum Op {
  Add
  Sub
  Mul
  Div
} derive(Show, Eq)

pub struct Fundef {  //fn add(x,y) -> Int { x+y }  (Int,Int) -> Int
  name : (String, Type)
  args : Array[(String, Type)]
  body : Syntax
} derive(Show)

pub enum Type {
  Unit
  Bool
  Int
  Double
  Fun(Array[Type], Type) // (_, _, _) -> _
  Tuple(Array[Type]) // (_, _, _)
  Array(Type) // Array[_]
  Var(Ref[Type?])
  Ptr
} derive(Show)

pub fn Type::is_ptr_like(self : Type) -> Bool {
  match self {
    Fun(_) | Tuple(_) | Array(_) | Ptr => true
    Var(t) =>
      match t.val {
        Some(t) => t.is_ptr_like()
        None => false
      }
    _ => false
  }
}

pub fn type2kind(self:Type) -> Kind{
  match self {
    Int => Int
    Double => Double
    _ => panic()
  }
}
pub fn Type::rep(self : Type) -> Type{  //Var({val : Some(Int)}) => Int
  match self {
    Var(t) => {
      match t.val {
        Some(ty) => {
          let actualType = ty.rep()
          t.val = Some(actualType)
          actualType
        }
        None => self
      }
    }
    Fun(argt,rett) => Fun(argt.map(fn{t=>t.rep()}),rett.rep())
    Tuple(arr_ty) => Tuple(arr_ty.map(fn{t=>t.rep()}))
    Array(ty) => Array(ty.rep())
    ty => ty
  }
}
pub fn Type::is_float_like(self : Type) -> Bool {
  match self {
    Double => true
    Var(t) =>
      match t.val {
        Some(t) => t.is_float_like()
        None => false
      }
    _ => false
  }
}

pub fn Type::size_of(self : Type, size_of_ptr : Int) -> Int {
  match self {
    Unit => 0
    Bool => 4
    Int => 4
    Double => 8
    Tuple(_) | Fun(_, _) | Array(_) | Ptr => size_of_ptr
    Var(t) =>
      match t.val {
        Some(t) => t.size_of(size_of_ptr)
        None => @util.die("Uninstantiated type variable")
      }
  }
}

pub fn Type::op_equal(self : Type, other : Type) -> Bool {  // Int =? Int
  match (self, other) {
    (Unit, Unit) => true
    (Bool, Bool) => true
    (Int, Int) => true
    (Double, Double) => true
    (Fun(xs, x), Fun(ys, y)) => xs == ys && x == y
    (Tuple(xs), Tuple(ys)) => xs == ys
    (Array(x), Array(y)) => x == y
    (Ptr, Ptr) => true
    (Var(x), Var(y)) => x.val == y.val
    _ => false
  }
}
