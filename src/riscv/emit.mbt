pub fn emit(
  input : Prog
) -> Array[AssemblyFunction] {
  let fun = input.funlist.map(emit_fundef)
  stackset.val = @immut/sorted_set.new()
  stackmap.val = []
  let main_body = emit_instr_rvasm(NonTail("zero"),input.body)
  let pre_size = stacksize()
  let pre = [Addi(Sp,Sp,-pre_size),
             Sd(Ra,{base:Sp,offset:(pre_size-8)}),
             Sd(Fp,{base:Sp,offset:(pre_size-16)}),
             Addi(Fp,Sp,pre_size)]
  let end :Array[RvAsm] = 
    [ Ld(Ra,{base:Sp,offset:pre_size-8}),
      Ld(Fp,{base:Sp,offset:pre_size-16}),
      Addi(Sp,Sp,pre_size),Ret]
  let main = {name:"minimbt_main",export:true,body:pre + main_body +end}
  fun + [main]
}

pub struct AssemblyFunction {
  name : String
  export : Bool
  body : Array[RvAsm]
}

pub fn AssemblyFunction::output(
  self : AssemblyFunction,
  logger : Logger
) -> Unit {
  let name = self.name
  if self.export {
    logger.write_string(".global \{name}\n")
  }
  logger.write_string("\{name}:\n")
  for asm in self.body {
    Show::output(asm, logger)
    logger.write_string("\n")
  }
}
