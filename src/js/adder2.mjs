function make_adder(x){
function adder(y){
return x+y
}
return adder
}
export default function main(){
let add2 = make_adder(2);
let add3 = make_adder(3);
globalThis.minimbt_print_int(add2(10)+add3(20))
}
