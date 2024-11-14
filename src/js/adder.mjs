function make_adder(x){
    function adder(y){
        return x+y
    }
        return adder
    }
export default function main(){
    minimbt_print_int(make_adder(3)(7))
}
