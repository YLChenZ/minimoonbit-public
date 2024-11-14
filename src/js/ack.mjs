function ack(x,y){
if (x<=0){
y+1
}
else {
if (y<=0){
ack(x-1,1)
}
else {
ack(x-1,ack(x,y-1))
}

}
return 
}
export default function main(){
globalThis.minimbt_print_int(ack(3,8))
}
