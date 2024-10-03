(* L5 Compiler
 * Remove Nops, replace jumps with fall-through
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 *)

module ThreeAS = Threeaddrassem

val cleanup : ThreeAS.func -> ThreeAS.func
