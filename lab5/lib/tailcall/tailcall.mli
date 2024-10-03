(* L5 Compiler
 * Tail Call Optimization
 * Author: Ethan Cheong, Wu Meng Hui
 *
 * Based on 15411 Lecture Notes.
 *)
module ThreeAS = Threeaddrassem

val tail_call_optimization : ThreeAS.func list -> ThreeAS.func list
