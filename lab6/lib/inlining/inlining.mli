(* L5 Compiler
 * Function Inlining
 * Author: Ethan Cheong, Wu Meng Hui
 *
 * Based on 15411 Lecture Notes.
 *)
module ThreeAS = Threeaddrassem

val inline_functions : ThreeAS.func list -> _inline_threshold:int -> ThreeAS.func list
