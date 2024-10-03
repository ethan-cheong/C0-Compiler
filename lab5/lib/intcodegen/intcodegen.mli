(* L1 Compiler
 * Assembly Code Generator for Three Address assembly
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Implements a "convenient munch" algorithm
 *)

val int_code_gen : Tree.program -> Threeaddrassem.program
