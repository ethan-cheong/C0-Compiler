(* L1 Compiler
 * Converts temps to refs on the stack 
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

(** Spill any temps to the stack, and replace them with references to the stack 
    with the corresponding stack offset. Expand function calls. *)
val stack_spill : Assem.func list -> only_main:bool -> Assem.func list
