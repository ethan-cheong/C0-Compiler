(* L1 Compiler
 * Argument filtering. 
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Filters for function arguments that are actually used in the function body.
 *)

(** [filter_args program] returns program, but with function declarations and 
    function calls solely containing the arguments that are referenced in the 
    body of the function declaration. *)
val filter_args : Threeaddrassem.program -> Threeaddrassem.program
