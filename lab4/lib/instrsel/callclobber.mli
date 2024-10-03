(* L1 Compiler
 * Instruction Selection.
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Returns the function's arguments that are NOT call clobbered.
 *)

(** [non_call_clobbered_args args body] is a Hashtbl that maps all non-call-
    clobbered arguments to their arg position. *)
val non_call_clobbered_args
  :  Threeaddrassem.operand list
  -> Threeaddrassem.body
  -> (Temp.t, int) Base.Hashtbl.t
