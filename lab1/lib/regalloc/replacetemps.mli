(* L1 Compiler
 * Given a mapping from temps to registers from greedy colouring and a list of 
 * abstract assembly instructions, returns the list with temps replaced with 
 * the corresponding register from the list.
 *)
open Core

val replace_temps : Assem.instr list -> (Node.t, Node.t) Hashtbl.t -> Assem.instr list
