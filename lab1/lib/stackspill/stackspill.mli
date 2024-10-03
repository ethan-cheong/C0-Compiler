(* L1 Compiler
 * Converts temps to refs on the stack 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 *)

(** Spill any temps to the stack, and replace them with references to the stack 
    with the corresponding stack offset. *)
val stack_spill : Assem.instr list -> Assem.instr list
