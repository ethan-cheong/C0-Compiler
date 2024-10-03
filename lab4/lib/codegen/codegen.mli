(* L1 Compiler
 * Assembly Code Generator for final representation of assembly 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Currently converts naively without register allocation
 *)

(* As of now, this converts mov instructions. *)
val code_gen : Assem.func list -> Assem.func list
