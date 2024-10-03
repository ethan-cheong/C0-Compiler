(* L1 Compiler
 * Builds interference graph given list of lines from liveness analysis
 * Uses Liveness.line instead of redefining own line
 * All pre-coloured registers interfere with each other, so that should be included here?
 *)

open Core
module AS = Assem
module NodeSet = Regalloc_modules.NodeSet

val build_interference_graph : Liveness.line list -> (Node.t, NodeSet.t) Hashtbl.t
val table_to_list : (Node.t, NodeSet.t) Hashtbl.t -> string list
