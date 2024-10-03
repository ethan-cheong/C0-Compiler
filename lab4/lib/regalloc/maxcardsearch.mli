(* L1 Compiler
 * Runs max cardinality search given the interference graph for simplical elimination ordering
 *)

open Core
module NodeSet = Regalloc_modules.NodeSet

val max_cardinality_search : (Node.t, NodeSet.t) Hashtbl.t -> Node.t list
