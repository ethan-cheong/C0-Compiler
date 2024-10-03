(* L1 Compiler
 * Runs max cardinality search given the interference graph for simplical elimination ordering
 *)

open Core

val max_cardinality_search : (Node.t, Set.Make(Node).t) Hashtbl.t -> Node.t list
