(* L1 Compiler
 * Greedily colours the interference graph given an ordering of nodes and a graph
 *)
open Core
module NodeSet = Regalloc_modules.NodeSet

(* Returns the coloured table *)
val greedy_colouring
  :  ?debug:bool
  -> (Node.t, NodeSet.t) Hashtbl.t
  -> Node.t list (* -> Assem.operand list *)
  -> (Node.t, Node.t) Hashtbl.t

(* Takes coloured table, liveness line, and adj_list to return new coloured_table *)
val coalesce
  :  (Node.t, Node.t) Hashtbl.t
  -> (Node.t, NodeSet.t) Hashtbl.t
  -> Liveness.line list
  -> (Node.t, Node.t) Hashtbl.t
