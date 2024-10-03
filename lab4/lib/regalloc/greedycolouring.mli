(* L1 Compiler
 * Greedily colours the interference graph given an ordering of nodes and a graph
 *)
open Core
module NodeSet = Regalloc_modules.NodeSet

val greedy_colouring
  :  ?debug:bool
  -> (Node.t, NodeSet.t) Hashtbl.t
  -> Node.t list (* -> Assem.operand list *)
  -> (Node.t, Node.t) Hashtbl.t
