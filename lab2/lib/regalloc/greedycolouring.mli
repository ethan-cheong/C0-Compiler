(* L1 Compiler
 * Greedily colours the interference graph given an ordering of nodes and a graph
 *)
open Core

val greedy_colouring
  :  ?debug:bool
  -> (Node.t, Nodeset.NodeSet.t) Hashtbl.t
  -> Node.t list
  -> (Node.t, Node.t) Hashtbl.t
