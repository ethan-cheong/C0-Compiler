(* L1 Compiler
 * Builds interference graph given list of lines from liveness analysis
 * Uses Liveness.line instead of redefining own line
 *)

open Core
module AS = Assem

val build_interference_graph : Liveness.line list -> (Node.t, Set.Make(Node).t) Hashtbl.t

val table_to_list
  :  ( Node.t
     , (Node.t, Set.Make(Node).Elt.comparator_witness) Set_intf.Set.t )
     Base.Hashtbl.t
  -> string list
