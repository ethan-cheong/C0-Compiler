(* L1 Compiler
 * Converts from assem into liveness list 
 * Parses the input in reverse
 * Follow the algorithm from recitation
 * 

 * Conducts liveness analysis by function
 *)
open Core
module AS = Assem
module NodeSet = Regalloc_modules.NodeSet

type line =
  { uses : NodeSet.t
  ; defines : NodeSet.t
  ; live_out : NodeSet.t
  ; move : bool
  ; line_number : Int32.t
  }

(* Inputs are the function itself, and a Hashtbl from function label to args *)
val liveness
  :  AS.func
  -> (string, NodeSet.t) Hashtbl.t
  -> Regalloc_modules.liveness_tables
  -> timestamps:Timestamp.t
  -> line list

val string_of_node_lst : line list -> string
