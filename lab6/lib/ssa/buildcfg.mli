(* L5 Compiler
 * Build Control Flow Graphs from three-address assembly procedure
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>
 *)
open Core
module ThreeAS = Threeaddrassem
module CFG = Cfg.CFG

(* Returns the CFG, the root node and the mapping of labels to bodies *)
val build_cfg
  :  ThreeAS.func
  -> print_cfg:bool (* -> int ref *)
  -> CFG.t * CFG.Node.t * (CFG.Node.t, Ssa.instr list) Hashtbl.t * CFG.Node.t list
(* val build_cfg : ThreeAS.func -> unit *)
