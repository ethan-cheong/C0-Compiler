(* L5 Compiler
 * Convert 3AS procedure to SSA procedure. 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Algorithms adapted from Chapter 19 of Modern Compiler Implementation (Appel)
 *)
open Core
module CFG = Cfg.CFG
module ThreeAS = Threeaddrassem

(* Returns the CFG, root node, and a mapping from labels to function bodies. *)
val abstr_to_ssa
  :  ThreeAS.func
  -> print_cfg:bool (* -> int ref *)
  -> CFG.t * CFG.Node.t * (CFG.Node.t, Ssa.instr list) Hashtbl.t * CFG.Node.t list

val print_label_to_body : (string, Ssa.instr list) Hashtbl.t -> unit
