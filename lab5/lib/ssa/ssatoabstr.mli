(* L5 Compiler
 * Convert SSA procedure to 3-addr abstr assem procedure. 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Algorithms adapted from Chapter 19 of Modern Compiler Implementation (Appel)
 *)
module ThreeAS = Threeaddrassem
module CFG = Cfg.CFG
open Core

(* Takes the CFG, root node and mapping from labels to func bodies. *)
val ssa_to_abstr
  :  CFG.t * CFG.Node.t * (CFG.Node.t, Ssa.instr list) Hashtbl.t * CFG.Node.t list
  -> print_cfg:bool
  -> ThreeAS.instr list (* change this to ThreeAS.func when complete *)
