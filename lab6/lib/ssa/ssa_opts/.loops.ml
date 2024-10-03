(* L5 Compiler
 * Loop-based optimizations
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Algorithms adapted from LLVM loop terminology
 *)

open Core
module CFG = Cfg.CFG
module Dominator = Cfg.Dominator

let loop_next_tree cfg root =
  let idom = Dominator.compute_idom cfg root in
  let dom_tree = Dominator.idom_to_dom_tree cfg idom in
  let dominators = Dominator.idom_to_dominators idom in
  CFG.iter_edges
    (fun n h ->
      (* Check if h dominates n *)
      let n_dominators = Dominator.S.of_list (dominators n) in
      if Dominator.S.mem h n_dominators then ( (* Consider the nodes that h dominates *) ))
    cfg
;;
