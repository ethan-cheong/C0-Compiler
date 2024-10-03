open Core
module ThreeAS = Threeaddrassem
module Dominator = Cfg.Dominator
module CFG = Cfg.CFG
module Dot = Cfg.Dot
module Node = CFG.Node
module Bfs = Cfg.Bfs
module VarTable = Type_modules.SSAVarTable
module IdSet = Set.Make (Int)

(* Not sure if necessary, work on it after sccp *)
let clean_ssa (cfg_orig, root_orig, new_label_to_bodies, labels_in_order) =
  (* Keep the cfg with only the new labels to bodies, filter the labels in order *)
  failwith "unimplemented"
;;
