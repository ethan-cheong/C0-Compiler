(* Rebuild the CFG after constant propagation *)
open Core
module ThreeAS = Threeaddrassem
module Dominator = Cfg.Dominator
module CFG = Cfg.CFG
module Dot = Cfg.Dot
module Node = CFG.Node
module Bfs = Cfg.Bfs
module VarTable = Type_modules.SSAVarTable
module IdSet = Set.Make (Int)
module VarSet = Type_modules.SSAVarSet
module LabelSet = Set.Make (String)

let id_to_instr = Hashtbl.create (module Int)
let label_to_ids = Hashtbl.create (module Node)
let id_to_label = Hashtbl.create (module Int)

let rec build_graph cfg orig curr_node seen_nodes =
  match Hashtbl.find seen_nodes curr_node with
  | Some _ -> ()
  | None ->
    Hashtbl.set seen_nodes ~key:curr_node ~data:true;
    CFG.add_vertex cfg curr_node;
    CFG.iter_succ
      (fun succ ->
        CFG.add_edge cfg curr_node succ;
        build_graph cfg orig succ seen_nodes)
      orig
      curr_node
;;

let only_accessible cfg root label_to_body =
  (* Printf.printf "\ngraph after renaming\n";
  print_label_to_body label_to_body; *)
  let cfg_filtered = CFG.create () in
  let seen_nodes =
    Hashtbl.create
      ~growth_allowed:false
      ~size:(Hashtbl.length label_to_body)
      (module String)
  in
  build_graph cfg_filtered cfg root seen_nodes;
  let filtered_labels =
    Hashtbl.filter_keys label_to_body ~f:(fun key -> CFG.mem_vertex cfg_filtered key)
  in
  cfg_filtered, root, filtered_labels
;;

let new_phi_args args indexes =
  List.filteri args ~f:(fun ind _ -> not (IdSet.mem indexes ind))
;;

let update_label_to_body label label_to_body indexes =
  Hashtbl.update label_to_body label ~f:(fun body_opt ->
    match body_opt with
    | None -> failwith "why none?"
    | Some body ->
      List.map body ~f:(fun instr ->
        match instr with
        | Ssa.Phi { args; dest } -> Ssa.Phi { args = new_phi_args args indexes; dest }
        | _ -> instr))
;;

(* If i use this function, 
  I need to remove the unused labels from the phi functions
  The unused phi are obtained from using cfg_orig and cfg
  For each node, get the predecessors. 
  If precessors are not equal, find all predecessors that do not exist in cfg
  Remove all of those predecessors from the phi function
*)

let rebuild_cfg (cfg_orig, root_orig, label_to_body, labels_in_order) =
  (* Dot.output_graph
    (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_cfg_orig.txt" root_orig))
    cfg_orig; *)
  Hashtbl.clear id_to_instr;
  Hashtbl.clear label_to_ids;
  Hashtbl.clear id_to_label;
  let counter = ref 0 in
  Hashtbl.iteri label_to_body ~f:(fun ~key:label ~data:instrs ->
    let instr_ids =
      List.fold_left instrs ~init:[] ~f:(fun acc instr ->
        counter := !counter + 1;
        Hashtbl.set id_to_instr ~key:!counter ~data:instr;
        Hashtbl.set id_to_label ~key:!counter ~data:label;
        !counter :: acc)
    in
    Hashtbl.set label_to_ids ~key:label ~data:instr_ids);
  let cfg, root, label_to_body = only_accessible cfg_orig root_orig label_to_body in
  CFG.iter_vertex
    (fun vertex ->
      let new_preds_set = LabelSet.of_list (CFG.pred cfg vertex) in
      let old_preds = CFG.pred cfg_orig vertex in
      let indexes =
        List.foldi old_preds ~init:IdSet.empty ~f:(fun ind acc curr_pred ->
          if LabelSet.mem new_preds_set curr_pred then acc else IdSet.add acc ind)
      in
      update_label_to_body vertex label_to_body indexes)
    cfg;
  let labels_in_order =
    List.filter labels_in_order ~f:(fun label -> Hashtbl.mem label_to_body label)
  in
  (* Printf.printf "\ngraph after reconstructing\n";
  Abstrtossa.print_label_to_body label_to_body;
  Dot.output_graph
    (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_cfg.txt" root_orig))
    cfg; *)
  cfg, root, label_to_body, labels_in_order
;;
