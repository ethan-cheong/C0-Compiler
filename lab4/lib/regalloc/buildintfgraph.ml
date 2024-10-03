(* L1 Compiler
 * Builds interference graph given list of lines from liveness analysis
 * Goes through each line
 * Given defs and liveouts, adds defs to adjlist for all liveout and liveout to adjlist for def
 * Time for ass-cancer. Now that there are multiple defs, need to add defs to everything
 *)

open Core
module AS = Assem
module NodeSet = Regalloc_modules.NodeSet
module Int32Table = Type_modules.Int32Table

(* Adds data to table, overwriting if necessary *)
(* let update_graph ~graph ~def =
  match Hashtbl.update table ~key ~data with
  | `Duplicate ->
    let (_ : unit) = Hashtbl.set table ~key ~data in
    false
  | `Ok -> true
;; *)

(* Adds def to adjlists of all liveouts *)
let add_def_to_liveout ~(defs : NodeSet.t) ~(liveouts : NodeSet.t) graph =
  NodeSet.iter liveouts ~f:(fun liveout ->
    Hashtbl.update graph liveout ~f:(fun curr_defs ->
      match curr_defs with
      | None -> defs
      | Some x -> NodeSet.union x defs))
;;

(* Adds liveouts to adjlist of def *)
let add_liveout_to_def ~(defs : NodeSet.t) ~(liveouts : NodeSet.t) graph =
  NodeSet.iter defs ~f:(fun def ->
    Hashtbl.update graph def ~f:(fun curr_liveouts ->
      match curr_liveouts with
      | None -> liveouts
      | Some x -> NodeSet.union x liveouts))
;;

(* Extract and assert only one variable defined per line *)

let remove_key_from_values tbl =
  Hashtbl.mapi tbl ~f:(fun ~key ~data -> NodeSet.remove data key)
;;

(* All precolored registers implicitly interfere with each other, implies all registers should interfere with each other? *)
let initialise_interference ~tbl =
  let reg_list =
    List.map
      Assem.[ AX; BX; CX; DX; SI; DI; BP; R8; R9; R11; R12; R13; R14; R15; R10; SP ]
      ~f:(fun x -> Node.node_of_operand (Assem.Reg { reg = x; size = DOUBLE }))
  in
  let regs_nodeset = NodeSet.of_list reg_list in
  add_liveout_to_def ~defs:regs_nodeset ~liveouts:regs_nodeset tbl
;;

(* Builds interference graph with keys in adjlist *)
let build_graph_with_keys (lst : Liveness.line list) : (Node.t, NodeSet.t) Hashtbl.t =
  let tbl = Hashtbl.create ~growth_allowed:true ~size:500 (module Node) in
  let (_ : unit) = initialise_interference ~tbl in
  let rec helper (lst : Liveness.line list) tbl =
    match lst with
    | [] -> tbl
    | hd :: t ->
      let defs = hd.defines in
      let liveouts = hd.live_out in
      if NodeSet.length defs <> 0 && NodeSet.length liveouts <> 0
      then (
        let (_ : unit) = add_liveout_to_def ~defs ~liveouts tbl in
        let (_ : unit) = add_def_to_liveout ~defs ~liveouts tbl in
        helper t tbl)
      else helper t tbl
    (* Since no need to add nodes*)
  in
  helper lst tbl
;;

let build_interference_graph (lst : Liveness.line list) : (Node.t, NodeSet.t) Hashtbl.t =
  let tbl = build_graph_with_keys lst in
  remove_key_from_values tbl
;;

(* Formats nodes *)

let format_node_set node_set =
  "["
  ^ String.concat ~sep:", " (List.map ~f:Node.format_node (NodeSet.to_list node_set))
  ^ "]"
;;

(* Formats adjlist into list for output testing *)
let table_to_list tbl =
  Hashtbl.fold tbl ~init:[] ~f:(fun ~key ~data acc ->
    (Node.format_node key ^ ": " ^ format_node_set data) :: acc)
;;

let table_to_graph tbl filename =
  Out_channel.with_file filename ~f:(fun out ->
    Out_channel.fprintf out "graph G {\n\n";
    Hashtbl.iteri tbl ~f:(fun ~key ~data ->
      let key_str =
        String.substr_replace_all ~pattern:"%" ~with_:"" (Node.format_node key)
      in
      NodeSet.iter data ~f:(fun other_node ->
        let node_str =
          String.substr_replace_all ~pattern:"%" ~with_:"" (Node.format_node other_node)
        in
        Out_channel.fprintf out "%s -- %s\n" key_str node_str));
    Out_channel.fprintf
      out
      "\n\
       ax [shape=Mdiamond];\n\
       bx [shape=Mdiamond];\n\
       cx [shape=Mdiamond];\n\
       dx [shape=Mdiamond];\n\
       sp [shape=Mdiamond];\n\
       bp [shape=Mdiamond];\n\
       si [shape=Mdiamond];\n\
       di [shape=Mdiamond];\n\
       r8 [shape=Mdiamond];\n\
       r9 [shape=Mdiamond];\n\
       r10 [shape=Mdiamond];\n\
       r11 [shape=Mdiamond];\n\
       r12 [shape=Mdiamond];\n\
       r13 [shape=Mdiamond];\n\
       r14 [shape=Mdiamond];\n\
       r15 [shape=Mdiamond];\n\
       }")
;;
