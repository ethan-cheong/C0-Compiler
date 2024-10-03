(* L5 Compiler
 * Build Control Flow Graph from three-address assembly program
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>
 *)

open Core
module ThreeAS = Threeaddrassem
module CFG = Cfg.CFG
module Dot = Cfg.Dot
module Node = CFG.Node

(** [split_edges cfg label_to_bodies] returns [cfg] but with no control-flow edges that lead 
    from a node with multiple successors to a node with multiple predecessors. It also updates
    all bodies in [label_to_bodies]. *)
(* let split_edges (cfg : CFG.t) label_to_bodies counter =
  let copy = CFG.copy cfg in
  CFG.iter_edges
    (fun a b ->
      if CFG.succ cfg a |> List.length > 1 && CFG.pred cfg b |> List.length > 1
      then (
        let split_label = Printf.sprintf "split_%d" !counter in
        Hashtbl.set label_to_bodies ~key:split_label ~data:[ Ssa.Jump b ];
        (* Modify a. *)
        let new_body =
          match Hashtbl.find_exn label_to_bodies a |> List.rev with
          | Ssa.If { lt; lf; lhs; rhs; condition } :: tl when String.(lt = b) ->
            Ssa.If { lt = split_label; lf; lhs; rhs; condition } :: tl |> List.rev
          | Ssa.If { lt; lf; lhs; rhs; condition } :: tl when String.(lf = b) ->
            Ssa.If { lt; lf = split_label; lhs; rhs; condition } :: tl |> List.rev
          | Ssa.Jump _ :: tl -> Ssa.Jump split_label :: tl |> List.rev
          | _ -> failwith "Inconsistency in cfg and edge representation"
        in
        Hashtbl.set label_to_bodies ~key:a ~data:new_body;
        incr counter;
        CFG.remove_edge copy a b;
        CFG.add_edge copy a split_label;
        CFG.add_edge copy split_label b))
    cfg;
  copy
;; *)

(** Build the control flow graph of [func]. Requires that [func] is in basic 
    block structure; each block starts with a label, and must contain a jump/
    return/if/mem_exn which marks the end of that block. Code after that and 
    until the next label is ignored. *)
let build_cfg (func : ThreeAS.func) ~print_cfg:_ =
  let func_name = (fst func).ident in
  let func_body = snd func in
  let graph = CFG.create () in
  (* At least add the root node so that procedures with no control flow work *)
  CFG.add_vertex graph func_name;
  (* If junk is true, it means we are looking at code that will never be run 
     because it is in between a ret/jmp/if/raise_exn and the end of the basic
      block. So we omit it from the program. *)
  let junk = ref false in
  (* curr_label is the current label being looked at *)
  let curr_label = ref func_name in
  (* curr_acc contains the function body of the current block*)
  let curr_acc = ref [] in
  let labels_in_order = ref [ func_name ] in
  (* Map all nodes to the assembly they contain *)
  let label_to_body = Hashtbl.create ~growth_allowed:true ~size:64 (module String) in
  List.iter func_body ~f:(fun instr ->
    match instr with
    | ThreeAS.Label s ->
      junk := false;
      curr_label := s;
      labels_in_order := !curr_label :: !labels_in_order;
      CFG.add_vertex graph s
    | ThreeAS.If { lt; lf; _ } when not !junk ->
      Hashtbl.set
        label_to_body
        ~key:!curr_label
        ~data:(List.rev (ThreeAS.instr_to_ssa instr :: !curr_acc));
      curr_acc := [];
      CFG.add_edge graph !curr_label lt;
      CFG.add_edge graph !curr_label lf;
      junk := true
    | ThreeAS.Jump l when not !junk ->
      Hashtbl.set
        label_to_body
        ~key:!curr_label
        ~data:(List.rev (ThreeAS.instr_to_ssa instr :: !curr_acc));
      curr_acc := [];
      CFG.add_edge graph !curr_label l;
      junk := true
    | Ret _ when not !junk ->
      Hashtbl.set
        label_to_body
        ~key:!curr_label
        ~data:(List.rev (ThreeAS.instr_to_ssa instr :: !curr_acc));
      curr_acc := [];
      junk := true
    | Ret_void when not !junk ->
      Hashtbl.set
        label_to_body
        ~key:!curr_label
        ~data:(List.rev (ThreeAS.instr_to_ssa instr :: !curr_acc));
      curr_acc := [];
      junk := true
    | CallF { ident = "raise"; _ } when not !junk ->
      Hashtbl.set
        label_to_body
        ~key:!curr_label
        ~data:(List.rev (ThreeAS.instr_to_ssa instr :: !curr_acc));
      curr_acc := [];
      junk := true
    | _ when not !junk -> curr_acc := ThreeAS.instr_to_ssa instr :: !curr_acc
    | _ -> ());
  if not !junk then Hashtbl.set label_to_body ~key:!curr_label ~data:(List.rev !curr_acc);
  (* Print out all nodes of the graph`*)
  (* Add this as a helper function lol otherwise it will always output the graph *)
  (* let split_edges_graph = split_edges graph label_to_body counter in
  if print_cfg
  then
    Dot.output_graph
      (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_split.txt" func_name))
      split_edges_graph; *)
  (* if print_cfg
  then
    Dot.output_graph
      (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_unsplit.txt" func_name))
      graph;
  if print_cfg
  then (
    Printf.printf "labels in order:\n";
    List.iter !labels_in_order ~f:(fun x -> Printf.printf "%s\n" x)); *)
  graph, func_name, label_to_body, !labels_in_order
;;
