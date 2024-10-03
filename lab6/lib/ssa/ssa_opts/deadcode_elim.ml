(* L5 Compiler
 * Deadcode Elimination
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>
 * Adapted from Engineering a Compiler (Cooper and Torczon, 2011).
 *)
open Core
module ThreeAS = Threeaddrassem
module Dominator = Cfg.Dominator
module CFG = Cfg.CFG
module Dot = Cfg.Dot
module Node = CFG.Node
module Bfs = Cfg.Bfs
module VarTable = Type_modules.SSAVarTable
module IdSet = Set.Make (Int)

let rec has_return (instrs : Ssa.instr list) : bool =
  match instrs with
  | [] -> false
  | h :: t ->
    (match h with
     | Ret _ | Ret_void -> true
     | _ -> has_return t)
;;

(* Make a copy of the CFG, along with the exit_node and entry_node *)
let copy_cfg
  (cfg_orig : CFG.t)
  (root_orig : CFG.Node.t)
  (label_to_bodies : (CFG.Node.t, Ssa.instr list) Hashtbl.t)
  : CFG.t * CFG.Node.t * CFG.Node.t * (CFG.Node.t, Ssa.instr list) Hashtbl.t
  =
  let cfg = CFG.create () in
  CFG.iter_edges (fun vert1 vert2 -> CFG.add_edge cfg vert1 vert2) cfg_orig;
  (* Todo: add an exit node *)
  let exit_node = "exit_node" in
  let entry_node = "entry_node" in
  CFG.add_vertex cfg exit_node;
  CFG.add_vertex cfg entry_node;
  Hashtbl.iteri label_to_bodies ~f:(fun ~key ~data ->
    if has_return data then CFG.add_edge cfg key exit_node);
  CFG.add_edge cfg entry_node root_orig;
  CFG.add_edge cfg entry_node exit_node;
  let new_label_to_bodies = Hashtbl.copy label_to_bodies in
  Hashtbl.set new_label_to_bodies ~key:exit_node ~data:[ Ssa.Nop ];
  Hashtbl.set new_label_to_bodies ~key:entry_node ~data:[ Ssa.Nop ];
  cfg, exit_node, entry_node, new_label_to_bodies
;;

let reverse_cfg cfg_modified =
  let cfg_rev = CFG.create () in
  CFG.iter_edges (fun vert1 vert2 -> CFG.add_edge cfg_rev vert2 vert1) cfg_modified;
  cfg_rev
;;

let create_cdg
  ((cfg_orig, root_orig, label_to_bodies) :
    CFG.t * CFG.Node.t * (CFG.Node.t, Ssa.instr list) Hashtbl.t)
  : CFG.t * CFG.Node.t * (CFG.Node.t, Ssa.instr list) Hashtbl.t
  =
  (* Root is the exit node *)
  let cfg, exit_node, _, new_label_to_bodies =
    copy_cfg cfg_orig root_orig label_to_bodies
  in
  let cfg_reversed = reverse_cfg cfg in
  let idom = Dominator.compute_idom cfg_reversed exit_node in
  let dom_tree = Dominator.idom_to_dom_tree cfg_reversed idom in
  let dom_frontier = Dominator.compute_dom_frontier cfg_reversed dom_tree idom in
  let cdg_graph = CFG.create () in
  CFG.iter_vertex
    (fun y ->
      let vert_frontier = dom_frontier y in
      List.iter vert_frontier ~f:(fun x -> CFG.add_edge cdg_graph y x))
    cfg_reversed;
  cdg_graph, exit_node, new_label_to_bodies
;;

(* 
  A statement is live if:
  1. Performs I/O, store, returns, calls function
  2. Defines a variable that is used in a live statement
  3. Is a conditional branch upon which some other live statement is control-dependent*

  For conditional branch, 

  1: straightforward
  2: Track all the variables in a hashtable. If they are used in a live statement, mark as true
  3': Track all nodes in a hashtable (empty by default). Any live statements should be added into the node table
  3: When an if/else block is encountered, if it goes to a node with a live statement, then mark that statement as live
*)

let initialise_tables cdg_graph =
  let var_table = VarTable.create ~growth_allowed:true () in
  let node_table = Hashtbl.create ~growth_allowed:true (module Node) in
  CFG.iter_vertex
    (fun vert -> Hashtbl.set node_table ~key:vert ~data:(false, []))
    cdg_graph;
  var_table, node_table
;;

let var_is_live variable var_table =
  match VarTable.find var_table variable with
  | None -> false
  | Some x -> x
;;

let label_is_live label node_table =
  match Hashtbl.find node_table label with
  | None -> false
  | Some (live, _) -> live
;;

let preprocess_instr
  instr
  (var_to_instr : int VarTable.t)
  (instr_to_mark : (int, bool) Hashtbl.t)
  initial_worklist
  counter
  =
  Ssa.(
    match instr with
    | Comment _ | Directive _ | Nop | Label _ ->
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None -> false
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Binop { dest; op; _ } ->
      VarTable.update var_to_instr dest ~f:(fun curr ->
        match curr with
        | None -> !counter
        | Some _ ->
          failwith (sprintf "%s should only be defined once" (Ssa.format_operand dest)));
      (match op with
       | Div | Mod | Sal | Sar | Shr ->
         Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
           match curr with
           | None ->
             initial_worklist := IdSet.add !initial_worklist !counter;
             true
           | Some _ ->
             failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
       | _ ->
         Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
           match curr with
           | None -> false
           | Some _ ->
             failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr))))
    | Mov { dest; _ } | Movsx { dest; _ } | Movzx { dest; _ } | Mov_trunc { dest; _ } ->
      VarTable.update var_to_instr dest ~f:(fun curr ->
        match curr with
        | None -> !counter
        | Some _ ->
          failwith (sprintf "%s should only be defined once" (Ssa.format_operand dest)));
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None -> false
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | If _ ->
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None -> false
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Jump _ ->
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None ->
          initial_worklist := IdSet.add !initial_worklist !counter;
          true
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Cmp _ -> failwith "when will i see a cmp????"
    | CallF { dest; _ } ->
      VarTable.update var_to_instr dest ~f:(fun curr ->
        match curr with
        | None -> !counter
        | Some _ ->
          failwith (sprintf "%s should only be defined once" (Ssa.format_operand dest)));
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None ->
          initial_worklist := IdSet.add !initial_worklist !counter;
          true
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Ret _ | Ret_void ->
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None ->
          initial_worklist := IdSet.add !initial_worklist !counter;
          true
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Store _ ->
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None ->
          initial_worklist := IdSet.add !initial_worklist !counter;
          true
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Load { dest; _ } ->
      VarTable.update var_to_instr dest ~f:(fun curr ->
        match curr with
        | None -> !counter
        | Some _ ->
          failwith (sprintf "%s should only be defined once" (Ssa.format_operand dest)));
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None ->
          initial_worklist := IdSet.add !initial_worklist !counter;
          true
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Lea { dest; _ } ->
      VarTable.update var_to_instr dest ~f:(fun curr ->
        match curr with
        | None -> !counter
        | Some _ ->
          failwith (sprintf "%s should only be defined once" (Ssa.format_operand dest)));
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None ->
          initial_worklist := IdSet.add !initial_worklist !counter;
          true
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr)))
    | Phi { dest; _ } ->
      VarTable.update var_to_instr dest ~f:(fun curr ->
        match curr with
        | None -> !counter
        | Some _ ->
          failwith (sprintf "%s should only be defined once" (Ssa.format_operand dest)));
      Hashtbl.update instr_to_mark !counter ~f:(fun curr ->
        match curr with
        | None -> false
        | Some _ ->
          failwith (sprintf "there should only be 1 instr %s" (Ssa.format_instr instr))))
;;

let is_temp =
  Ssa.(
    function
    | Temp _ -> true
    | _ -> false)
;;

(* Find and mark where the variable is defined *)
let find_mark_def var var_to_instr id_to_mark worklist =
  let instr_id_opt = VarTable.find var_to_instr var in
  match instr_id_opt with
  | None -> () (* WARNING: happens for ../tests/l2-basic/return23.l2 *)
  | Some instr_id ->
    Hashtbl.update id_to_mark instr_id ~f:(fun x ->
      match x with
      | None -> failwith "x must be marked"
      | Some y ->
        if not y
        then (
          worklist := IdSet.add !worklist instr_id;
          true)
        else y)
;;

(* We know that these instructions are critical *)
let process_instruction
  instruction
  curr_id
  var_to_instr
  id_to_mark
  worklist
  node_to_branch
  id_to_node
  cdg_graph
  =
  let instr_label = Hashtbl.find_exn id_to_node curr_id in
  Ssa.(
    match instruction with
    | Comment _ | Directive _ | Nop | Label _ -> failwith "instruction should not pop up"
    | Cmp _ -> failwith "process instruction compare??"
    | Binop { lhs; rhs; _ } ->
      if is_temp lhs then find_mark_def lhs var_to_instr id_to_mark worklist;
      if is_temp rhs then find_mark_def rhs var_to_instr id_to_mark worklist
    | Mov { src; _ } | Movsx { src; _ } | Movzx { src; _ } | Mov_trunc { src; _ } ->
      if is_temp src then find_mark_def src var_to_instr id_to_mark worklist
    (* The lt and lf for if statements don't matter *)
    | If { lhs; rhs; _ } ->
      if is_temp lhs then find_mark_def lhs var_to_instr id_to_mark worklist;
      if is_temp rhs
      then
        find_mark_def rhs var_to_instr id_to_mark worklist
        (* Jumps and labels dont rely on anything, so just skip it *)
    | Jump _ -> ()
    | Ret { src } ->
      if is_temp src then find_mark_def src var_to_instr id_to_mark worklist
    (* Ret voids dont rely on anything either *)
    | Ret_void -> ()
    | CallF { args; _ } ->
      List.iter args ~f:(fun arg ->
        if is_temp arg then find_mark_def arg var_to_instr id_to_mark worklist)
    | Store { base; index; src; _ } ->
      if is_temp base then find_mark_def base var_to_instr id_to_mark worklist;
      if is_temp index then find_mark_def index var_to_instr id_to_mark worklist;
      if is_temp src then find_mark_def src var_to_instr id_to_mark worklist
    | Load { base; index; _ } ->
      if is_temp base then find_mark_def base var_to_instr id_to_mark worklist;
      if is_temp index then find_mark_def index var_to_instr id_to_mark worklist
    | Lea { base; index; _ } ->
      if is_temp base then find_mark_def base var_to_instr id_to_mark worklist;
      if is_temp index then find_mark_def index var_to_instr id_to_mark worklist
    | Phi { args; _ } ->
      List.iter args ~f:(fun arg ->
        if is_temp arg then find_mark_def arg var_to_instr id_to_mark worklist));
  CFG.iter_succ
    (fun b ->
      match Hashtbl.find node_to_branch b with
      | None ->
        () (* failwith (sprintf "why successor has no branch? %s %s\n" b instr_label) *)
      | Some branch ->
        Hashtbl.update id_to_mark branch ~f:(fun x ->
          match x with
          | None -> failwith "mark is either true or false"
          | Some y ->
            if not y
            then (
              worklist := IdSet.add !worklist branch;
              true)
            else y))
    cdg_graph
    instr_label
;;

(* Need to go through each postdom, see which one contains a marked statement i guess *)
let find_nearest_marked_postdom id id_to_node label_to_ids id_to_mark cdg_graph =
  let node = Hashtbl.find_exn id_to_node id in
  let successor_nodes = CFG.succ cdg_graph node in
  let rec find_helper successors =
    match successors with
    | [] -> failwith "no postdom that is marked"
    | h :: t ->
      let succ_ids = Hashtbl.find_exn label_to_ids h in
      let has_marked_statement =
        List.exists succ_ids ~f:(fun succ_id -> Hashtbl.find_exn id_to_mark succ_id)
      in
      if has_marked_statement then h else find_helper t
  in
  find_helper successor_nodes
;;

let process_label_table
  (label_to_bodies : (CFG.Node.t, Ssa.instr list) Hashtbl.t)
  cdg_graph
  =
  (* 
    Resulting tables:
    map node to id of branch that ends it
    map id to instruction
    map variable to id of its definition
    map id to mark
  *)
  let node_to_branch = Hashtbl.create ~growth_allowed:true (module Node) in
  let id_to_instr = Hashtbl.create (module Int) in
  let var_to_instr = VarTable.create ~growth_allowed:true () in
  let id_to_mark = Hashtbl.create ~growth_allowed:true (module Int) in
  let id_to_node = Hashtbl.create (module Int) in
  let label_to_ids = Hashtbl.create ~growth_allowed:true (module String) in
  let worklist = ref IdSet.empty in
  let counter = ref 0 in
  Hashtbl.iteri label_to_bodies ~f:(fun ~key:label ~data:instrs ->
    if not (CFG.mem_vertex cdg_graph label)
    then ()
    else (
      let _, id_list, last_instr =
        List.fold_left
          instrs
          ~init:(false, [], [])
          ~f:(fun (has_return, acc, instr_acc) instr ->
          if has_return
          then has_return, acc, instr_acc
          else (
            match instr with
            | Ssa.Ret _ | Ssa.Ret_void ->
              counter := !counter + 1;
              Hashtbl.set id_to_instr ~key:!counter ~data:instr;
              Hashtbl.set id_to_node ~key:!counter ~data:label;
              preprocess_instr instr var_to_instr id_to_mark worklist counter;
              true, !counter :: acc, instr :: instr_acc
              (* TODO: include jumps and callf raise and ifs *)
            | _ ->
              counter := !counter + 1;
              Hashtbl.set id_to_instr ~key:!counter ~data:instr;
              Hashtbl.set id_to_node ~key:!counter ~data:label;
              preprocess_instr instr var_to_instr id_to_mark worklist counter;
              false, !counter :: acc, instr :: instr_acc))
      in
      Hashtbl.set label_to_ids ~key:label ~data:(List.rev id_list);
      (* Printf.printf "label: %s\n" label;
      List.iter (List.rev last_instr) ~f:(fun instr ->
        Printf.printf "instr: %s\n" (Ssa.format_instr instr)); *)
      let last_instr = List.hd last_instr in
      match last_instr with
      | None -> ()
      | Some instr ->
        (* Need to match this instruction with possible branches, if or jump *)
        (match instr with
         | If _ | Jump _ -> Hashtbl.set node_to_branch ~key:label ~data:!counter
         | _ -> ())));
  (* Now, run through the worklist, mark *)
  while not (IdSet.is_empty !worklist) do
    let curr_id = IdSet.min_elt_exn !worklist in
    worklist := IdSet.remove !worklist curr_id;
    (* Now, need to run patten matching on the variables used in operation *)
    let instruction = Hashtbl.find_exn id_to_instr curr_id in
    process_instruction
      instruction
      curr_id
      var_to_instr
      id_to_mark
      worklist
      node_to_branch
      id_to_node
      cdg_graph
  done;
  (* 
    Sweep
    For postdominance, iterate through the cdg graph successors to find one that is marked?
  *)
  Hashtbl.map label_to_ids ~f:(fun ids ->
    List.filter_map ids ~f:(fun id ->
      let is_marked = Hashtbl.find_exn id_to_mark id in
      let instr = Hashtbl.find_exn id_to_instr id in
      if is_marked
      then Some instr
      else (
        match instr with
        | Jump _ -> failwith "jumps should all be marked"
        | If _ ->
          let jump_loc =
            find_nearest_marked_postdom id id_to_node label_to_ids id_to_mark cdg_graph
          in
          Some (Ssa.Jump jump_loc)
        | Label _ | Directive _ | Comment _ | Nop -> Some instr
        | _ -> None)))
;;

let run_adce (cfg_orig, root_orig, label_to_bodies, labels_in_order) =
  (* Printf.printf "\ngraph before adce\n";
  Abstrtossa.print_label_to_body label_to_bodies; *)
  let cfg_orig, root_orig, label_to_bodies, labels_in_order =
    Rebuild_cfg.rebuild_cfg (cfg_orig, root_orig, label_to_bodies, labels_in_order)
  in
  let cdg_graph, _, new_label_to_bodies =
    create_cdg (cfg_orig, root_orig, label_to_bodies)
  in
  (* Dot.output_graph
    (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_pre_adce.txt" root_orig))
    cfg_orig; *)
  (* Dot.output_graph
    (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_cdg.txt" root_orig))
    cdg_graph; *)
  let new_label_to_bodies' = process_label_table new_label_to_bodies cdg_graph in
  let new_label_to_bodies'' =
    Hashtbl.mapi label_to_bodies ~f:(fun ~key:label ~data:_ ->
      match Hashtbl.find new_label_to_bodies' label with
      | None -> [ Ssa.Nop ]
      | Some x -> x)
  in
  (* Hashtbl.filter_keys_inplace new_label_to_bodies' ~f:(fun key ->
    String.compare key "exit_node" <> 0 && String.compare key "entry_node" <> 0); *)
  let labels_in_order' =
    List.filter labels_in_order ~f:(fun label ->
      match Hashtbl.find new_label_to_bodies'' label with
      | None -> false
      | Some _ -> true)
  in
  let new_label_to_bodies''' =
    Hashtbl.map new_label_to_bodies'' ~f:(fun instrs ->
      List.filter instrs ~f:(fun instr ->
        match instr with
        | Nop -> false
        | _ -> true))
  in
  (* Printf.printf "\ngraph after adce\n";
  Abstrtossa.print_label_to_body new_label_to_bodies'''; *)
  cfg_orig, root_orig, new_label_to_bodies''', labels_in_order'
;;
