(* L3 Compiler
 * Runs all the functions required for regalloc
 *)

open Core
module AS = Assem
module Int32Set = Type_modules.Int32Set
module Int32Table = Type_modules.Int32Table
module NodeSet = Regalloc_modules.NodeSet

let create_liveness_tables =
  let pred_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let jump_table = Hashtbl.create ~growth_allowed:true ~size:500 (module String) in
  let livein_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let liveout_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let uses_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let defs_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let movs_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  Regalloc_modules.
    { uses_table
    ; defs_table
    ; movs_table
    ; jump_table
    ; pred_table
    ; liveout_table
    ; livein_table
    }
;;

let clear_tables (tables : Regalloc_modules.liveness_tables) : unit =
  let (_ : unit) = Hashtbl.clear tables.uses_table in
  let (_ : unit) = Hashtbl.clear tables.defs_table in
  let (_ : unit) = Hashtbl.clear tables.movs_table in
  let (_ : unit) = Hashtbl.clear tables.jump_table in
  let (_ : unit) = Hashtbl.clear tables.pred_table in
  let (_ : unit) = Hashtbl.clear tables.liveout_table in
  Hashtbl.clear tables.livein_table
;;

let regalloc_indiv
  ?(intf_graph_file = "intf_graph.txt")
  ~(func : AS.func)
  ~(headers : (string, NodeSet.t) Hashtbl.t)
  ~(liveness_tables : Regalloc_modules.liveness_tables)
  ~(_skip_regalloc_per_function : int)
  ~(_coalesce : bool)
  ~(_skip_mcs : int)
  ~(debug : bool)
  ~(do_opt : bool)
  ~(print_intf_graph : bool)
  ~(timestamps : Timestamp.t)
  : AS.func
  =
  (* Skip functions if they are tail-recursive and have less than 16 temps, 
     or if they are too big for regalloc*)
  if ((fst func).tail_rec && (fst func).num_temps <= 16)
     || (fst func).num_temps > _skip_regalloc_per_function
  then func
  else (
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " liveness");
    let (live_lst : Liveness.line list) =
      Liveness.liveness func headers liveness_tables ~timestamps
    in
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " liveness");
    let (_ : unit) = clear_tables liveness_tables in
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " buildintfgraph");
    let intf_graph = Buildintfgraph.build_interference_graph live_lst in
    if print_intf_graph || debug
    then Buildintfgraph.table_to_graph intf_graph intf_graph_file;
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " buildintfgraph");
    (* if debug then Printf.printf "%s" (Liveness.string_of_node_lst live_lst); *)
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " mcs");
    let node_ordering =
      if (fst func).num_temps > _skip_mcs
      then Hashtbl.keys intf_graph
      else Maxcardsearch.max_cardinality_search intf_graph
    in
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " mcs");
    let func_header = fst func in
    let func_args = func_header.args in
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " greedycolouring");
    let greedy_color =
      Greedycolouring.greedy_colouring ~debug:false intf_graph node_ordering
    in
    let coalesced =
      if do_opt && _coalesce
      then Greedycolouring.coalesce greedy_color intf_graph live_lst
      else greedy_color
    in
    if print_intf_graph || debug
    then Buildintfgraph.table_to_graph intf_graph "intf_graph_after.txt";
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " greedycolouring");
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " replacetemps");
    let colored_args = Replacetemps.replace_temps_header coalesced func_args in
    let abstr_assem = snd func in
    let colored_body = Replacetemps.replace_temps abstr_assem greedy_color in
    Timestamp.mark_timestamp timestamps ((fst func).label ^ " replacetemps");
    let new_signature = AS.{ func_header with args = colored_args; regalloc = true } in
    new_signature, colored_body)
;;

let regalloc
  ?(intf_graph_file = "intf_graph.txt")
  (funcs : AS.func list)
  ~(_skip_regalloc_per_function : int)
  ~(_skip_mcs : int)
  ~(_coalesce : bool)
  ~(debug : bool)
  ~(do_opt : bool)
  ~(print_intf_graph : bool)
  ~(timestamps : Timestamp.t)
  : AS.func list
  =
  let liveness_tables = create_liveness_tables in
  let headers = Extract_args.extract_args funcs in
  List.map funcs ~f:(fun func ->
    regalloc_indiv
      ~func
      ~headers
      ~_skip_regalloc_per_function
      ~liveness_tables
      ~_skip_mcs
      ~debug
      ~_coalesce
      ~do_opt
      ~print_intf_graph
      ~intf_graph_file
      ~timestamps)
;;

(* let%expect_test "Test pow function regalloc" =
  Temp.reset ();
  let func_label =
    AS.Func_label
      { label = "pow"
      ; args =
          [ AS.Reg { reg = AS.DI; size = DOUBLE }; AS.Reg { reg = AS.SI; size = DOUBLE } ]
      }
  in
  let b = AS.Temp (Temp.make 100) in
  let e = AS.Temp (Temp.make 200) in
  let t0 = AS.Temp (Temp.make 0) in
  let t1 = AS.Temp (Temp.make 1) in
  let t2 = AS.Temp (Temp.make 2) in
  let instrs =
    AS.
      [ func_label
      ; Mov { dest = b; src = AS.Reg { reg = AS.DI; size = DOUBLE } }
      ; Mov { dest = e; src = AS.Reg { reg = AS.SI; size = DOUBLE } }
      ; Cmp { lhs = Imm Int32.zero; rhs = e }
      ; Jc { cmp = E; label = "done" }
      ; Jmp "recurse"
      ; Label "done"
      ; Mov { dest = AS.Reg { reg = AS.AX; size = DOUBLE }; src = Imm Int32.one }
      ; Ret
      ; Label "recurse"
      ; Binop { op = Sub; src = Imm Int32.one; dest = e }
      ; Mov { dest = t0; src = e }
      ; Mov { dest = AS.Reg { reg = AS.SI; size = DOUBLE }; src = t0 }
      ; Mov { dest = AS.Reg { reg = AS.DI; size = DOUBLE }; src = b }
      ; Call "pow"
      ; Mov { dest = t1; src = AS.Reg { reg = AS.AX; size = DOUBLE } }
      ; Binop { op = IMul; src = b; dest = t1 }
      ; Mov { dest = t2; src = t1 }
      ; Mov { dest = AS.Reg { reg = AS.AX; size = DOUBLE }; src = t2 }
      ; Ret
      ]
  in
  let outputs = regalloc [ instrs ] ~temp_counter:0 ~_skip_mcs:10 in
  Printf.printf
    "%s"
    (List.fold
       (List.map (List.concat outputs) ~f:Assem.format)
       ~init:""
       ~f:(fun x y -> x ^ "\n" ^ y));
  [%expect {|
    |}]
;; *)
