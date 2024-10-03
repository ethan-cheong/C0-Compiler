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
  ~(func : AS.func)
  ~(headers : (string, NodeSet.t) Hashtbl.t)
  ~(liveness_tables : Regalloc_modules.liveness_tables)
  ~(_skip_regalloc_per_function : int)
  ~(_skip_mcs : int)
  ~(debug : bool)
  ~(timestamps : Timestamp.t)
  : AS.func
  =
  (* Skip functions if they are tail-recursive and have less than 16 temps, 
      or if they are too big for regalloc*)
  (* TODO: it might be more efficient to keep track of temp_count for each
          function in their header! we can count the number of temps assigned
          during trans... *)
  if ((fst func).tail_rec && (fst func).num_temps <= 16)
     || (fst func).num_temps > _skip_regalloc_per_function
  then func
  else (
    let func_name = (fst func).label in
    if debug then Timestamp.mark_timestamp timestamps ("liveness for " ^ func_name);
    let (live_lst : Liveness.line list) =
      Liveness.liveness func headers liveness_tables
    in
    if debug then Timestamp.mark_timestamp timestamps ("liveness for " ^ func_name);
    let (_ : unit) = clear_tables liveness_tables in
    if debug then Timestamp.mark_timestamp timestamps ("buildintfgraph for " ^ func_name);
    let intf_graph = Buildintfgraph.build_interference_graph live_lst in
    if debug then Timestamp.mark_timestamp timestamps ("buildintfgraph for " ^ func_name);
    if debug then Timestamp.mark_timestamp timestamps ("maxcardsearch for " ^ func_name);
    let node_ordering =
      if (fst func).num_temps > _skip_mcs
      then
        Hashtbl.keys intf_graph
        (* TODO: use the same hash tbl for each func, then clear after completion
            Initialze table size to be equal to the tuning parameter *)
      else Maxcardsearch.max_cardinality_search intf_graph
    in
    if debug then Timestamp.mark_timestamp timestamps ("maxcardsearch for " ^ func_name);
    let func_header = fst func in
    let func_args = func_header.args in
    if debug then Timestamp.mark_timestamp timestamps ("greedycolouring for " ^ func_name);
    let greedy_color =
      Greedycolouring.greedy_colouring ~debug:false intf_graph node_ordering
    in
    if debug then Timestamp.mark_timestamp timestamps ("greedycolouring for " ^ func_name);
    let colored_args = Replacetemps.replace_temps_header greedy_color func_args in
    let abstr_assem = snd func in
    if debug then Timestamp.mark_timestamp timestamps ("replacetemps for " ^ func_name);
    let colored_body = Replacetemps.replace_temps abstr_assem greedy_color in
    if debug then Timestamp.mark_timestamp timestamps ("replacetemps for " ^ func_name);
    let new_signature = AS.{ func_header with args = colored_args; regalloc = true } in
    new_signature, colored_body)
;;

let regalloc
  (funcs : AS.func list)
  ~(_skip_regalloc_per_function : int)
  ~(_skip_mcs : int)
  ~(debug : bool)
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
