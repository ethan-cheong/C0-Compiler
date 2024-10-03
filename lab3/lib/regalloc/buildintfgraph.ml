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
(* Used in testing *)
(* 
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
;; *)

(* 
let%expect_test "test" =
  Temp.reset ();
  let lexbuf = Lexing.from_string "int main() {return 1;}" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = Intcodegen.int_code_gen ir in
  let live_lst = Liveness.liveness assem_three in
  let graph_set = build_interference_graph live_lst in
  let graph_list = table_to_list graph_set in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  List.iter ~f:output_graph_line graph_list;
  [%expect {|
      "%eax": []
    |}]
;;

let%expect_test "Test parsing of simple main into 3 assem" =
  Temp.reset ();
  let lexbuf = Lexing.from_string "int main() {return (5 + 3 - 6 * 3); }" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = Intcodegen.int_code_gen ir in
  let live_lst = Liveness.liveness assem_three in
  let graph_table = build_interference_graph live_lst in
  let graph_list = table_to_list graph_table in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  List.iter ~f:output_graph_line graph_list;
  [%expect
    {|
      "%t4": ["%t3"]
      "%t3": ["%t4"]
      "%t5": ["%t1", "%t6"]
      "%t1": ["%t2", "%t5", "%t6"]
      "%t6": ["%t1", "%t5"]
      "%t2": ["%t1"]
      "%eax": []
    |}]
;; *)

(* let%expect_test "Test parsing of simple main into 3 assem" =
  Temp.reset ();
  let lexbuf =
    Lexing.from_string
      "int pow(int b, int e) {\n\
      \    if (e == 0) {\n\
      \      return 1;\n\
      \    } else {\n\
      \      return b * pow(b, e-1);\n\
      \    }\n\
      \  }"
  in
  let ast = C0_parser.program_l3 C0_lexer.initial lexbuf in
  let elaborated_ast = Elaborate.elaborate ast in
  let typechecked_ast = Elaborate_decl.elaborate_decl elaborated_ast in
  let ir = Trans.translate typechecked_ast in
  let three_addr_assem = Intcodegen.int_code_gen ir in
  let abstr_assem = Instrsel.instr_sel three_addr_assem in
  let headers = Extract_args.extract_args abstr_assem in
  let item =
    match List.hd abstr_assem with
    | Some x -> x
    | None -> failwith "program must have pow function"
  in
  let live_lst = Liveness.liveness item headers in
  let graph_table = build_interference_graph live_lst in
  let graph_list = table_to_list graph_table in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  Printf.printf
    "%s"
    (List.fold
       (List.map (List.concat abstr_assem) ~f:Assem.format)
       ~init:""
       ~f:(fun x y -> x ^ "\n" ^ y));
  List.iter ~f:output_graph_line graph_list;
  [%expect {|
    |}]
;; *)

(* let lexbuf = Lexing.from_string "int main() {return (5 + 3 - 6 * 3); }" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = Intcodegen.int_code_gen ir in
  let live_lst = Liveness.liveness assem_three in
  let graph_table = build_interference_graph live_lst in
  let graph_list = table_to_list graph_table in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  List.iter ~f:output_graph_line graph_list;
  [%expect
    {|
      "%t4": ["%t3"]
      "%t3": ["%t4"]
      "%t5": ["%t1", "%t6"]
      "%t1": ["%t2", "%t5", "%t6"]
      "%t6": ["%t1", "%t5"]
      "%t2": ["%t1"]
      "%eax": []
    |}] *)
(* 
let%expect_test "Test pow function intf graph" =
  Temp.reset ();
  let signature =
    AS.
      { label = "pow"
      ; args =
          [ AS.Reg { reg = AS.DI; size = DOUBLE }; AS.Reg { reg = AS.SI; size = DOUBLE } ]
      ; tail_rec = false
      }
  in
  let b = AS.Temp (Temp.make 100) in
  let e = AS.Temp (Temp.make 200) in
  let t0 = AS.Temp (Temp.make 0) in
  let t1 = AS.Temp (Temp.make 1) in
  let t2 = AS.Temp (Temp.make 2) in
  let instrs =
    AS.
      [ Mov { dest = b; src = AS.Reg { reg = AS.DI; size = DOUBLE } }
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
      ; Call { ident = "pow"; args = [ b; t0 ] }
      ; Mov { dest = t1; src = AS.Reg { reg = AS.AX; size = DOUBLE } }
      ; Binop { op = IMul; src = b; dest = t1 }
      ; Mov { dest = t2; src = t1 }
      ; Mov { dest = AS.Reg { reg = AS.AX; size = DOUBLE }; src = t2 }
      ; Ret
      ]
  in
  let func = signature, instrs in
  let liveness_tables = create_liveness_tables in
  let headers = Extract_args.extract_args [ func ] in
  let live_lst = Liveness.liveness func headers liveness_tables in
  let graph_table = build_interference_graph live_lst in
  let graph_list = table_to_list graph_table in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  Printf.printf
    "%s"
    (List.fold
       (List.map (List.concat [ instrs ]) ~f:Assem.format)
       ~init:""
       ~f:(fun x y -> x ^ "\n" ^ y));
  Printf.printf "\n";
  List.iter ~f:output_graph_line graph_list;
  [%expect {|
    |}]
;; *)

(* let%expect_test "Test comparison of nodes" =
  let testing_vars =
    [ Node.Temp (Temp.make 1), Node.Temp (Temp.make 1)
    ; Node.Temp (Temp.make 1), Node.Temp (Temp.make 2)
    ; Node.Temp (Temp.make 2), Node.Temp (Temp.make 1)
    ; Node.Reg AS.AX, Node.Temp (Temp.make 1)
    ; Node.Reg AS.AX, Node.Reg AS.AX
    ; Node.Reg AS.AX, Node.Reg AS.DX
    ; Node.Null, Node.Reg AS.AX
    ; Node.Null, Node.Temp (Temp.make 2)
    ]
  in
  let compare_vars (var1, var2) =
    Printf.printf "%s\n" (string_of_int (Node.compare var1 var2))
  in
  List.iter ~f:compare_vars testing_vars;
  [%expect {|
    |}]
;; *)
