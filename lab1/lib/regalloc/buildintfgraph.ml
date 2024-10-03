(* L1 Compiler
 * Builds interference graph given list of lines from liveness analysis
 * Goes through each line
 * Given defs and liveouts, adds defs to adjlist for all liveout and liveout to adjlist for def
 *)

module AS = Assem
open Nodeset
open Core

(* Adds data to table, overwriting if necessary *)
let add_to_table table ~key ~data =
  match Hashtbl.add table ~key ~data with
  | `Duplicate ->
    let (_ : unit) = Hashtbl.set table ~key ~data in
    false
  | `Ok -> true
;;

(* Adds def to adjlists of all liveouts *)
let add_def_to_liveout defs liveouts graph =
  let rec helper liveouts =
    match liveouts with
    | [] -> ()
    | h :: t ->
      let liveout_entry =
        match Hashtbl.find graph h with
        | None -> NodeSet.of_list [ defs ]
        | Some x -> NodeSet.add x defs
      in
      assert (add_to_table graph ~key:h ~data:liveout_entry || true);
      helper t
  in
  helper liveouts
;;

(* Adds liveouts to adjlist of def *)
let add_liveout_to_def defs liveouts graph =
  let key_entries =
    match Hashtbl.find graph defs with
    | None -> NodeSet.of_list liveouts
    | Some x -> NodeSet.union x (NodeSet.of_list liveouts)
  in
  assert (add_to_table graph ~key:defs ~data:key_entries || true)
;;

(* Extract and assert only one variable defined per line *)
let extract_def = function
  | h :: [] -> Some h
  | [] -> None
  | _ -> failwith "Must have at most 1 definition per line"
;;

let remove_key_from_values tbl =
  Hashtbl.mapi tbl ~f:(fun ~key ~data -> NodeSet.remove data key)
;;

(* Builds interference graph with keys in adjlist *)
let build_graph_with_keys (lst : Liveness.line list) : (Node.t, NodeSet.t) Hashtbl.t =
  let tbl = Hashtbl.create ~growth_allowed:true ~size:500 (module Node) in
  let rec helper (lst : Liveness.line list) tbl =
    match lst with
    | [] -> tbl
    | hd :: t ->
      let defines = hd.defines in
      let live_out = hd.live_out in
      let def_opt = extract_def defines in
      (match def_opt with
       | Some def ->
         let def_node = Node.node_of_operand def in
         let liveout_nodes = List.map live_out ~f:(fun x -> Node.node_of_operand x) in
         let (_ : unit) = add_liveout_to_def def_node liveout_nodes tbl in
         let (_ : unit) = add_def_to_liveout def_node liveout_nodes tbl in
         helper t tbl
       | None -> helper t tbl)
    (* Since no need to add nodes*)
  in
  helper lst tbl
;;

let build_interference_graph (lst : Liveness.line list) : (Node.t, NodeSet.t) Hashtbl.t =
  let tbl = build_graph_with_keys lst in
  remove_key_from_values tbl
;;

(* Format operands and nodes *)
let format_op x = "\"" ^ AS.format_operand x ^ "\""
let format_node x = Node.operand_of_node x |> format_op

let format_node_set node_set =
  "[" ^ String.concat ~sep:", " (List.map ~f:format_node (NodeSet.to_list node_set)) ^ "]"
;;

(* Formats adjlist into list for output testing *)
let table_to_list tbl =
  Hashtbl.fold tbl ~init:[] ~f:(fun ~key ~data acc ->
    (format_node key ^ ": " ^ format_node_set data) :: acc)
;;
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
