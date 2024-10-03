(* L1 Compiler
 Runs Maximum cardinality search algorithm as described in recitation and notes
 Edited dune file to include the following: 
core_kernel core_kernel.pairing_heap
As referenced from https://groups.google.com/g/ocaml-core/c/nMscbnfAf5Y 
 *)
open Core
module AS = Assem
module NodeTbl = Hashtbl.Make (Node)
module NodeCmp = Comparator.Make (Node)
module NodeSet = Regalloc_modules.NodeSet

(* Comparison function to allow for selecting of maximal weight *)
let compare_node_weights ((wt1, node1) : int * Node.t) ((wt2, node2) : int * Node.t) =
  match wt1, wt2 with
  | _ when wt1 > wt2 -> true
  | _ when wt1 < wt2 -> false
  | _ -> Node.compare node1 node2 >= 0
;;

(* Helper function to get weight of node from weighttbl *)
let get_weight tbl node =
  match NodeTbl.find tbl node with
  | None -> failwith "Node should no longer exist"
  | Some x -> x
;;

(* Give a node to be removed from the table, it is removed from all the sets that contain it *)
let remove_from_neighbours node nodeset =
  match nodeset with
  | None -> failwith "if removing a node, its neighbours should still exist"
  | Some x -> NodeSet.remove x node
;;

(* Return the added weight *)
let update_weight = function
  | Some x -> x + 1
  | None -> failwith "Update weight should only occur to valid nodes"
;;

(* Update weights for all neighbours in a NodeSet in the weight table *)
let update_weights (neighbours : NodeSet.t) (weight_tbl : int NodeTbl.t) =
  NodeSet.iter neighbours ~f:(fun x -> NodeTbl.update weight_tbl x ~f:update_weight)
;;

(* Removes the current vertex from all neighbours to prevent future updates *)
let update_neighbours
  (neighbours : NodeSet.t)
  (vertex : Node.t)
  (neighbour_tbl : NodeSet.t NodeTbl.t)
  =
  NodeSet.iter neighbours ~f:(fun x ->
    NodeTbl.update neighbour_tbl x ~f:(remove_from_neighbours vertex))
;;

(* Removes the current vertex from both weight and neighbour tables *)
let remove_from_tables node neighbour_tbl weight_tbl =
  let (_ : unit) = NodeTbl.remove neighbour_tbl node in
  NodeTbl.remove weight_tbl node
;;

(* If node has been visited, just remove all its edges as well.
   Also, update all the weights *)
let update_tables weight_tbl neighbour_tbl node =
  let neighbours =
    match NodeTbl.find neighbour_tbl node with
    | None -> failwith "if removing a node, it must exist in table"
    | Some x -> x
  in
  update_weights neighbours weight_tbl;
  update_neighbours neighbours node neighbour_tbl;
  remove_from_tables node neighbour_tbl weight_tbl
;;

(* Get biggest weight to find the node to remove from table *)
let find_biggest_weight tbl nodes curr_weight curr_node =
  let rec helper nodes curr_weight curr_node =
    match nodes with
    | [] -> curr_node
    | h :: t ->
      let h_weight = get_weight tbl h in
      if compare_node_weights (h_weight, h) (curr_weight, curr_node)
      then helper t h_weight h
      else helper t curr_weight curr_node
  in
  helper nodes curr_weight curr_node
;;

(* Helper function to split the current list of nodes for use in the algorithm *)
let split_key_list = function
  | [] -> failwith "List should have at least one element if splitting"
  | h :: t -> h, t
;;

(* Initialisres the required tables. 
   Adjlist is copied to prevent deleted from adjlist if the previous values are required *)
let build_weight_table adjlist = NodeTbl.map adjlist ~f:(fun _ -> 0)
let build_tables adjlist = build_weight_table adjlist, NodeTbl.copy adjlist

let run_algo adjlist =
  let rec helper weight_tbl neighbours_tbl acc =
    match Hashtbl.count neighbours_tbl ~f:(fun _ -> true) with
    | 0 -> acc
    | _ ->
      let keys = Hashtbl.keys neighbours_tbl in
      let head, tail = split_key_list keys in
      let head_weight = get_weight weight_tbl head in
      let biggest_node = find_biggest_weight weight_tbl tail head_weight head in
      let (_ : unit) = update_tables weight_tbl neighbours_tbl biggest_node in
      helper weight_tbl neighbours_tbl (biggest_node :: acc)
  in
  let weight_tbl, neighbours_tbl = build_tables adjlist in
  helper weight_tbl neighbours_tbl []
;;

(* Algorithm will return the node in reverse order of popping. *)
let max_cardinality_search (adjlist : (Node.t, NodeSet.t) Hashtbl.t) : Node.t list =
  run_algo adjlist
;;

(******************************TESTING****************************************)

(* Helper functions to print test cases *)
(* let node_from_int (x : int) = Node.node_of_operand (AS.Temp (Temp.make x))

let node_from_reg (x : AS.reg) =
  Node.node_of_operand (AS.Reg { reg = x; size = AS.DOUBLE })
;; *)

(* let node_to_string node = Assem.format_operand (Node.operand_of_node node) *)

(* let create_adjlist_test =
  let t1 = node_from_int 1 in
  let t2 = node_from_int 2 in
  let t3 = node_from_int 3 in
  let t4 = node_from_int 4 in
  let t5 = node_from_int 5 in
  let rx = node_from_reg AS.R10 in
  let ry = node_from_reg AS.R11 in
  let rz = node_from_reg AS.R12 in
  let rax = node_from_reg AS.AX in
  let t1_adj = NodeSet.of_list [ rx ] in
  let t2_adj = NodeSet.of_list [ rx ] in
  let t3_adj = NodeSet.of_list [ rx ] in
  let t4_adj = NodeSet.of_list [ rx; ry; rz ] in
  let t5_adj = NodeSet.of_list [ rx; rz ] in
  let rx_adj = NodeSet.of_list [ t1; t2; t3; t4; t5; ry; rz ] in
  let ry_adj = NodeSet.of_list [ t4; rx; rz ] in
  let rz_adj = NodeSet.of_list [ t4; t5; rx; ry ] in
  let rax_adj = NodeSet.of_list [] in
  let all_nodes =
    [ t1, t1_adj
    ; t2, t2_adj
    ; t3, t3_adj
    ; t4, t4_adj
    ; t5, t5_adj
    ; rx, rx_adj
    ; ry, ry_adj
    ; rz, rz_adj
    ; rax, rax_adj
    ]
  in
  match NodeTbl.of_alist ~growth_allowed:true ~size:500 all_nodes with
  | `Duplicate_key _ -> failwith "duplicate key"
  | `Ok x -> x
;; *)
(* 
(* OUTPUTS IN REVERSE *)
let%expect_test "Test parsing of simple main into 3 assem" =
  let graph = create_adjlist_test in
  let output_graph = max_cardinality_search graph in
  let output_graph_line instr = Printf.printf "\t%s\n" (node_to_string instr) in
  List.iter ~f:output_graph_line output_graph;
  [%expect
    {|
      %eax
      %t1
      %t2
      %t3
      %t5
      %t4
      %r10d
      %r11d
      %r12d
    |}]
;; *)
