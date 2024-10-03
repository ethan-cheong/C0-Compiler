(* L1 Compiler
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Greedily colours the interference graph given an ordering of nodes and a graph
 *)

open Core
open Nodeset

(** Helper function for extracting options *)
let get_option = function
  | Some s -> s
  | None -> failwith "Node not found in hash table"
;;

(** This returns an ordered set of the 13 (?) registers we have available in their
     natural ordering (the ordering we define). For now, we use the predefined 
     ordering (their lexicographical ordering)*)
let get_register_set : NodeSet.t =
  NodeSet.of_list
    (List.map
       Assem.[ EAX; EBX; ECX; EDX; ESI; EDI; R8D; R9D; R11D; R12D; R13D; R14D; R15D ]
       ~f:(fun x -> Node.node_of_operand (Assem.Reg x)))
;;

(** Takes in an input precolouring with nodes that are already coloured.
    Requires: all registers in [precolouring] should be coloured with themselves
    all nodes in [node_ordering] are contained within the graph 
    represented by [adj_list]. 
    If nodes x, y are connected in the graph, then [adj_list] has entries 
    [x : ... y...] and [y: ... x ...].
    Note that adj_list is implemented with a Hashtbl that has keys of type 
    Node and values of type NodeSet.
    *)
let greedy_colouring
  ?(debug = false)
  (adj_list : (Node.t, NodeSet.t) Hashtbl.t)
  (node_ordering : Node.t list)
  : (Node.t, Node.t) Hashtbl.t
  =
  (* Hacky fix until meng hui fixes Max Card Search *)
  let regs, nonregs = List.partition_tf node_ordering ~f:(fun n -> Node.is_register n) in
  let proper_node_ordering = regs @ nonregs in
  let colouring =
    Hashtbl.create
      ~growth_allowed:true
      ~size:(List.length proper_node_ordering)
      (module Node)
  in
  if debug then Printf.printf "Node ordering that we are using: \n";
  if debug
  then List.iter proper_node_ordering ~f:(fun n -> print_string (Node.format_node n));
  let rec greedy_colouring_helper = function
    | [] -> ()
    | h :: t when Node.is_register h ->
      if debug
      then Printf.printf "\ncolouring register %s with itself\n" (Node.format_node h);
      Hashtbl.set colouring ~key:h ~data:h;
      greedy_colouring_helper t
    | h :: t ->
      if debug then Printf.printf "\ncolouring node ";
      if debug then print_string (Node.format_node h ^ "\n");
      let neighbours = Hashtbl.find adj_list h |> get_option in
      if debug then Printf.printf "Printing its neighbours:";
      if debug
      then Set.iter neighbours ~f:(fun x -> x |> Node.format_node |> print_string);
      let colours_used =
        Set.filter_map
          (module NodeSet.Elt)
          neighbours
          ~f:(fun neighbour -> Hashtbl.find colouring neighbour)
      in
      if debug then Printf.printf "\ncolours used so far by its neighbours:";
      if debug
      then Set.iter colours_used ~f:(fun x -> x |> Node.format_node |> print_string);
      let min_colour =
        match NodeSet.min_elt (NodeSet.diff get_register_set colours_used) with
        | None -> Node.null_node () (* Leave it uncoloured *)
        | Some s -> s
      in
      if debug
      then print_string ("\nmin colour used is " ^ Node.format_node min_colour ^ "\n");
      (match Hashtbl.add colouring ~key:h ~data:min_colour with
       | `Duplicate -> failwith "we already coloured this node"
       | `Ok ->
         ();
         greedy_colouring_helper t)
  in
  greedy_colouring_helper proper_node_ordering;
  colouring
;;

(*********************** TESTING ********************)
(* 
let print_hash ht =
  Hashtbl.iteri ht ~f:(fun ~key:x ~data:y ->
    print_string (Node.format_node x ^ " -> " ^ Node.format_node y ^ "\n"))
;;

let g1 =
  let adj_list = Hashtbl.create ~growth_allowed:false ~size:6 (module Node) in
  let add_nodes key lst =
    Hashtbl.set
      adj_list
      ~key:(Node.node_of_operand (Assem.Temp (Temp.make key)))
      ~data:
        (Set.of_list
           (module NodeSet.Elt)
           (List.map ~f:(fun x -> Node.node_of_operand (Temp (Temp.make x))) lst))
  in
  add_nodes 1 [ 3; 5; 6 ];
  add_nodes 2 [ 5; 6 ];
  add_nodes 3 [ 1; 4; 5 ];
  add_nodes 4 [ 3 ];
  add_nodes 5 [ 1; 3; 6; 2 ];
  add_nodes 6 [ 1; 5; 2 ];
  adj_list
;;

let k15 =
  let adj_list = Hashtbl.create ~growth_allowed:false ~size:15 (module Node) in
  let add_nodes key lst =
    Hashtbl.set
      adj_list
      ~key:(Node.node_of_operand (Assem.Temp (Temp.make key)))
      ~data:
        (Set.of_list
           (module NodeSet.Elt)
           (List.map ~f:(fun x -> Node.node_of_operand (Temp (Temp.make x))) lst))
  in
  add_nodes 1 [ 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 2 [ 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 3 [ 1; 2; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 4 [ 1; 2; 3; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 5 [ 1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 6 [ 1; 2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 7 [ 1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 8 [ 1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 9 [ 1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15 ];
  add_nodes 10 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15 ];
  add_nodes 11 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15 ];
  add_nodes 12 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 14; 15 ];
  add_nodes 13 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15 ];
  add_nodes 14 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 15 ];
  add_nodes 15 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14 ];
  adj_list
;;

(** "Saturate" all registers, then test if 16 is assigned 1 and 17 2.*)
let k15plus2 =
  let adj_list = Hashtbl.create ~growth_allowed:false ~size:17 (module Node) in
  let add_nodes key lst =
    Hashtbl.set
      adj_list
      ~key:(Node.node_of_operand (Assem.Temp (Temp.make key)))
      ~data:
        (Set.of_list
           (module NodeSet.Elt)
           (List.map ~f:(fun x -> Node.node_of_operand (Temp (Temp.make x))) lst))
  in
  add_nodes 1 [ 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 2 [ 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 3 [ 1; 2; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 4 [ 1; 2; 3; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 5 [ 1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 6 [ 1; 2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 7 [ 1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 8 [ 1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15 ];
  add_nodes 9 [ 1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15 ];
  add_nodes 10 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15 ];
  add_nodes 11 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15 ];
  add_nodes 12 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 14; 15 ];
  add_nodes 13 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15 ];
  add_nodes 14 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 15 ];
  add_nodes 15 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 17 ];
  add_nodes 16 [ 17 ];
  add_nodes 17 [ 16 ];
  adj_list
;;

let node_of_int_list lst =
  List.map ~f:(fun x -> Node.node_of_operand (Temp (Temp.make x))) lst
;;

let%expect_test "Graph colouring on a simple graph g1 with 6 nodes" =
  let coloring = greedy_colouring g1 (node_of_int_list [ 5; 2; 4; 3; 1; 6 ]) in
  print_hash coloring;
  [%expect
    {|
     5 -> 1
     2 -> 2
     4 -> 1
     3 -> 2
     1 -> 3
     6 -> 4
   |}]
;;

let%expect_test "Graph colouring on g1 in a diff order" =
  let output = greedy_colouring g1 (node_of_int_list [ 1; 2; 3; 4; 5; 6 ]) in
  print_hash output;
  [%expect
    {|
     1 -> 1
     2 -> 1
     3 -> 2
     4 -> 1
     5 -> 3
     6 -> 2
   |}]
;;

let%expect_test "Graph colouring K15 - the graph will need more than 13 regs" =
  let output =
    greedy_colouring
      k15
      (node_of_int_list [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ])
  in
  print_hash output;
  [%expect
    {|
   1 -> 1
   2 -> 2
   3 -> 3
   4 -> 4
   5 -> 5
   6 -> 6
   7 -> 7
   8 -> 8
   9 -> 9
   10 -> 10
   11 -> 11
   12 -> 12
   13 -> 13
   14 -> -1
   15 -> -1
 |}]
;;

let%expect_test "Graph colouring on K15 plus 2 - the graph will need more than 13 regs" =
  let output =
    greedy_colouring
      k15plus2
      (node_of_int_list [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17 ])
  in
  print_hash output;
  [%expect
    {|
   1 -> 1
   2 -> 2
   3 -> 3
   4 -> 4
   5 -> 5
   6 -> 6
   7 -> 7
   8 -> 8
   9 -> 9
   10 -> 10
   11 -> 11
   12 -> 12
   13 -> 13
   14 -> -1
   15 -> -1
   16 -> 1
   17 -> 2
 |}]
;; *)
