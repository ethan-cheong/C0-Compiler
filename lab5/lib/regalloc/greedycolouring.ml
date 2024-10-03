(* L1 Compiler
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Greedily colours the interference graph given an ordering of nodes and a graph
 *)

open Core
module NodeSet = Regalloc_modules.NodeSet
module AS = Assem

(** Helper function for extracting options *)
let get_option = function
  | Some s -> s
  | None -> failwith "Node not found in hash table"
;;

(** This returns an ordered set of the 13 registers we have available in their
      natural ordering (the ordering we define in assem).  *)
let get_register_set : NodeSet.t =
  NodeSet.of_list
    (List.map
       (* The order in this list is inconsequential. *)
       Assem.[ AX; BX; CX; DX; SI; DI; BP; R8; R9; R11; R12; R13; R14; R15 ]
       ~f:(fun x -> Node.node_of_operand (Assem.Reg { reg = x; size = DOUBLE })))
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
  (* (operands : Assem.operand list) *)
  (* Hacky fix until meng hui fixes Max Card Search *)
  let regs, nonregs = List.partition_tf node_ordering ~f:(fun n -> Node.is_register n) in
  let proper_node_ordering = regs @ nonregs in
  let colouring =
    Hashtbl.create
      ~growth_allowed:true
      ~size:(List.length proper_node_ordering)
      (module Node)
  in
  (* let operand_nodes = List.map operands ~f:Node.node_of_operand in *)
  (* pre_colour ~colouring ~operands:operand_nodes; *)
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
      then NodeSet.iter neighbours ~f:(fun x -> x |> Node.format_node |> print_string);
      let colours_used =
        NodeSet.filter_map neighbours ~f:(fun neighbour ->
          Hashtbl.find colouring neighbour)
      in
      if debug then Printf.printf "\ncolours used so far by its neighbours:";
      if debug
      then NodeSet.iter colours_used ~f:(fun x -> x |> Node.format_node |> print_string);
      let min_colour =
        match NodeSet.min_elt (NodeSet.diff get_register_set colours_used) with
        | None -> Node.null_node () (* Leave it uncoloured *)
        | Some s -> s
      in
      if debug
      then print_string ("\nmin colour used is " ^ Node.format_node min_colour ^ "\n");
      (match Hashtbl.add colouring ~key:h ~data:min_colour with
       | `Duplicate ->
         if debug then Printf.printf "duplicate, not sure if issue\n";
         greedy_colouring_helper t
       | `Ok -> greedy_colouring_helper t)
  in
  greedy_colouring_helper proper_node_ordering;
  (* remove_colour ~colouring ~operands:operand_nodes; *)
  colouring
;;

(* Only take the uses and defs of movs, arrange into a pair *)
let extract_movs (lst : Liveness.line list) : (Node.t * Node.t) list =
  List.filter_map lst ~f:(fun { move; uses; defines; _ } ->
    if not move
    then None
    else if NodeSet.length uses <> 1
    then None
    else if NodeSet.length defines <> 1
    then None
    else (
      let use =
        match List.hd (NodeSet.to_list uses) with
        | None -> failwith "must have 1 uses"
        | Some x -> x
      in
      let define =
        match List.hd (NodeSet.to_list defines) with
        | None -> failwith "must have 1 defines"
        | Some x -> x
      in
      match use, define with
      | Reg _, Reg _ -> None
      | Reg _, _ -> None
      | _, Reg _ -> None
      | _, _ -> Some (use, define)))
;;

let create_new_node dummy_counter =
  let t = !dummy_counter in
  incr dummy_counter;
  Node.Dummy t
;;

let update_neighbours
  ~(adj_list : (Node.t, NodeSet.t) Hashtbl.t)
  ~(coloured_table : (Node.t, Node.t) Base.Hashtbl.t)
  ~(has_coalesced : (Node.t, unit) Hashtbl.t)
  neighbours
  used
  defined
  new_node
  min_colour
  : unit
  =
  (* Adjlist can be modified, so remove both used and defined.
      Also remove the edges to used/defined *)
  Hashtbl.remove adj_list used;
  Hashtbl.remove adj_list defined;
  NodeSet.iter neighbours ~f:(fun neighbour ->
    Hashtbl.update adj_list neighbour ~f:(fun neighbour_set ->
      match neighbour_set with
      | None -> NodeSet.empty
      | Some x ->
        let removed_used = NodeSet.remove x used in
        let removed_defined = NodeSet.remove removed_used defined in
        NodeSet.add removed_defined new_node));
  (* coloured_table can include the dummy, since no function refers to dummies *)
  (* Now, add the new node to the adjlist in the neighbours *)
  Hashtbl.set adj_list ~key:new_node ~data:neighbours;
  (* Set the new_node, used, and defined colour in coloured_table as well. *)
  Hashtbl.set coloured_table ~key:used ~data:min_colour;
  Hashtbl.set coloured_table ~key:defined ~data:min_colour;
  Hashtbl.set coloured_table ~key:new_node ~data:min_colour;
  Hashtbl.set has_coalesced ~key:used ~data:();
  Hashtbl.set has_coalesced ~key:defined ~data:()
;;

let try_coalesce
  ~(adj_list : (Node.t, NodeSet.t) Hashtbl.t)
  ~(coloured_table : (Node.t, Node.t) Base.Hashtbl.t)
  ~(has_coalesced : (Node.t, unit) Hashtbl.t)
  used
  defined
  dummy_counter
  : unit
  =
  match Hashtbl.find has_coalesced used, Hashtbl.find has_coalesced defined with
  | Some _, _ -> ()
  | _, Some _ -> ()
  | None, None ->
    (* Make sure that used and defined have not yet been replaced? *)
    let used_neighbours =
      match Hashtbl.find adj_list used with
      | None -> NodeSet.empty
      | Some x ->
        (* Printf.printf "temp: %s |" (Node.format_node used);
         NodeSet.iter x ~f:(fun x -> Printf.printf "%s " (Node.format_node x));
         Printf.printf "\n"; *)
        x
    in
    if NodeSet.mem used_neighbours defined
    then ()
    else (
      (* Printf.printf "temps: %s %s\n" (Node.format_node used) (Node.format_node defined); *)
      let def_neighbours =
        match Hashtbl.find adj_list defined with
        | None -> NodeSet.empty
        | Some x -> x
      in
      (* Now, some union magick *)
      let neighbours = NodeSet.union used_neighbours def_neighbours in
      let neighbours_colours =
        (* map is expensive, n log(n) *)
        NodeSet.map neighbours ~f:(fun x ->
          match Hashtbl.find coloured_table x with
          | Some x -> x
          | None -> failwith "node must be coloured, at least null node")
      in
      let neighbours_colours' = NodeSet.remove neighbours_colours (Node.null_node ()) in
      (* Now, check if there is a register that exists and is not a null node lol *)
      let exists, min_colour =
        match NodeSet.min_elt (NodeSet.diff get_register_set neighbours_colours') with
        | None -> false, Node.null_node () (* Leave it uncoloured *)
        | Some s -> true, s
      in
      if not exists
      then ()
      else (
        (* Need to create new node here. New node added into the graph and replaces used/defined *)
        let new_node = create_new_node dummy_counter in
        (* Iterate through all the neighbours, update the edges *)
        update_neighbours
          ~adj_list
          ~coloured_table
          ~has_coalesced
          neighbours
          used
          defined
          new_node
          min_colour))
;;

(* coalesce_table is the table mapping from original_node to new_node *)
let coalesce
  (coloured_table : (Node.t, Node.t) Hashtbl.t)
  (adj_list : (Node.t, NodeSet.t) Hashtbl.t)
  liveness_line
  =
  let movs = extract_movs liveness_line in
  let has_coalesced = Hashtbl.create ~growth_allowed:true ~size:16 (module Node) in
  let dummy_counter = ref 0 in
  (* Now, iterate through the moves and run the coalesce *)
  List.iter movs ~f:(fun (used, defined) ->
    try_coalesce ~coloured_table ~adj_list ~has_coalesced used defined dummy_counter);
  coloured_table
;;
