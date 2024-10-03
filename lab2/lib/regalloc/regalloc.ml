open Core
module AS = Assem

(** This function is only called by lab1 checkpoint, and not actually used in 
    top. *)
let regalloc (_program : Lab1_checkpoint.program) : Lab1_checkpoint.allocations =
  let liveness_lst = Checkpointtoliveness.checkpoint_to_liveness _program in
  (* List.iter liveness_lst ~f:(fun line ->
    line |> generate_pairwise_list_from_line |> print_pairwise_list); *)
  let intf_graph = Buildintfgraph.build_interference_graph liveness_lst in
  let node_ordering = Maxcardsearch.max_cardinality_search intf_graph in
  (* Printf.printf "Number of distinct nodes is %d\n" (List.length node_ordering); *)
  let greedy_colouring =
    Greedycolouring.greedy_colouring ~debug:false intf_graph node_ordering
  in
  let get_defines (l : Liveness.line) =
    match l with
    | { defines = d; _ } -> d
  in
  List.map liveness_lst ~f:(fun line ->
    match List.hd (get_defines line) with
    | None -> None
    | Some d ->
      (match d with
       | Temp _ ->
         Some
           Node.(
             ( d |> node_of_operand |> format_node
             , d |> node_of_operand |> Hashtbl.find_exn greedy_colouring |> format_node ))
       | _ -> None))
;;
