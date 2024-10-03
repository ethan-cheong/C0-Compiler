(* L1 Compiler
 * Given a mapping from temps to registers from greedy colouring and a list of 
 * abstract assembly instructions, returns the list with temps replaced with 
 * the corresponding register from the list.
 *)

open Core
module AS = Assem

(* Searches the colouring hashtbl for temps and replaces them accordingly. *)
let search_colouring (value : AS.operand) (colouring : (Node.t, Node.t) Hashtbl.t) =
  match value with
  | AS.Temp _ ->
    (match Hashtbl.find colouring (Node.node_of_operand value) with
     | Some x ->
       (try Node.operand_of_node x with
        | Failure _ -> value)
     | None -> value)
  | _ -> value
;;

(* Replaces any temps in each line. *)
let substitute_temps (colouring : (Node.t, Node.t) Hashtbl.t) = function
  | AS.Binop { op; dest; src } ->
    AS.Binop
      { op; dest = search_colouring dest colouring; src = search_colouring src colouring }
  | AS.Unop { op; src; div_type } ->
    AS.Unop { op; src = search_colouring src colouring; div_type }
  | AS.Test { lhs; rhs } ->
    AS.Test { lhs = search_colouring lhs colouring; rhs = search_colouring rhs colouring }
  | AS.Mov { dest; src } ->
    AS.Mov
      { dest = search_colouring dest colouring; src = search_colouring src colouring }
  | AS.Cmp { lhs; rhs } ->
    AS.Cmp { lhs = search_colouring lhs colouring; rhs = search_colouring rhs colouring }
  | x -> x
;;

(** Requires: colouring must be derived from applying register allocation to lst. 
     This means that all temps in lst should have a hash table key in colouring.*)
let replace_temps (lst : AS.instr list) (colouring : (Node.t, Node.t) Hashtbl.t)
  : AS.instr list
  =
  let rec replace_temps_helper lst acc =
    match lst with
    | [] -> List.rev acc
    | h :: t -> replace_temps_helper t (substitute_temps colouring h :: acc)
  in
  replace_temps_helper lst []
;;
