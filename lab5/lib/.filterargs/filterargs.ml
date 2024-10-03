(* L1 Compiler
 * Argument filtering. 
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Filters for function arguments that are actually used in the function body.
 *)
open Core
module ThreeAS = Threeaddrassem
module TempSet = Set.Make (Temp)

let is_temp = function
  | ThreeAS.Temp _ -> true
  | _ -> false
;;

let temp_of_operand = function
  | ThreeAS.Temp t -> t
  | _ -> failwith "Called temp_of_operand on a non-temp 3AS operand."
;;

(** [arg_position_to_used f] returns an array [used_mapping]; 
    [used_mapping[i]] indicates whether function argument at position [i] was 
    used in the function body. *)
let arg_position_to_used (f : ThreeAS.func) =
  let signature, body = f in
  let args = signature.args in
  let n_args = List.length args in
  let args_defined = Hashtbl.create ~growth_allowed:true ~size:n_args (module Temp) in
  let is_defined t = Hashtbl.mem args_defined t in
  let args_used = Hashtbl.create ~growth_allowed:true ~size:n_args (module Temp) in
  let is_used t = Hashtbl.mem args_used t in
  List.iter args ~f:(fun arg ->
    Hashtbl.set args_defined ~key:(temp_of_operand arg) ~data:());
  let mark_operand_if_defined op =
    if is_temp op
       && op |> temp_of_operand |> is_used |> not
       && op |> temp_of_operand |> is_defined
    then Hashtbl.set args_used ~key:(op |> temp_of_operand) ~data:()
  in
  let mark_args_as_used (instr : ThreeAS.instr) =
    match instr with
    | Binop { dest; lhs; rhs; _ } ->
      mark_operand_if_defined lhs;
      mark_operand_if_defined rhs;
      mark_operand_if_defined dest
    | Mov { dest; src } ->
      mark_operand_if_defined dest;
      mark_operand_if_defined src
    | Cmp { lhs; rhs } ->
      mark_operand_if_defined lhs;
      mark_operand_if_defined rhs
    | CallF { dest; args; _ } ->
      mark_operand_if_defined dest;
      List.iter args ~f:mark_operand_if_defined
    | _ -> ()
  in
  List.iter body ~f:mark_args_as_used;
  let used_mapping = Array.create ~len:n_args false in
  List.iteri args ~f:(fun i arg ->
    if arg |> temp_of_operand |> is_used then Array.set used_mapping i true);
  used_mapping
;;

(* TODO: This should come BEFORE ssa. *)
let filter_args (program : ThreeAS.program) =
  (* First, produce mapping from ALL function names to their used_mappings *)
  let n_funcs = List.length program in
  let name_to_used_mapping =
    Hashtbl.create ~growth_allowed:false ~size:n_funcs (module String)
  in
  List.iter program ~f:(fun func ->
    Hashtbl.set
      name_to_used_mapping
      ~key:(fst func).ident
      ~data:(arg_position_to_used func));
  (* Helper function to apply to each function *)
  let filter_args_helper (func : ThreeAS.func) : ThreeAS.func =
    let signature, body = func in
    let used_mapping = Hashtbl.find_exn name_to_used_mapping signature.ident in
    let new_args = List.filteri signature.args ~f:(fun i _ -> Array.get used_mapping i) in
    let replace_call_args (instr : ThreeAS.instr) =
      match instr with
      | CallF { dest; ident; args; assign_res } ->
        (match Hashtbl.find name_to_used_mapping ident with
         (* If a function is not in the mapping, it means it was defined 
            outside of the program (library function).*)
         | None -> instr
         | Some callee_used_mapping ->
           let callee_new_args =
             List.filteri args ~f:(fun i _ -> Array.get callee_used_mapping i)
           in
           ThreeAS.CallF { dest; ident; args = callee_new_args; assign_res })
      | _ -> instr
    in
    let new_body = List.map body ~f:replace_call_args in
    { signature with args = new_args }, new_body
  in
  (* Apply helper to every function in the program. *)
  List.map program ~f:(fun func -> filter_args_helper func)
;;
