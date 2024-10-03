(* L1 Compiler
 * Instruction Selection.
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Returns the set of a function's arguments that are call clobbered.
 *)
open Core
module ThreeAS = Threeaddrassem

(** [line_of_first_call body] is the line number (0-indexed) of the first call 
instruction in body. 
If there are no functions called, it returns [Int.max_value]. *)
let line_of_first_call (body : ThreeAS.body) =
  match
    List.findi body ~f:(fun _ instr ->
      match instr with
      | CallF _ -> true
      | _ -> false)
  with
  | Some (line_number, _) -> line_number
  | None -> Int.max_value
;;

(* Div and mod overwrite edx. *)
let line_of_first_div_mod (body : ThreeAS.body) =
  match
    List.findi body ~f:(fun _ instr ->
      match instr with
      | Binop { op; _ } ->
        (match op with
         | Div | Mod -> true
         | _ -> false)
      | _ -> false)
  with
  | Some (line_number, _) -> line_number
  | None -> Int.max_value
;;

(* Shifts overwrite ecx. *)
let line_of_first_shift (body : ThreeAS.body) =
  match
    List.findi body ~f:(fun _ instr ->
      match instr with
      | Binop { op; _ } ->
        (match op with
         | Sal | Sar -> true
         | _ -> false)
      | _ -> false)
  with
  | Some (line_number, _) -> line_number
  | None -> Int.max_value
;;

(** [non_call_clobbered_args args body] is a Hashtbl that maps all non-call-
    clobbered arguments to their arg position. *)
let non_call_clobbered_args args body =
  let defined_args =
    Hashtbl.create ~growth_allowed:false ~size:(List.length args) (module Temp)
  in
  let number_of_lines = List.length body in
  (* If there is control flow, just assume all args are call clobbered*)
  match
    List.find
      ~f:(fun instr ->
        match instr with
        | ThreeAS.JumpC _ | Jump _ -> true
        | _ -> false)
      body
  with
  | Some _ -> defined_args
  | None ->
    (* Add all defined args and their position. *)
    List.iteri args ~f:(fun i arg ->
      match arg with
      | ThreeAS.Temp t -> Hashtbl.set defined_args ~key:t ~data:i
      | _ -> failwith "Arg can't contain non-temps in 3AS");
    let arg_to_last_line =
      Hashtbl.create ~growth_allowed:false ~size:(List.length args) (module Temp)
    in
    let extract_temp line_number operand =
      match operand with
      (* Keep temps only if they are arguments and are not already recorded.
       Save the line number as number_of_lines - line_number - 1. *)
      | ThreeAS.Temp t ->
        if Hashtbl.mem defined_args t && not (Hashtbl.mem arg_to_last_line t)
        then Hashtbl.set arg_to_last_line ~key:t ~data:(number_of_lines - line_number - 1)
      | _ -> ()
    in
    (* Find the last time the temp is REFERENCED. *)
    List.iteri (List.rev body) ~f:(fun i instr ->
      match instr with
      | ThreeAS.Binop { lhs; rhs; _ } ->
        extract_temp i lhs;
        extract_temp i rhs
      | Mov { src; _ } -> extract_temp i src
      | Cmp { lhs; rhs } ->
        extract_temp i lhs;
        extract_temp i rhs
      | Ret { src } -> extract_temp i src
      | CallF { args; _ } -> List.iter args ~f:(extract_temp i)
      | _ -> ());
    let n_first_call = line_of_first_call body in
    let n_first_div_mod = line_of_first_div_mod body in
    let n_first_shift = line_of_first_shift body in
    (* Return non-call-clobbered args. *)
    Hashtbl.filteri defined_args ~f:(fun ~key:arg ~data:arg_number ->
      match Hashtbl.find arg_to_last_line arg, arg_number with
      (* Not call clobbered if call is the first time they are referenced.*)
      (* For edx, last reference has to be before any calls and any divmods*)
      | Some last_reference, 2 ->
        last_reference <= n_first_call && last_reference < n_first_div_mod
      (* For ecx, last reference has to be before any shifts *)
      | Some last_reference, 3 ->
        last_reference <= n_first_call && last_reference < n_first_shift
      (* For the other arguments, they just need to be before any calls*)
      | Some last_reference, _ -> last_reference <= n_first_call
      (* If they are never referenced in the function, then they are not call clobbered*)
      | None, _ -> true)
;;
