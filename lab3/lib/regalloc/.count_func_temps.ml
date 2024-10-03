(* L1 Compiler
 * Converts from finalassem into liveness json
 * Parses the input in reverse
 * Follow the algorithm from recitation
 * Implementation: Read the readme.md for documentation
 *)

open Core
module AS = Assem

(* Created modules to simplify functions *)
module OperandSet = Type_modules.OperandSet

let count_temp_line ~(curr : AS.instr) ~(op_set : OperandSet.t) : OperandSet.t =
  match curr with
  | AS.Binop { src; dest; _ } ->
    let added_src =
      match src with
      | AS.Temp _ -> OperandSet.add op_set src
      | _ -> op_set
    in
    (match dest with
     | AS.Temp _ -> OperandSet.add added_src src
     | _ -> added_src)
  | AS.Unop { src; _ } ->
    (match src with
     | AS.Temp _ -> OperandSet.add op_set src
     | _ -> op_set)
  | AS.Cmp { lhs; rhs } ->
    let added_lhs =
      match lhs with
      | AS.Temp _ -> OperandSet.add op_set lhs
      | _ -> op_set
    in
    (match rhs with
     | AS.Temp _ -> OperandSet.add added_lhs rhs
     | _ -> added_lhs)
  | AS.Mov { dest; src; _ } ->
    let added_src =
      match src with
      | AS.Temp _ -> OperandSet.add op_set src
      | _ -> op_set
    in
    (match dest with
     | AS.Temp _ -> OperandSet.add added_src src
     | _ -> added_src)
  | AS.Nullop _ | AS.Directive _ | AS.Comment _ | AS.Label _ | AS.Jmp _ | AS.Jc _ | AS.Ret
    -> op_set
  | AS.Test { lhs; rhs } ->
    let added_lhs =
      match lhs with
      | AS.Temp _ -> OperandSet.add op_set lhs
      | _ -> op_set
    in
    (match rhs with
     | AS.Temp _ -> OperandSet.add added_lhs rhs
     | _ -> added_lhs)
  | AS.Call { args; _ } ->
    List.fold_left args ~init:op_set ~f:(fun acc arg ->
      match arg with
      | AS.Temp _ -> OperandSet.add acc arg
      | _ -> acc)
;;

let count_temps ~(func : AS.func) : int =
  let lines = snd func in
  let temp_count =
    List.fold_left lines ~init:OperandSet.empty ~f:(fun op_set curr ->
      count_temp_line ~curr ~op_set)
  in
  OperandSet.length temp_count
;;
