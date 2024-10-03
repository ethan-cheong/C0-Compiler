(* L5 Compiler
 * Peephole optimizations
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>
 * Adapted from 15-411 lecture notes on peephole optimizations
 *)
open Core

let constant_folding (body : Ssa.instr list) =
  List.map body ~f:(fun instr ->
    match instr with
    (* If result raises arithmetic exception, don't do anything; pattern match. *)
    | Binop { op = Div; rhs = Imm z; _ } when Int32.(z = zero) -> instr
    | Binop { op = Mod; rhs = Imm z; _ } when Int32.(z = zero) -> instr
    | Binop { op = Sal; rhs = Imm s; _ } when Int32.(s > of_int_exn 31) -> instr
    | Binop { op = Sar; rhs = Imm s; _ } when Int32.(s > of_int_exn 31) -> instr
    | Binop { op = Shr; rhs = Imm s; _ } when Int32.(s > of_int_exn 31) -> instr
    | Binop { op; lhs = Imm l; rhs = Imm r; dest } ->
      (match op with
       | Add -> Mov { dest; src = Imm Int32.(l + r) }
       | Sub -> Mov { dest; src = Imm Int32.(l - r) }
       | Mul -> Mov { dest; src = Imm Int32.(l * r) }
       | Div -> Mov { dest; src = Imm Int32.(l / r) }
       | Mod -> Mov { dest; src = Imm Int32.(l % r) }
       | Or -> Mov { dest; src = Imm Int32.(l lor r) }
       | Xor -> Mov { dest; src = Imm Int32.(l lxor r) }
       | And -> Mov { dest; src = Imm Int32.(l land r) }
       | Sal -> Mov { dest; src = Imm Int32.(l lsl to_int_exn r) }
       | Sar -> Mov { dest; src = Imm Int32.(l asr to_int_exn r) }
       | Shr -> Mov { dest; src = Imm Int32.(l lsr to_int_exn r) })
    (* Rewrite conditionals *)
    | If { lhs = Imm l; rhs = Imm r; condition; lt; lf } ->
      (match condition with
       | Lt -> if Int32.(l < r) then Jump lt else Jump lf
       | Leq -> if Int32.(l <= r) then Jump lt else Jump lf
       | Gt -> if Int32.(l > r) then Jump lt else Jump lf
       | Geq -> if Int32.(l >= r) then Jump lt else Jump lf
       | Eq -> if Int32.(l = r) then Jump lt else Jump lf
       | Neq -> if Int32.(l <> r) then Jump lt else Jump lf)
    | _ -> instr)
;;

let run_peephole (cfg_orig, root_orig, label_to_bodies, labels_in_order) =
  let new_label_to_bodies = Hashtbl.map label_to_bodies ~f:constant_folding in
  cfg_orig, root_orig, new_label_to_bodies, labels_in_order
;;
