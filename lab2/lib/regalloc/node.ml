(* L1 Compiler
 * Representation of possible nodes in the interference graph.
 * 
 *)

open Core

(**
We need that the type can take Temps and Regs (except RSP, RBP and R10D)
and convert them into a node type. 
Only regs and temps are valid inputs
*)
module AS = Assem

module T = struct
  type t =
    | Entry of AS.operand
    | Null
  [@@deriving compare, sexp, hash]
end

include T

let null_node () = Null

(* Pattern match to prevent Imms and Refs from returning *)
let node_of_operand (x : AS.operand) : t =
  match x with
  | AS.MAX_INT | AS.Imm _ | AS.Ref _ ->
    failwith "Immediates and Refs not allowed as node values"
  | AS.Label _ -> failwith "Labels not allowed as nodes"
  | AS.Reg x -> Entry (AS.Reg x)
  | AS.Temp x -> Entry (AS.Temp x)
;;

(*
  Only regs and temps are returned. This can return a null.
*)
let operand_of_node (x : t) : AS.operand =
  match x with
  | Entry x -> x
  | Null -> failwith "Tried to get the operand of a null node."
;;

let format_node (x : t) : string =
  match x with
  | Entry x -> AS.format_operand x
  | Null -> "NULL"
;;

let is_register = function
  | Entry e ->
    (match e with
     | AS.Reg _ -> true
     | _ -> false)
  | _ -> false
;;

include Comparable.Make (T)
