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
    | Temp of Temp.t
    | Reg of AS.reg
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
  | AS.Reg { reg; _ } -> Reg reg
  | AS.Temp t -> Temp t
;;

let format_node (x : t) : string =
  match x with
  | Temp t -> Temp.name t
  | Reg r -> AS.format_reg r
  | Null -> "NULL"
;;

(* TODO: Allocate correct size for the reg when converting from node to operand *)
let operand_of_node (x : t) : AS.operand =
  match x with
  | Null -> failwith "no nulls as of yet"
  | Temp t -> AS.Temp t
  | Reg r -> AS.Reg { reg = r; size = AS.DOUBLE }
;;

let is_register = function
  | Reg _ -> true
  | _ -> false
;;

include Comparable.Make (T)
