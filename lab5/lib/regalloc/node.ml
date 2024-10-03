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

(* TODO: store the entire assem operand as node instead.
   Implement our own comparator that uses Assem.compare_reg and only looks 
   at the reg field. (Probably have to implement hash and sexp that only look
   at the reg field as well.)
   For temps, we can use Temp's compare sexp and hash.*)

module T = struct
  type t =
    | Temp of Temp.t
    | Reg of AS.reg
    | Null
    | Dummy of int
  [@@deriving compare, sexp, hash]
end

include T

let null_node () = Null

(* Pattern match to prevent Imms and Refs from returning *)
let node_of_operand (x : AS.operand) : t =
  match x with
  | AS.MAX_INT | AS.Imm _ | AS.Addr_imm _ | AS.Stack_ref _ ->
    failwith "Immediates and Refs not allowed as node values"
  | AS.Reg { reg; _ } -> Reg reg
  | AS.Temp t -> Temp t
;;

let format_node (x : t) : string =
  match x with
  | Temp t -> Temp.name t
  | Reg r -> AS.format_reg r
  | Null -> "NULL"
  | Dummy i -> sprintf "Dummy%s" (string_of_int i)
;;

let is_register = function
  | Reg _ -> true
  | _ -> false
;;

include Comparable.Make (T)
