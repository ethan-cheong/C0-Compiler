(* L1 Compiler
 * Representation of possible nodes in the interference graph.
 * 
 *)

open Core

type t [@@deriving compare, sexp, hash]

include Comparable.S with type t := t

(** Return the null node (AKA mark that the node in the graph couldn't be coloured *)
val null_node : unit -> t

(**
    We need that the type can take Temps and Regs (except RSP, RBP and R10D)
    and convert them into a node type. 
    Only regs and temps are valid inputs
*)

val node_of_operand : Assem.operand -> t

(*
   Only regs and temps are returned.
   *)

val operand_of_node : t -> Assem.operand
val format_node : t -> string

(** Returns true iff a Node is a register. *)
val is_register : t -> bool
