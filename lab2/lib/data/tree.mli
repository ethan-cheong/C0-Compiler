(* L1 Compiler
 * IR Trees
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

(* pure binary operations. Or, Xor and And are bitwise operations. *)
type binop_pure =
  | Add
  | Sub
  | Mul
  | Or
  | Xor
  | And

(* These are also pure, but we treat them differently in translation *)
type binop_cmp =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq

(* Operations that are impure because they may throw an exception. *)
type binop_impure =
  | Div
  | Mod
  | Sal
  | Sar

(* MAX_INT is added to represent 0xFFFFFFFF. At this stage, all booleans are 
   represented as Int(0) or Int(1). *)
type const =
  | Int of Int32.t
  | MAX_INT

(* Expressions should be pure; they should have no side effects! *)
type exp =
  | Const of const
  | Temp of Temp.t
  | Binop_pure of
      { lhs : exp
      ; op : binop_pure
      ; rhs : exp
      }
  | Binop_cmp of
      { lhs : exp
      ; op : binop_cmp
      ; rhs : exp
      }

(* descr * id *)
type label = string * int

type cmd =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Binop_impure of
      { lhs : exp
      ; op : binop_impure
      ; rhs : exp
      ; dest : Temp.t
      }
  | Function (* as of lab 2, unclear about what this rep should be *)
  | If of
      { condition : exp
      ; lt : label
      ; lf : label
      }
  | Goto of label
  | Label of label
  | Return of exp

type program = cmd list

module Print : sig
  val pp_exp : exp -> string
  val pp_cmd : cmd -> string
  val pp_program : program -> string
end
