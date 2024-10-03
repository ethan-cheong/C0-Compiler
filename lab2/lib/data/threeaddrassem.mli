(* L1 Compiler
 * Three Address Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps. 
 *
 *)

(* Representations of the 16 registers available. *)

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Temp of Temp.t
  | Label of string

(* Unary operations (negation, bitwise not) have been converted to their binop
   equivalents after codegen. *)
type operation =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Or
  | Xor
  | And
  | Sal
  | Sar

type comparison =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq

type instr =
  (* dest <- lhs op rhs *)
  | Binop of
      { op : operation
      ; dest : operand
      ; lhs : operand
      ; rhs : operand
      }
  | Mov of
      { dest : operand
      ; src : operand
      }
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string
  | Cmp of
      { lhs : operand
      ; rhs : operand
      }
  (* j(cmp) label *)
  | JumpC of
      { cmp : comparison
      ; label : operand
      }
  (* goto label *)
  | Jump of { label : operand }
  | Label of string
  | Ret of { src : operand }

val format_binop : operation -> string
val format_operand : operand -> string
val format : instr -> string
