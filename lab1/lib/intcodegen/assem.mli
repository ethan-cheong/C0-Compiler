(* L1 Compiler
 * Three Address Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps. Also allows for operands to be references
 *
 *)

type reg =
  | EAX
  | EBX
  | ECX
  | EDX
  | RSP
  | RBP
  | ESI
  | EDI
  | R8D
  | R9D
  | R10D
  | R11D
  | R12D
  | R13D
  | R14D
  | R15D
[@@deriving compare, sexp, hash, equal]

type operand =
  | Imm of Int32.t
  | Reg of reg
  | Temp of Temp.t
  | Ref of
      { offset : Int32.t
      ; reg : reg
      }
[@@deriving compare, sexp, hash, equal]

type operation =
  | Add
  | Sub
  | Mul
  | Div
  | Mod

type instr =
  (* dest <- lhs op rhs *)
  | Binop of
      { op : operation
      ; dest : operand
      ; lhs : operand
      ; rhs : operand
      }
  (* dest <- src *)
  | Mov of
      { dest : operand
      ; src : operand
      }
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string

val format_reg : reg -> string
val format_binop : operation -> string
val format_operand : operand -> string
val format : instr -> string
