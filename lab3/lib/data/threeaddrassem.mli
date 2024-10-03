(* L1 Compiler
 * Three Address Assembly language
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps. Also allows for operands to be references
 *
 *)

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Temp of Temp.t

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
      ; label : string
      }
  (* goto label *)
  | Jump of string
  | Label of string
  | Ret of { src : operand }
  | CallF of
      { dest : operand
      ; ident : string (* These are the actual function labels.*)
      ; args : operand list
      ; assign_res : bool
      }

type body = instr list

type signature =
  { ident : string (* Name of function block *)
  ; args : operand list (* function args (temps) that are in scope in the function. *)
  ; tail_rec : bool (* Whether the function is tail recursive. *)
  ; num_temps : int (* Number of temps used in the function body *)
  }

type func = signature * body
type program = func list

val format_binop : operation -> string
val format_operand : operand -> string
val format_instr : instr -> string
val format : program -> string
