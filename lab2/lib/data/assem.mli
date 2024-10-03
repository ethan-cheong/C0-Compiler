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

(* Representations of the 16 registers available. *)
type reg =
  | EAX
  | EBX
  | ECX
  | EDX
  | RSP
  | EBP
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
  | MAX_INT
  | Reg of reg
  | Temp of Temp.t
  | Ref of
      { offset : Int32.t
      ; reg : reg
      }
  | Label of string
[@@deriving compare, sexp, hash, equal]

(* This is used to indicate to the register allocator whether the instruction
   was originally a div or a mod. *)
type div_type =
  | Div
  | Mod
  | NotDiv (* Used for unops only *)

type two_addr_op =
  | Add
  | Sub
  | IMul
  | Sal
  | Sar
  | Xor
  | And
  | Or

type one_addr_op =
  | IDiv
  | Pop
  | Push

type zero_addr_op = Cltd

type comparison =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq

type instr =
  | Unop of
      { op : one_addr_op
      ; src : operand
      ; div_type : div_type
      }
  | Nullop of { op : zero_addr_op }
  | Binop of
      { op : two_addr_op
      ; src : operand
      ; dest : operand
      }
    (* dest <- src *)
  | Mov of
      { dest : operand
      ; src : operand
      }
  | Test of
      { lhs : operand
      ; rhs : operand
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
  | Ret

val operand_of_three_addr_operand : Threeaddrassem.operand -> operand
val cmp_of_three_addr_cmp : Threeaddrassem.comparison -> comparison
val format_reg : reg -> string
val format_operand : operand -> string
val format : instr -> string
