(* L1 Compiler
 * Naive Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Final representation of assembly before compiler outputs
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

type operand =
  | Imm of Int32.t
  | Reg of reg
  | Ref of
      { offset : Int32.t
      ; reg : reg
      }

type word_size =
  | L
  | Q

type two_address_operator =
  | Add
  | Sub
  | IMul
  | Mov

type one_address_operator =
  | IDiv
  | Pop
  | Push

type zero_address_operator = Cltd

type instr =
  (* dest <- lhs op rhs *)
  | Binop of
      { op : two_address_operator
      ; word_size : word_size
      ; src : operand
      ; dest : operand
      }
  | Unop of
      { op : one_address_operator
      ; word_size : word_size
      ; src : operand
      }
  | Nullop of { op : zero_address_operator }
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string
  | Ret

(* Converts abstract assembly operands to final operands *)
val final_of_operand : Assem.operand -> operand

(* Converts representation of assembly into string containing final assembly
   [Example use] : Binop {op = Add; dest = Reg EAX; src = 5} -> "add eax, 4"*)
val format : instr -> string
