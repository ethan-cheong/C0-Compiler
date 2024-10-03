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

(* Comparison types, used in conditional jumps *)
type comparison =
  | L
  | Le
  | G
  | Ge
  | E
  | Ne

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Reg of reg
  (* offset(reg) *)
  | Ref of
      { offset : Int32.t
      ; reg : reg
      }
  | Label of string

type word_size =
  | L
  | Q

type two_address_operator =
  | Add
  | Sub
  | IMul
  | Mov
  | Sal
  | Sar
  | Xor
  | And
  | Or

type one_address_operator =
  | IDiv
  | Pop
  | Push

type zero_address_operator = Cltd

type instr =
  (* op^word_size src, dest *)
  | Binop of
      { op : two_address_operator
      ; word_size : word_size
      ; src : operand
      ; dest : operand
      }
  (* op^word_size src *)
  | Unop of
      { op : one_address_operator
      ; word_size : word_size
      ; src : operand
      }
  (* op *)
  | Nullop of { op : zero_address_operator }
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string
  | Ret
  (* cmp lhs, rhs *)
  | Cmp of
      { lhs : operand
      ; rhs : operand
      }
  (* test lhs, rhs*)
  | Test of
      { lhs : operand
      ; rhs : operand
      }
  (* j^cmp label*)
  | Jc of
      { cmp : comparison
      ; label : operand
      }
  (* jmp label*)
  | Jmp of { label : operand }
  (* Label: *)
  | Label of string

(* Converts abstract assembly operands to final operands *)
val final_of_operand : Assem.operand -> operand
val final_of_comparison : Assem.comparison -> comparison

(* Converts representation of assembly into string containing final assembly
   [Example use] : Binop {op = Add; dest = Reg EAX; src = 5} -> "add eax, 4"*)
val format : instr -> string
