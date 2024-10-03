(* L1 Compiler
 * Three Address Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps
 *)

open Core
module ThreeAS = Threeaddrassem

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

type div_type =
  | Div
  | Mod
  | NotDiv

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

(* functions that format assembly output *)

let operand_of_three_addr_operand : ThreeAS.operand -> operand = function
  | ThreeAS.Imm x -> Imm x
  | ThreeAS.MAX_INT -> MAX_INT
  | ThreeAS.Temp t -> Temp t
  | ThreeAS.Label s -> Label s
;;

let cmp_of_three_addr_cmp : ThreeAS.comparison -> comparison = function
  | ThreeAS.Lt -> Lt
  | ThreeAS.Leq -> Leq
  | ThreeAS.Gt -> Gt
  | ThreeAS.Geq -> Geq
  | ThreeAS.Eq -> Eq
  | ThreeAS.Neq -> Neq
;;

let format_reg = function
  | EAX -> "%eax"
  | EBX -> "%ebx"
  | ECX -> "%ecx"
  | EDX -> "%edx"
  | RSP -> "%rsp"
  | EBP -> "%ebp"
  | ESI -> "%esi"
  | EDI -> "%edi"
  | R8D -> "%r8d"
  | R9D -> "%r9d"
  | R10D -> "%r10d"
  | R11D -> "%r11d"
  | R12D -> "%r12d"
  | R13D -> "%r13d"
  | R14D -> "%r14d"
  | R15D -> "%r15d"
;;

let format_two_addr_op : two_addr_op -> string = function
  | Add -> "add"
  | Sub -> "sub"
  | IMul -> "imul"
  | Sal -> "sal"
  | Sar -> "sar"
  | Xor -> "xor"
  | And -> "and"
  | Or -> "or"
;;

let format_one_addr_op : one_addr_op -> string = function
  | IDiv -> "idiv"
  | Push -> "push"
  | Pop -> "pop"
;;

let format_zero_addr_op : zero_addr_op -> string = function
  | Cltd -> "cltd"
;;

let format_comparison = function
  | Lt -> "<"
  | Leq -> "<="
  | Gt -> ">"
  | Geq -> ">="
  | Eq -> "=="
  | Neq -> "!="
;;

let format_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | MAX_INT -> "$0xFFFFFFFF"
  | Temp t -> Temp.name t
  | Reg r -> format_reg r
  | Ref { offset; reg } -> Int32.to_string offset ^ "(" ^ format_reg reg ^ ")"
  | Label l -> l
;;

let format = function
  | Mov mv -> sprintf "%s <-- %s" (format_operand mv.dest) (format_operand mv.src)
  | Binop { op; src; dest } ->
    sprintf
      "%s\t%s, %s"
      (format_two_addr_op op)
      (format_operand src)
      (format_operand dest)
  | Unop { op; src; _ } -> sprintf "%s\t%s" (format_one_addr_op op) (format_operand src)
  | Nullop { op; _ } -> sprintf "%s" (format_zero_addr_op op)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Cmp { lhs; rhs } -> sprintf "cmp %s %s " (format_operand lhs) (format_operand rhs)
  | Test { lhs; rhs } -> sprintf "test %s, %s" (format_operand lhs) (format_operand rhs)
  | Label label -> sprintf "%s:" label
  | JumpC { cmp; label } ->
    sprintf "jumpc%s %s" (format_comparison cmp) (format_operand label)
  | Jump { label } -> sprintf "jump %s" (format_operand label)
  | Ret -> "ret"
;;
