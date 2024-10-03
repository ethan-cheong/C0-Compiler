(* L1 Compiler
 * Naive Assembly language
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *
 * Final representation of assembly before compiler outputs
 *
 *)

open Core

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
  | Cmp of
      { lhs : operand
      ; rhs : operand (* Literally cmp lhs, rhs*)
      }
  | Test of
      { lhs : operand
      ; rhs : operand
      }
  | Jc of
      { cmp : comparison
      ; label : operand
      }
  | Jmp of { label : operand }
  | Label of string

let final_of_reg : Assem.reg -> reg = function
  | EAX -> EAX
  | EBX -> EBX
  | ECX -> ECX
  | EDX -> EDX
  | RSP -> RSP
  | EBP -> EBP
  | ESI -> ESI
  | EDI -> EDI
  | R8D -> R8D
  | R9D -> R9D
  | R10D -> R10D
  | R11D -> R11D
  | R12D -> R12D
  | R13D -> R13D
  | R14D -> R14D
  | R15D -> R15D
;;

let final_of_comparison : Assem.comparison -> comparison = function
  | Lt -> L
  | Leq -> Le
  | Gt -> G
  | Geq -> Ge
  | Eq -> E
  | Neq -> Ne
;;

let final_of_operand = function
  | Assem.MAX_INT -> MAX_INT
  | Assem.Imm i -> Imm i
  | Assem.Reg r -> Reg (final_of_reg r)
  | Assem.Ref { offset = o; reg = r } -> Ref { offset = o; reg = final_of_reg r }
  | Assem.Temp _ -> failwith "Temps not supported in x86 assembly"
  | Assem.Label l -> Label l
;;

let format_word_size = function
  | L -> "l"
  | Q -> "q"
;;

let format_comparison = function
  | Le -> "le"
  | L -> "l"
  | G -> "g"
  | Ge -> "ge"
  | E -> "e"
  | Ne -> "ne"
;;

let format_two_address_operator = function
  | Add -> "add"
  | Sub -> "sub"
  | IMul -> "imul"
  | Mov -> "mov"
  | Sal -> "sal"
  | Sar -> "sar"
  | Xor -> "xor"
  | And -> "and"
  | Or -> "or"
;;

let format_one_address_operator = function
  | IDiv -> "idiv"
  | Push -> "push"
  | Pop -> "pop"
;;

let format_zero_address_operator = function
  | Cltd -> "cltd"
;;

let format_register = function
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

let format_operand = function
  | Imm i -> "$" ^ Int32.to_string i
  | MAX_INT -> "$0xFFFFFFFF"
  | Reg r -> format_register r
  | Ref { offset; reg } -> Int32.to_string offset ^ "(" ^ format_register reg ^ ")"
  | Label s -> s
;;

let format = function
  | Binop { op; word_size; src; dest } ->
    sprintf
      "%s%s\t%s, %s"
      (format_two_address_operator op)
      (format_word_size word_size)
      (format_operand src)
      (format_operand dest)
  | Unop { op; word_size; src } ->
    sprintf
      "%s%s\t%s"
      (format_one_address_operator op)
      (format_word_size word_size)
      (format_operand src)
  | Nullop { op } -> sprintf "%s" (format_zero_address_operator op)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret -> "ret"
  | Cmp { lhs; rhs } -> sprintf "cmp %s, %s" (format_operand lhs) (format_operand rhs)
  | Test { lhs; rhs } -> sprintf "test %s, %s" (format_operand lhs) (format_operand rhs)
  | Jc { cmp; label } -> sprintf "j%s %s" (format_comparison cmp) (format_operand label)
  | Jmp { label } -> sprintf "jmp %s" (format_operand label)
  | Label l -> sprintf "%s:" l
;;
