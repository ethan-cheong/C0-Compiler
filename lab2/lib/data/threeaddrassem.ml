(* L1 Compiler
 * Three Address Assembly language
 * 
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps
 *)

open Core

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Temp of Temp.t
  | Label of string

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

(* functions that format assembly output *)

let format_binop : operation -> string = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Or -> "|"
  | Xor -> "^"
  | And -> "&"
  | Sal -> "<<"
  | Sar -> ">>"
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
  | Label l -> l
;;

let format = function
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (format_operand binop.dest)
      (format_operand binop.lhs)
      (format_binop binop.op)
      (format_operand binop.rhs)
  | Mov mv -> sprintf "%s <-- %s" (format_operand mv.dest) (format_operand mv.src)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Cmp { lhs; rhs } -> sprintf "cmp %s %s " (format_operand lhs) (format_operand rhs)
  | Label label -> sprintf "%s:" label
  | JumpC { cmp; label } ->
    sprintf "jumpc%s %s" (format_comparison cmp) (format_operand label)
  | Jump { label } -> sprintf "jump %s" (format_operand label)
  | Ret { src } -> sprintf "ret %s" (format_operand src)
;;
