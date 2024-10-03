(* L1 Compiler
 * Three Address Assembly language
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps
 *)

open Core

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Temp of Temp.t

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
      ; ident : string
      ; args : operand list
      ; assign_res : bool
      }

type body = instr list

type signature =
  { ident : string (* Name of function block *)
  ; args : operand list (* function args *)
  ; tail_rec : bool
  ; num_temps : int
  }

type func = signature * body
type program = func list

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
  | Lt -> "l"
  | Leq -> "le"
  | Gt -> "g"
  | Geq -> "ge"
  | Eq -> "e"
  | Neq -> "ne"
;;

let format_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | MAX_INT -> "$0xFFFFFFFF"
  | Temp t -> Temp.name t
;;

let format_args arg_list =
  let string_list = List.map arg_list ~f:format_operand in
  "(" ^ String.concat ~sep:", " string_list ^ ")"
;;

let format_instr = function
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
  | JumpC { cmp; label } -> sprintf "j%s %s" (format_comparison cmp) label
  | Jump s -> sprintf "jmp %s" s
  | Ret { src } -> sprintf "ret %s" (format_operand src)
  | CallF { dest; ident; args; _ } ->
    sprintf "%s <-- %s%s" (format_operand dest) ident (format_args args)
;;

let rec format_body = function
  | [] -> ""
  | instr :: instrs -> format_instr instr ^ "\n" ^ format_body instrs
;;

(* Helper function for printing args in function labels *)

let format_arg_list arg_list =
  let string_list =
    List.map arg_list ~f:(fun op ->
      match op with
      | Temp t -> Temp.name t
      | _ -> failwith "3AS args can't contain non-temps!")
  in
  "(" ^ String.concat ~sep:", " string_list ^ ")"
;;

let format_signature { ident; args; tail_rec; num_temps } =
  Printf.sprintf
    "%s%s:%s num_temps:%d"
    ident
    (format_arg_list args)
    (if tail_rec then "[tr]" else "")
    num_temps
;;

let format p =
  List.fold
    (List.map p ~f:(fun (s, b) -> format_signature s ^ "\n" ^ format_body b))
    ~init:""
    ~f:(fun x y -> x ^ "\n" ^ y)
;;
