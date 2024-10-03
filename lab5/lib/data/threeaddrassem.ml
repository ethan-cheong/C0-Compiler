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
  | Addr_imm of Int64.t
  | Temp of Temp.t
[@@deriving sexp, compare, hash, equal]

type t = operand [@@deriving sexp, compare, hash, equal]

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
  | Shr

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
  | Movsx of
      (* Mov with sign extend*)
      
      { dest : operand
      ; src : operand
      }
  | Movzx of
      (* Mov with zero extend*)
      
      { dest : operand
      ; src : operand
      }
  | Mov_trunc of
      (* Mov from 64 to 32 bit *)
      
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
  | If of
      { lhs : operand
      ; rhs : operand
      ; condition : comparison
      ; lt : string
      ; lf : string
      }
  (* goto label *)
  | Jump of string
  | Label of string
  | Ret of { src : operand }
  | Ret_void
  | CallF of
      { dest : operand
      ; ident : string
      ; args : operand list
      ; assign_res : bool
      }
  | Store of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; src : operand
      }
  | Load of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
  | Lea of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
  | Nop

type body = instr list

type signature =
  { ident : string (* Name of function block *)
  ; args : operand list (* function args *)
  ; tail_rec : bool
  ; num_temps : int
  ; recursive : bool
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
  | Shr -> ">>(h)"
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
  | Imm n -> "$" ^ Int32.to_string n ^ "d"
  | MAX_INT -> "$0xFFFFFFFFd"
  | Temp t -> Temp.name t
  | Addr_imm i -> "$" ^ Int64.to_string i ^ "q"
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
  | Movsx { src; dest } ->
    sprintf "%s <-sx- %s " (format_operand dest) (format_operand src)
  | Movzx { src; dest } ->
    sprintf "%s <-zx- %s " (format_operand dest) (format_operand src)
  | Mov_trunc { src; dest } ->
    sprintf "%s <-trunc- %s " (format_operand dest) (format_operand src)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Cmp { lhs; rhs } -> sprintf "cmp %s %s " (format_operand lhs) (format_operand rhs)
  | Label label -> sprintf "%s:" label
  | If { lhs; rhs; condition; lt; lf } ->
    sprintf
      "if(%s %s %s) then %s else %s"
      (format_operand lhs)
      (format_comparison condition)
      (format_operand rhs)
      lt
      lf
  | Jump s -> sprintf "jmp %s" s
  | Ret { src } -> sprintf "ret %s" (format_operand src)
  | Ret_void -> "ret_void"
  | CallF { dest; ident; args; _ } ->
    sprintf "%s <-- %s%s" (format_operand dest) ident (format_args args)
  | Store { disp; base; scale; src; _ } when scale = 0 ->
    sprintf
      "M[%s(%s)] <-- %s"
      (Int32.to_string disp)
      (format_operand base)
      (format_operand src)
  | Store { disp; base; index; scale; src } ->
    sprintf
      "M[%s(%s, %s, %d)] <-- %s"
      (Int32.to_string disp)
      (format_operand base)
      (format_operand index)
      scale
      (format_operand src)
  | Load { disp; base; scale; dest; _ } when scale = 0 ->
    sprintf
      "%s <-- M[%s(%s)]"
      (format_operand dest)
      (Int32.to_string disp)
      (format_operand base)
  | Load { disp; base; index; scale; dest } ->
    sprintf
      "%s <-- M[%s(%s, %s, %d)]"
      (format_operand dest)
      (Int32.to_string disp)
      (format_operand base)
      (format_operand index)
      scale
  | Lea { disp; base; scale; dest; _ } when scale = 0 ->
    sprintf
      "%s <-lea- %s(%s)"
      (format_operand dest)
      (Int32.to_string disp)
      (format_operand base)
  | Lea { disp; base; index; scale; dest } ->
    sprintf
      "%s <-lea- %s(%s, %s, %d)"
      (format_operand dest)
      (Int32.to_string disp)
      (format_operand base)
      (format_operand index)
      scale
  | Nop -> "Nop"
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

let format_signature { ident; args; tail_rec; num_temps; _ } =
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

(* Conversion to and from SSA *)
let operand_to_ssa = function
  | Imm i -> Ssa.Imm i
  | MAX_INT -> Ssa.MAX_INT
  | Addr_imm i -> Ssa.Addr_imm i
  | Temp t -> Ssa.Temp t
;;

let operand_of_ssa = function
  | Ssa.Imm i -> Imm i
  | MAX_INT -> MAX_INT
  | Addr_imm i -> Addr_imm i
  | Temp t -> Temp t
;;

let operation_to_ssa = function
  | Add -> Ssa.Add
  | Sub -> Sub
  | Mul -> Mul
  | Div -> Div
  | Mod -> Mod
  | Or -> Or
  | Xor -> Xor
  | And -> And
  | Sal -> Sal
  | Sar -> Sar
  | Shr -> Shr
;;

let operation_of_ssa = function
  | Ssa.Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | Div -> Div
  | Mod -> Mod
  | Or -> Or
  | Xor -> Xor
  | And -> And
  | Sal -> Sal
  | Sar -> Sar
  | Shr -> Shr
;;

let comparison_to_ssa = function
  | Lt -> Ssa.Lt
  | Leq -> Leq
  | Gt -> Gt
  | Geq -> Geq
  | Eq -> Eq
  | Neq -> Neq
;;

let comparison_of_ssa = function
  | Ssa.Lt -> Lt
  | Leq -> Leq
  | Gt -> Gt
  | Geq -> Geq
  | Eq -> Eq
  | Neq -> Neq
;;

let instr_to_ssa = function
  | Binop { op; dest; lhs; rhs } ->
    Ssa.Binop
      { op = operation_to_ssa op
      ; dest = operand_to_ssa dest
      ; lhs = operand_to_ssa lhs
      ; rhs = operand_to_ssa rhs
      }
  | Mov { dest; src } -> Mov { dest = operand_to_ssa dest; src = operand_to_ssa src }
  | Movsx { dest; src } ->
    Ssa.Movsx { dest = operand_to_ssa dest; src = operand_to_ssa src }
  | Movzx { dest; src } ->
    Ssa.Movzx { dest = operand_to_ssa dest; src = operand_to_ssa src }
  | Mov_trunc { dest; src } ->
    Ssa.Mov_trunc { dest = operand_to_ssa dest; src = operand_to_ssa src }
  | Directive s -> Directive s
  | Comment s -> Comment s
  | Cmp { lhs; rhs } -> Cmp { lhs = operand_to_ssa lhs; rhs = operand_to_ssa rhs }
  | If { lhs; rhs; condition; lt; lf } ->
    If
      { lhs = operand_to_ssa lhs
      ; rhs = operand_to_ssa rhs
      ; condition = comparison_to_ssa condition
      ; lt
      ; lf
      }
  | Jump s -> Jump s
  | Label s -> Label s
  | Ret { src } -> Ret { src = operand_to_ssa src }
  | Ret_void -> Ret_void
  | CallF { dest; ident; args; assign_res } ->
    CallF
      { dest = operand_to_ssa dest
      ; ident
      ; args = List.map args ~f:operand_to_ssa
      ; assign_res
      }
  | Store { disp; base; index; scale; src } ->
    Store
      { disp
      ; base = operand_to_ssa base
      ; index = operand_to_ssa index
      ; scale
      ; src = operand_to_ssa src
      }
  | Load { disp; base; index; scale; dest } ->
    Load
      { disp
      ; base = operand_to_ssa base
      ; index = operand_to_ssa index
      ; scale
      ; dest = operand_to_ssa dest
      }
  | Lea { disp; base; index; scale; dest } ->
    Lea
      { disp
      ; base = operand_to_ssa base
      ; index = operand_to_ssa index
      ; scale
      ; dest = operand_to_ssa dest
      }
  | Nop -> Nop
;;

let instr_of_ssa = function
  | Ssa.Binop { op; dest; lhs; rhs } ->
    Binop
      { op = operation_of_ssa op
      ; dest = operand_of_ssa dest
      ; lhs = operand_of_ssa lhs
      ; rhs = operand_of_ssa rhs
      }
  | Mov { dest; src } -> Mov { dest = operand_of_ssa dest; src = operand_of_ssa src }
  | Movsx { dest; src } -> Movsx { dest = operand_of_ssa dest; src = operand_of_ssa src }
  | Movzx { dest; src } -> Movzx { dest = operand_of_ssa dest; src = operand_of_ssa src }
  | Mov_trunc { dest; src } ->
    Mov_trunc { dest = operand_of_ssa dest; src = operand_of_ssa src }
  | Directive s -> Directive s
  | Comment s -> Comment s
  | Cmp { lhs; rhs } -> Cmp { lhs = operand_of_ssa lhs; rhs = operand_of_ssa rhs }
  | If { lhs; rhs; condition; lt; lf } ->
    If
      { lhs = operand_of_ssa lhs
      ; rhs = operand_of_ssa rhs
      ; condition = comparison_of_ssa condition
      ; lt
      ; lf
      }
  | Jump s -> Jump s
  | Label s -> Label s
  | Ret { src } -> Ret { src = operand_of_ssa src }
  | Ret_void -> Ret_void
  | CallF { dest; ident; args; assign_res } ->
    CallF
      { dest = operand_of_ssa dest
      ; ident
      ; args = List.map args ~f:operand_of_ssa
      ; assign_res
      }
  | Store { disp; base; index; scale; src } ->
    Store
      { disp
      ; base = operand_of_ssa base
      ; index = operand_of_ssa index
      ; scale
      ; src = operand_of_ssa src
      }
  | Load { disp; base; index; scale; dest } ->
    Load
      { disp
      ; base = operand_of_ssa base
      ; index = operand_of_ssa index
      ; scale
      ; dest = operand_of_ssa dest
      }
  | Lea { disp; base; index; scale; dest } ->
    Lea
      { disp
      ; base = operand_of_ssa base
      ; index = operand_of_ssa index
      ; scale
      ; dest = operand_of_ssa dest
      }
  | Nop -> Nop
  | Phi _ -> failwith "no phi functions should be found when going back to threeas"
;;

let body_to_ssa body = List.map body ~f:instr_to_ssa
let body_of_ssa body = List.map body ~f:instr_of_ssa

let signature_to_ssa { ident; args; tail_rec; num_temps; recursive } =
  Ssa.
    { ident
    ; args = List.map args ~f:operand_to_ssa
    ; from_func = true
    ; tail_rec
    ; num_temps
    ; recursive
    }
;;
