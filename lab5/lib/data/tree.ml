(* L1 Compiler
 * IR Trees
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)
open Core

type binop_pure =
  | Add
  | Sub
  | Mul
  | Or
  | Xor
  | And

type binop_cmp =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq

type binop_impure =
  | Div
  | Mod
  | Sal
  | Sar

type const =
  | Int of Int32.t
  | MAX_INT

(* Expressions should be pure; they should have no side effects! *)
type exp =
  | Const of const
  | Temp of Temp.t
  | Binop_pure of
      { lhs : exp
      ; op : binop_pure
      ; rhs : exp
      }
  | Binop_cmp of
      { lhs : exp
      ; op : binop_cmp
      ; rhs : exp
      }
  | Addr_const of Int64.t (* 64-bit const used in address arithmetic. *)

type label = string * int

type cmd =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Move_truncate of
      { dest : Temp.t
      ; src : exp
      }
  | Move_sign_extend of
      { dest : Temp.t
      ; src : exp
      }
  | Move_zero_extend of
      { dest : Temp.t
      ; src : exp
      }
  | Binop_impure of
      { lhs : exp
      ; op : binop_impure
      ; rhs : exp
      ; dest : Temp.t
      }
  | Function_call of
      { dest : Temp.t
      ; ident : string (* function name *)
      ; args : exp list
      ; assign_res : bool
      }
  | If of
      { condition : exp
      ; lt : label
      ; lf : label
      }
  | Goto of label
  | Label of label
  | Return of exp
  | Return_void
  | Memory_read of
      { dest : exp
      ; disp : Int32.t
      ; base : exp
      ; index : exp
      ; scale : int
      }
  | Memory_write of
      { src : exp
      ; disp : Int32.t
      ; base : exp
      ; index : exp
      ; scale : int
      }
  | Load_effective_address of
      { dest : exp
      ; disp : Int32.t
      ; base : exp
      ; index : exp
      ; scale : int
      }
  | Comment of string
  | Nop

type body = cmd list

type signature =
  { ident : string (* function name *)
  ; args : exp list (* function args *)
  ; tail_rec : bool
  ; num_temps : int
  ; recursive : bool 
  }

type func = signature * body
type program = func list

module type PRINT = sig
  val pp_exp : exp -> string
  val pp_cmd : cmd -> string
  val pp_program : program -> string
end

module Print : PRINT = struct
  let pp_binop_pure = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Or -> "|"
    | Xor -> "^"
    | And -> "&"
  ;;

  let pp_binop_impure = function
    | Div -> "/"
    | Mod -> "%"
    | Sal -> "<<"
    | Sar -> ">>"
  ;;

  let pp_binop_cmp = function
    | Lt -> "<"
    | Leq -> "<="
    | Gt -> ">"
    | Geq -> ">="
    | Eq -> "=="
    | Neq -> "!="
  ;;

  let pp_const = function
    | Int x -> Int32.to_string x
    | MAX_INT -> "0xFFFFFFFF"
  ;;

  let rec pp_exp = function
    | Const x -> pp_const x
    | Temp t -> Temp.name t
    | Binop_pure binop ->
      Printf.sprintf
        "(%s %s %s)"
        (pp_exp binop.lhs)
        (pp_binop_pure binop.op)
        (pp_exp binop.rhs)
    | Binop_cmp binop ->
      Printf.sprintf
        "(%s %s %s)"
        (pp_exp binop.lhs)
        (pp_binop_cmp binop.op)
        (pp_exp binop.rhs)
    | Addr_const i -> sprintf "addr_const(%s)" (Int64.to_string i)
  ;;

  let pp_label (descr, id) = Printf.sprintf "%s_%d" descr id

  let pp_arg_list arg_list =
    let string_list = List.map arg_list ~f:pp_exp in
    "(" ^ String.concat ~sep:", " string_list ^ ")"
  ;;

  let pp_cmd = function
    | Move mv -> Temp.name mv.dest ^ "  <--  " ^ pp_exp mv.src
    | Move_truncate { src; dest } -> Temp.name dest ^ "  <-trunc-  " ^ pp_exp src
    | Move_sign_extend { src; dest } -> Temp.name dest ^ "  <-sign-ext-  " ^ pp_exp src
    | Move_zero_extend { src; dest } -> Temp.name dest ^ "  <-zero-ext-  " ^ pp_exp src
    | Return e -> "return " ^ pp_exp e
    | Return_void -> "return void"
    | Binop_impure { lhs; op; rhs; dest; _ } ->
      Printf.sprintf
        "%s <-- %s %s %s"
        (Temp.name dest)
        (pp_exp lhs)
        (pp_binop_impure op)
        (pp_exp rhs)
    | Function_call { dest; ident; args; _ } ->
      Printf.sprintf "%s <-- %s%s" (Temp.name dest) ident (pp_arg_list args)
    | If { condition; lt; lf } ->
      Printf.sprintf
        "if %s then %s else %s"
        (pp_exp condition)
        (pp_label lt)
        (pp_label lf)
    | Goto label -> Printf.sprintf "goto %s" (pp_label label)
    | Label label -> Printf.sprintf "%s:" (pp_label label)
    | Memory_read { dest; disp; base; scale; _ } when scale = 0 ->
      Printf.sprintf "%s <- M[%s(%s)]" (pp_exp dest) (Int32.to_string disp) (pp_exp base)
    | Memory_read { dest; disp; base; index; scale } ->
      Printf.sprintf
        "%s <- M[%s(%s, %s, %d)]"
        (pp_exp dest)
        (Int32.to_string disp)
        (pp_exp base)
        (pp_exp index)
        scale
    | Memory_write { src; disp; base; scale; _ } when scale = 0 ->
      Printf.sprintf "M[%s(%s)] <- %s" (Int32.to_string disp) (pp_exp base) (pp_exp src)
    | Memory_write { src; disp; base; index; scale } ->
      Printf.sprintf
        "M[%s(%s, %s, %d)] <- %s"
        (Int32.to_string disp)
        (pp_exp base)
        (pp_exp index)
        scale
        (pp_exp src)
    | Load_effective_address { dest; disp; base; scale; _ } when scale = 0 ->
      Printf.sprintf "%s <-lea- %s(%s)" (pp_exp dest) (Int32.to_string disp) (pp_exp base)
    | Load_effective_address { dest; disp; base; index; scale } ->
      Printf.sprintf
        "%s <-lea- %s(%s, %s, %d)"
        (pp_exp dest)
        (Int32.to_string disp)
        (pp_exp base)
        (pp_exp index)
        scale
    | Comment s -> Printf.sprintf "Comment: " ^ s
    | Nop -> "nop"
  ;;

  let rec pp_body = function
    | [] -> ""
    | cmd :: cmds -> pp_cmd cmd ^ "\n" ^ pp_body cmds
  ;;

  let pp_signature { ident; args; tail_rec; num_temps ; _} =
    Printf.sprintf
      "%s%s:%s num_temps:%d"
      ident
      (pp_arg_list args)
      (if tail_rec then "[tr]" else "")
      num_temps
  ;;

  let pp_program (p : program) =
    List.fold
      (List.map p ~f:(fun (s, b) -> pp_signature s ^ "\n" ^ pp_body b))
      ~init:""
      ~f:(fun x y -> x ^ "\n" ^ y)
  ;;
end
