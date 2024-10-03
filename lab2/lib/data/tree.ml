(* L1 Compiler
 * IR Trees
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Modified: Ethan Cheong <echeong@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

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

type label = string * int

type cmd =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Binop_impure of
      { lhs : exp
      ; op : binop_impure
      ; rhs : exp
      ; dest : Temp.t
      }
  | Function (* as of lab 2, unclear about what this rep should be *)
  | If of
      { condition : exp
      ; lt : label
      ; lf : label
      }
  | Goto of label
  | Label of label
  | Return of exp

type program = cmd list

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
  ;;

  let pp_label (descr, id) = Printf.sprintf "%s_%d" descr id

  let pp_cmd = function
    | Move mv -> Temp.name mv.dest ^ "  <--  " ^ pp_exp mv.src
    | Return e -> "return " ^ pp_exp e
    | Binop_impure { lhs; op; rhs; dest } ->
      Printf.sprintf
        "%s <-- %s %s %s"
        (Temp.name dest)
        (pp_exp lhs)
        (pp_binop_impure op)
        (pp_exp rhs)
    | Function -> "As of lab 2, functions are not supported"
    | If { condition; lt; lf } ->
      Printf.sprintf
        "if %s then %s else %s"
        (pp_exp condition)
        (pp_label lt)
        (pp_label lf)
    | Goto label -> Printf.sprintf "goto %s" (pp_label label)
    | Label label -> Printf.sprintf "%s:" (pp_label label)
  ;;

  (* | Binop_impure of
      { lhs : exp
      ; op : binop_impure
      ; rhs : exp
      ; dest : Temp.t
      }
  | Function (* as of lab 2, unclear about what this rep should be *)
  | If of
      { lhs : exp
      ; op : binop_cmp
      ; rhs : exp
      ; lt : label
      ; lf : label
      }
  | Goto of label
  | Label of label *)

  let rec pp_program = function
    | [] -> ""
    | cmd :: cmds -> pp_cmd cmd ^ "\n" ^ pp_program cmds
  ;;
end
