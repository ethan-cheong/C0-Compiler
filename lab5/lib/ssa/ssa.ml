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
[@@deriving compare, sexp, hash, equal]

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
[@@deriving compare, sexp, hash, equal]

type comparison =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq
[@@deriving compare, sexp, hash, equal]

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
  | Phi of
      { args : operand list
      ; dest : operand
      }
[@@deriving compare, sexp, hash, equal]

type body = instr list

type header =
  { ident : string (* Name of function block *)
  ; args : operand list (* function args *)
  ; from_func : bool
  ; tail_rec : bool
  ; num_temps : int
  ; recursive : bool 
  }

type basic_block = header * body
type t = basic_block list

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
  | Shr -> ">h>"
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
  | Nop -> "Nop "
  | Phi { dest; args } -> sprintf "%s <- Phi%s" (format_operand dest) (format_args args)
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

let format_header { ident; args; tail_rec; num_temps; from_func; _ } =
  Printf.sprintf
    "%s%s:%s%s num_temps:%d"
    ident
    (format_arg_list args)
    (if from_func then "[from_func]" else "")
    (if tail_rec then "[tr]" else "")
    num_temps
;;

let format p =
  List.fold
    (List.map p ~f:(fun (s, b) -> format_header s ^ "\n" ^ format_body b))
    ~init:""
    ~f:(fun x y -> x ^ "\n" ^ y)
;;
