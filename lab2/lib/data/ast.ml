(* L1 Compiler
 * Unelaborated Abstract Syntax Trees
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

open Core

type binop_pure =
  | Plus
  | Minus
  | Times
  | Bitwise_or
  | Bitwise_xor
  | Bitwise_and

type binop_impure =
  | Divided_by
  | Modulo
  | Left_shift
  | Right_shift

type cmp_binop =
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | Equal
  | Not_equal

type unop =
  | Negative
  | Bitwise_not
  | Not

type tau =
  | Int
  | Bool

(* Notice that the subexpressions of an expression are marked.
 * (That is, the subexpressions are of type exp Mark.t, not just
 * type exp.) This means that source code location (a src_span) is
 * associated with the subexpression. Currently, the typechecker uses
 * this source location to print more helpful error messages.
 *
 * It's the parser and lexer's job to associate src_span locations with each
 * ast. It's instructive, but not necessary, to closely read the source code
 * for c0_parser.mly, c0_lexer.mll, and parse.ml to get a good idea of how
 * src_spans are created.
 *
 * Check out the Mark module for ways of converting a marked expression into
 * the original expression or to the src_span location. You could also just
 * look at how the typechecker gets the src_span from an expression when it
 * prints error messages.
 *
 * It's completely possible to remove Marks entirely from your compiler, but
 * it will be harder to figure out typechecking errors for later labs.
 *)
type exp =
  | Var of Symbol.t
  | Const of (Int32.t * tau)
  | Binop_pure of
      { op : binop_pure
      ; lhs : mexp
      ; rhs : mexp
      }
  | Binop_impure of
      { op : binop_impure
      ; lhs : mexp
      ; rhs : mexp
      }
  | Unop of
      { op : unop
      ; operand : mexp
      }
  | Function of mexp list
  | Comparison of
      { op : cmp_binop
      ; lhs : mexp
      ; rhs : mexp
      }
  | And of
      { lhs : mexp
      ; rhs : mexp
      }
  | Or of
      { lhs : mexp
      ; rhs : mexp
      }
  | Ternary of
      { condition : mexp
      ; lhs : mexp
      ; rhs : mexp
      }

and mexp = exp Mark.t

type decl =
  | New_var of Symbol.t
  | Init of Symbol.t * mexp

type stm =
  | Declare of decl * tau * mstm
  | Assign of Symbol.t * mexp
  | Return of mexp
  | If of mexp * mstm * mstm
  | While of mexp * mstm
  | Nop
  | Seq of mstm * mstm
  | For of mstm * mstm * mexp * mstm
  | Expr_stm of mexp
  | Block_intermediate of mstm list
  | Declare_intermediate of decl * tau
  | Assign_exp of mexp * mexp

and mstm = stm Mark.t

(* Currently programs are a single function with no arguments and return type int. *)
type program = mstm list
type program_raw = Symbol.t * mstm list

module Print = struct
  let pp_binop_pure = function
    | Plus -> "add"
    | Minus -> "minus"
    | Times -> "times"
    | Bitwise_or -> "bitwise_or"
    | Bitwise_xor -> "bitwise_xor"
    | Bitwise_and -> "bitwise_and"
  ;;

  let pp_binop_impure = function
    | Divided_by -> "divide"
    | Modulo -> "modulo"
    | Left_shift -> "left_shift"
    | Right_shift -> "right_shift"
  ;;

  let pp_cmp_binop = function
    | Less -> "less_than"
    | Less_equal -> "lesser_or_equal"
    | Greater -> "greater_than"
    | Greater_equal -> "greater_or_equal "
    | Equal -> "equal"
    | Not_equal -> "not_equal"
  ;;

  let pp_unop = function
    | Negative -> "negate"
    | Bitwise_not -> "bitwise_not"
    | Not -> "logical_not"
  ;;

  let pp_tau = function
    | Int -> "int"
    | Bool -> "bool"
  ;;

  let rec pp_exp = function
    | Var id -> Symbol.name id
    | Const (c, t) -> sprintf "%s_const(%s)" (pp_tau t) (Int32.to_string c)
    | Binop_pure binop ->
      sprintf
        "%s(%s, %s)"
        (pp_binop_pure binop.op)
        (pp_mexp binop.lhs)
        (pp_mexp binop.rhs)
    | Binop_impure binop ->
      sprintf
        "%s(%s, %s)"
        (pp_binop_impure binop.op)
        (pp_mexp binop.lhs)
        (pp_mexp binop.rhs)
    | Unop unop -> sprintf "%s(%s)" (pp_unop unop.op) (pp_mexp unop.operand)
    | Function _ -> "Functions not implemented in lab2"
    | Comparison cmp ->
      sprintf "%s(%s, %s)" (pp_cmp_binop cmp.op) (pp_mexp cmp.lhs) (pp_mexp cmp.rhs)
    | And binop -> sprintf "logical_and(%s, %s)" (pp_mexp binop.lhs) (pp_mexp binop.rhs)
    | Or binop -> sprintf "logical_or(%s, %s)" (pp_mexp binop.lhs) (pp_mexp binop.rhs)
    | Ternary conds ->
      sprintf
        "ternary(%s, %s, %s)"
        (pp_mexp conds.condition)
        (pp_mexp conds.lhs)
        (pp_mexp conds.rhs)

  and pp_mexp e = pp_exp (Mark.data e)

  let pp_tau = function
    | Int -> "int"
    | Bool -> "bool"
  ;;

  let pp_decl = function
    | New_var id -> sprintf "%s" (Symbol.name id)
    | Init (id, e) -> sprintf "assign(%s,\n%s)" (Symbol.name id) (pp_mexp e)
  ;;

  (* TODO: I'm suspecting that Symbol should contain our type info as well, but 
     we won't know for sure until we do typechecking.*)
  let rec pp_stm = function
    | Declare (id, t, s) ->
      sprintf "decl(%s, %s, \n%s \n)" (pp_tau t) (pp_decl id) (pp_mstm s)
    | Declare_intermediate (id, t) -> sprintf "decl_int(%s, %s)" (pp_tau t) (pp_decl id)
    | Assign (id, e) -> sprintf "assign(%s,\n%s)" (Symbol.name id) (pp_mexp e)
    | Return e -> sprintf "return(%s)" (pp_mexp e)
    | If (e, s1, s2) -> sprintf "if(%s, \n%s, \n%s)" (pp_mexp e) (pp_mstm s1) (pp_mstm s2)
    | While (e, s) -> sprintf "while(%s,\n%s)" (pp_mexp e) (pp_mstm s)
    | Nop -> sprintf "Nop"
    | Seq (s1, s2) -> sprintf "seq(%s,\n%s)" (pp_mstm s1) (pp_mstm s2)
    | For (s1, s2, e, s3) ->
      sprintf "for(%s, %s, %s, \n%s)" (pp_mstm s1) (pp_mexp e) (pp_mstm s2) (pp_mstm s3)
    | Expr_stm e -> sprintf "expr_stm(%s)" (pp_mexp e)
    | Block_intermediate stms -> sprintf "block(%s\n)" (pp_stms stms)
    | Assign_exp (e1, e2) -> sprintf "assign_exp(%s,\n%s)" (pp_mexp e1) (pp_mexp e2)

  and pp_mstm stm = pp_stm (Mark.data stm)
  and pp_stms stms = String.concat (List.map ~f:(fun stm -> pp_mstm stm ^ ";") stms)

  let pp_program = pp_mstm
end
