(* L1 Compiler
 * Abstract Syntax Trees
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

(* Operator *)

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

(* Statement plus src file location *)
and mstm = stm Mark.t

type program = mstm list
type program_raw = Symbol.t * mstm list

(* Print as source, with redundant parentheses *)
module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : mstm -> string
  val pp_mstm : mstm -> string
end
