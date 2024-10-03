(* L1 Compiler
 * Abstract Syntax Trees
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Forward compatible fragment of C0
 *)

module FieldMap = Type_modules.FieldMap
module FieldTable = Type_modules.FieldTable

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
  (* small types *)
  | Int
  | Bool
  | Void
  | Pointer of tau
  | Array of tau
  | Struct of Symbol.t
  | Alias of
      Symbol.t (* Typechecking should elaborate this out (resolve to actual type) *)
  | Any
  | Dummy
[@@deriving compare, sexp, hash, equal]
(* Use dummy when parsing for unknown types initially *)
(* This is irrelevant after typechecking since NULL_POINTER doesn't come with a type *)

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

type param = tau * Symbol.t

type exp =
  | Paren of mexp (* Elaborated out *)
  | Var of
      { ident : Symbol.t
      ; var_type : tau
      }
  | Const of
      { value : Int32.t
      ; const_type : tau
      }
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
  | Function_call of
      { ident : Symbol.t
      ; args : mexp list
      ; return_type : tau (* Return type of the function*)
      }
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
      ; result_type : tau (* This is the type of lhs & rhs *)
      }
  (*l4*)
  | Alloc of tau (* Allocate a cell on the heap for a pointer *)
  | Deref of
      { address : mexp
      ; pointer_type : tau (* Add during typechecking *)
      }
  | Null_pointer
  | Alloc_array of
      { array_type : tau
      ; size : mexp
      }
  | Array_access of
      { array : mexp
      ; index : mexp
      ; array_type : tau (* add during typechecking*)
      }
  | Struct_access_parse of
      { s : mexp (* think of a better name for this *)
      ; field : Symbol.t (* size of the field being accessed *)
      ; field_type : tau
      }
  | Struct_access of
      { s : mexp (* think of a better name for this *)
      ; offset : Int64.t (* Use to map to offset, calculate in elab_typecheck *)
      ; field_type : tau
      }

and mexp = exp Mark.t

and decl =
  | New_var of Symbol.t
  | Init of Symbol.t * mexp

and stm =
  | Declare of decl * tau * mstm
  | Assign of mexp * mexp
  | Asnop_pure_mem of
      { lhs : mexp
      ; op : binop_pure
      ; rhs : mexp
      }
  | Asnop_pure_mem_intermediate of
      { lhs : mexp
      ; op : binop_pure option
      ; rhs : mexp
      }
  | Asnop_impure_mem of
      { lhs : mexp
      ; op : binop_impure
      ; rhs : mexp
      }
  | Asnop_impure_mem_intermediate of
      { lhs : mexp
      ; op : binop_impure option
      ; rhs : mexp
      }
  | Return of mexp
  | Return_void
  | If of mexp * mstm * mstm
  | While of mexp * mstm
  | Nop
  | Seq of mstm * mstm
  | For of mstm * mstm * mexp * mstm
  | Expr_stm of mexp
  | Block_intermediate of mstm list
  | Declare_intermediate of decl * tau
  | Assert of mexp
  (* Elaborated out *)
  | Postop of
      { postop : binop_pure
      ; target : mexp
      }

(* Statement plus src file location *)
and mstm = stm Mark.t

type program_block =
  | Function_Def of
      { ret_type : tau
      ; ident : Symbol.t
      ; params : param list
      ; fn_block : mstm
      }
  | Function_Decl of
      { ret_type : tau
      ; ident : Symbol.t
      ; params : param list
      }
  | Typedef of
      { original : tau
      ; alias : Symbol.t
      }
  | Function_Def_Intermediate of
      { ret_type : tau
      ; ident : Symbol.t
      ; params : param list
      ; fn_block : mstm list (* turned into mstm in elaboration. *)
      }
  | Struct_Def of
      { ident : Symbol.t
      ; fields : (Symbol.t * tau) List.t (* Field name to index and tau instead *)
      }
  | Struct_Def_Intermediate of
      { ident : Symbol.t
      ; fields : (tau * Symbol.t) list
      }
  | Struct_Decl of { ident : Symbol.t }

and mprogram_block = program_block Mark.t

type program = mprogram_block list

(* Print as source, with redundant parentheses *)
module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
  val pp_mstm : mstm -> string
  val pp_tau : tau -> string
end
