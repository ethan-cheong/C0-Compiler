(* L1 Compiler
 * Unelaborated Abstract Syntax Trees
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

open Core
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
  | Int
  | Bool
  | Void
  | Pointer of tau
  | Array of tau
  | Struct of Symbol.t
  | Alias of Symbol.t
  | Any
  | Dummy
  | Char
  | String
[@@deriving compare, sexp, hash, equal]

type t = tau [@@deriving compare, sexp, hash, equal]

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
  | String_const of string
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
      (* Deref(x) where x in an int ptr. Then pointer type should be int. *)
      
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
    (* TODO: change *)
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
  | Anno_result
  | Anno_elem of tau (* Get the type information from arr *)
  | Anno_index
  | Anno_length of mexp
  | Cast of
      { pointer_type : tau
      ; operand : mexp
      ; orig_type : tau
      }
  | Forall of
      { arr : mexp
      ; condition : mexp
      }
  | Exists of
      { arr : mexp
      ; condition : mexp
      }

and mexp = exp Mark.t

and decl =
  | New_var of Symbol.t
  | Init of Symbol.t * mexp

and stm =
  | Declare of decl * tau * mstm
  | Assign of mexp * mexp (* LHS must be an lvalue *)
  | Asnop_pure_mem of
      { lhs : mexp (* LHS must be an lvalue *)
      ; op : binop_pure
      ; rhs : mexp
      }
  | Asnop_pure_mem_intermediate of
      { lhs : mexp
      ; op : binop_pure option
      ; rhs : mexp
      }
  | Asnop_impure_mem of
      { lhs : mexp (* LHS must be an lvalue *)
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
  | Annotated_stm of anno * mstm
  | Annotated_stm_intermediate of anno list * mstm
  (* Elaborated out *)
  (* Elaborated out *)
  | Postop of
      { postop : binop_pure
      ; target : mexp
      }

and mstm = stm Mark.t

(* L6 *)
and anno = spec list

and spec =
  | Requires of mexp
  | Ensures of mexp
  | Loop_invariant of mexp
  | Assert_spec of mexp

type program_block =
  | Function_Def of
      { ret_type : tau
      ; ident : Symbol.t
      ; params : param list
      ; fn_block : mstm
      }
  | Function_Def_Anno of
      { ret_type : tau
      ; ident : Symbol.t
      ; params : param list
      ; anno : anno
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
      ; fn_block : mstm list
      }
  | Function_Def_Anno_Intermediate of
      { ret_type : tau
      ; ident : Symbol.t
      ; params : param list
      ; anno : anno list
      ; fn_block : mstm list
      }
  | Struct_Def of
      { ident : Symbol.t
      ; fields : (Symbol.t * tau) list
      }
  | Struct_Def_Intermediate of
      { ident : Symbol.t
      ; fields : (tau * Symbol.t) list
      }
  | Struct_Decl of { ident : Symbol.t }

and mprogram_block = program_block Mark.t

(* Program_l3 is now a list of mexps, considering how it has a return type *)
type program = mprogram_block list

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

  let rec pp_tau = function
    | Int -> "int"
    | Bool -> "bool"
    | Alias s -> sprintf "alias %s" (Symbol.name s)
    | Void -> "void"
    | Any -> "any"
    | Pointer t -> sprintf "%s pointer" (pp_tau t)
    | Array t -> sprintf "%s array" (pp_tau t)
    | Struct s -> sprintf "%s struct" (Symbol.name s)
    | Dummy -> "dummy"
    | Char -> "char"
    | String -> "string"
  ;;

  let pp_param (tau, sym) = pp_tau tau ^ " " ^ Symbol.name sym

  let pp_param_list param_list =
    let string_list = List.map param_list ~f:pp_param in
    "(" ^ String.concat ~sep:", " string_list ^ ")"
  ;;

  let rec pp_exp = function
    | Paren e -> sprintf "(%s)" (pp_mexp e)
    | Var { ident; var_type } -> sprintf "(%s %s)" (pp_tau var_type) (Symbol.name ident)
    | Const { value; const_type } ->
      sprintf "const(%s, %s)" (Int32.to_string value) (pp_tau const_type)
    | String_const s -> sprintf "string_const(%s)" s
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
    | Function_call { ident; args; _ } ->
      sprintf "%s(%s)" (Symbol.name ident) (pp_arg_list args)
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
    | Alloc t -> sprintf "alloc(%s)" (pp_tau t)
    | Deref { address; _ } -> sprintf "deref(%s)" (pp_mexp address)
    | Null_pointer -> "NULL_POINTER"
    | Alloc_array { array_type; size } ->
      sprintf "alloc_array(%s, %s)" (pp_tau array_type) (pp_mexp size)
    | Array_access { array; index; _ } -> sprintf "%s[%s]" (pp_mexp array) (pp_mexp index)
    | Struct_access_parse { s; field; _ } ->
      sprintf "%s.%s(parse)" (pp_mexp s) (Symbol.name field)
    | Struct_access { s; offset; _ } ->
      sprintf "%s.[%s]" (pp_mexp s) (Int64.to_string_hum ~delimiter:',' offset)
    | Anno_result -> "anno_result"
    | Anno_elem _ -> "anno_elem"
    | Anno_index -> "anno_index"
    | Anno_length e -> sprintf "anno_length(%s)" (pp_mexp e)
    | Cast { pointer_type; operand; orig_type } ->
      sprintf
        "cast(%s, %s, orig: %s)"
        (pp_tau pointer_type)
        (pp_mexp operand)
        (pp_tau orig_type)
    | Forall { arr; condition } ->
      sprintf "forall(%s, %s)" (pp_mexp arr) (pp_mexp condition)
    | Exists { arr; condition } ->
      sprintf "forall(%s, %s)" (pp_mexp arr) (pp_mexp condition)

  and pp_mexp e = pp_exp (Mark.data e)

  and pp_arg_list arg_list =
    let string_list = List.map arg_list ~f:pp_mexp in
    "(" ^ String.concat ~sep:", " string_list ^ ")"

  and pp_decl = function
    | New_var id -> sprintf "\t%s" (Symbol.name id)
    | Init (id, e) -> sprintf "assign(%s,\n\t%s)" (Symbol.name id) (pp_mexp e)

  and pp_stm = function
    | Declare (id, t, s) ->
      sprintf "decl(%s, %s, \n\t%s \n)" (pp_tau t) (pp_decl id) (pp_mstm s)
    | Declare_intermediate (id, t) -> sprintf "decl_int(%s, %s)" (pp_tau t) (pp_decl id)
    | Assign (lhs, e) -> sprintf "assign(%s,\n\t%s)" (pp_mexp lhs) (pp_mexp e)
    | Asnop_pure_mem { lhs; op; rhs } ->
      sprintf "asnop(%s, %s, %s)" (pp_mexp lhs) (pp_binop_pure op) (pp_mexp rhs)
    | Asnop_impure_mem { lhs; op; rhs } ->
      sprintf "asnop(%s, %s, %s)" (pp_mexp lhs) (pp_binop_impure op) (pp_mexp rhs)
    | Return e -> sprintf "return(%s)" (pp_mexp e)
    | Return_void -> "return_void()"
    | If (e, s1, s2) ->
      sprintf "if(%s, \n\t%s, \n\t%s)" (pp_mexp e) (pp_mstm s1) (pp_mstm s2)
    | While (e, s) -> sprintf "while(%s,\n\t%s)" (pp_mexp e) (pp_mstm s)
    | Nop -> sprintf "Nop"
    | Seq (s1, s2) -> sprintf "seq(%s,\n\t%s)" (pp_mstm s1) (pp_mstm s2)
    | For (s1, s2, e, s3) ->
      sprintf "for(%s, %s, %s, \n%s)" (pp_mstm s1) (pp_mexp e) (pp_mstm s2) (pp_mstm s3)
    | Expr_stm e -> sprintf "expr_stm(%s)" (pp_mexp e)
    | Block_intermediate stms -> sprintf "block(\n\t%s\n)" (pp_stms stms)
    | Assert e -> sprintf "assert(%s)" (pp_mexp e)
    | Annotated_stm_intermediate (anno, mstm) ->
      sprintf "anno(%s, %s)" (pp_anno_list anno) (pp_mstm mstm)
    | Annotated_stm (anno, mstm) -> sprintf "anno(%s, %s)" (pp_anno anno) (pp_mstm mstm)
    | Asnop_pure_mem_intermediate { lhs; op; rhs } ->
      sprintf
        "asnop(%s, %s, %s)"
        (pp_mexp lhs)
        (match op with
         | None -> "="
         | Some x -> pp_binop_pure x)
        (pp_mexp rhs)
    | Asnop_impure_mem_intermediate { lhs; op; rhs } ->
      sprintf
        "asnop(%s, %s, %s)"
        (pp_mexp lhs)
        (match op with
         | None -> "="
         | Some x -> pp_binop_impure x)
        (pp_mexp rhs)
    | Postop { postop; target } ->
      (match postop with
       | Plus -> sprintf "%s++" (pp_mexp target)
       | Minus -> sprintf "%s--" (pp_mexp target)
       | _ -> failwith "wtf?")

  and pp_mstm stm = pp_stm (Mark.data stm)
  and pp_stms stms = String.concat (List.map ~f:(fun stm -> pp_mstm stm ^ ";") stms)

  and pp_anno (specs : anno) =
    List.fold specs ~init:"" ~f:(fun acc spec -> (pp_spec spec ^ "\n") ^ acc)

  and pp_anno_list (lst : anno list) =
    List.fold ~init:"" lst ~f:(fun acc anno -> (pp_anno anno ^ "\n") ^ acc)

  and pp_spec = function
    | Requires mexp -> sprintf "requires(%s)" (pp_mexp mexp)
    | Ensures mexp -> sprintf "ensures(%s)" (pp_mexp mexp)
    | Loop_invariant mexp -> sprintf "loop_invariant(%s)" (pp_mexp mexp)
    | Assert_spec mexp -> sprintf "assert_spec(%s)" (pp_mexp mexp)
  ;;

  let pp_program_block = function
    | Function_Def { ret_type; ident; params; fn_block } ->
      sprintf
        "fn_def(%s, %s, %s \n%s\t\n)"
        (pp_tau ret_type)
        (Symbol.name ident)
        (pp_param_list params)
        (pp_mstm fn_block)
    | Function_Def_Anno { ret_type; ident; params; anno; fn_block } ->
      sprintf
        "fn_def_anno(%s, %s, %s, (anno:%s) \n%s\t\n)"
        (pp_tau ret_type)
        (Symbol.name ident)
        (pp_param_list params)
        (pp_anno anno)
        (pp_mstm fn_block)
    | Function_Decl { ret_type; ident; params } ->
      sprintf
        "declare_function(%s, %s, %s)"
        (pp_tau ret_type)
        (Symbol.name ident)
        (pp_param_list params)
    | Function_Def_Intermediate { ret_type; ident; params; fn_block } ->
      sprintf
        "define_function(%s, %s, %s \n%s\t\n)"
        (pp_tau ret_type)
        (Symbol.name ident)
        (pp_param_list params)
        (String.concat ~sep:";\n" (List.map ~f:(fun x -> "\t" ^ pp_mstm x) fn_block))
    | Function_Def_Anno_Intermediate { ret_type; ident; params; anno; fn_block } ->
      sprintf
        "define_function(%s, %s, %s (anno:%s) \n%s\t\n)"
        (pp_tau ret_type)
        (Symbol.name ident)
        (pp_param_list params)
        (pp_anno_list anno)
        (String.concat ~sep:";\n" (List.map ~f:(fun x -> "\t" ^ pp_mstm x) fn_block))
    | Typedef { original; alias } ->
      sprintf "typedef(%s, %s)\n" (pp_tau original) (Symbol.name alias)
    | Struct_Decl { ident } -> sprintf "declare_struct(%s)\n" (Symbol.name ident)
    | Struct_Def { ident; fields } ->
      sprintf
        "define_struct(%s, %s)\n"
        (Symbol.name ident)
        (List.fold_left fields ~init:"" ~f:(fun acc (fieldname, tau) ->
           acc ^ sprintf "%s %s," (pp_tau tau) (Symbol.name fieldname)))
    | Struct_Def_Intermediate { ident; fields } ->
      sprintf
        "define_struct(%s, %s)\n"
        (Symbol.name ident)
        (String.concat
           ~sep:";\n"
           (List.map
              ~f:(fun (tau, symbol) -> "\t" ^ pp_tau tau ^ " " ^ Symbol.name symbol)
              fields))
  ;;

  let pp_mprogram_block program = pp_program_block (Mark.data program)

  let pp_program program =
    String.concat ~sep:";\n" (List.map ~f:(fun x -> pp_mprogram_block x) program)
  ;;
end
