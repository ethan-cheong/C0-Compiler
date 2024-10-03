%{
(* L1 Compiler
 * L1 grammar
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now conforms to the L1 fragment of C0
 *
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with 2014 spec
 *
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 *   - Update to use Core instead of Core.Std and ppx
 *
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Update to use menhir instead of ocamlyacc.
 *   - Improve presentation of marked asts.
 *
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

let mark
  (data : 'a)
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) : 'a Mark.t =
  let src_span = Mark.of_positions start_pos end_pos in
  Mark.mark data src_span

let expand_pointer ~s ~field
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) =
  let marked_deref = mark (Ast.Deref {address = s; pointer_type = Ast.Dummy}) start_pos end_pos in
  Ast.Struct_access_parse {s = marked_deref; field; field_type = Ast.Dummy}

(* Postops always pure *)
(*
let expand_postop ~postops ~target
  (start_pos: Lexing.position)
  (end_pos: Lexing.position) =
  let (postop, marked_postop) = postops in
  let binop = Ast.Binop_pure {
    op = postop;
    lhs = target;
    rhs = marked_postop;
  } in
  Ast.Assign (target, mark binop start_pos end_pos)  
*)

%}

%token Eof
%token Semicolon
%token Ternary_if Ternary_else
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token <Int32.t> Bool_const
%token <Int32.t> Char_const
%token <String.t> String_const
%token Requires Ensures Loop_invariant Anno_assert New_line
%token Exist Forall Arrelement Arrindex
%token Anno_length Anno_result Anno_line Anno_start Anno_end
%token Return
%token Int
%token Bool, Char, String
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq
%token L_brace R_brace
%token L_paren R_paren
%token L_bracket R_bracket
%token While_keyword For_keyword If_keyword Else_keyword
%token And Or Not Bitwise_not
%token Bitwise_and_eq Bitwise_xor_eq Bitwise_or_eq Left_shift_eq Right_shift_eq
%token Bitwise_and Bitwise_xor Bitwise_or
%token Less Less_eq Greater Greater_eq Not_eq Equals
%token Left_shift Right_shift
%token Plus Minus Star Slash Percent
%token Minus_minus Plus_plus
%token Unary
%token Then
%token Typedef Void Assert
%token Comma
%token <Symbol.t> Value_ident
%token <Symbol.t> Type_ident
%token Dot Arrow
%token Alloc Alloc_array Null Struct
%token Deref


(* Unary is a dummy terminal.
 * We need dummy terminals if we wish to assign a precedence
 * to a production that does not correspond to the precedence of
 * the rightmost terminal in that production.
 * Implicit in this is that precedence can only be inferred for
 * terminals. Therefore, don't try to assign precedence to "rules"
 * or "productions".
 *
 * Minus_minus is a dummy terminal to parse-fail on.
 *)
%right Ternary_if 
%left Or
%left And
%left Bitwise_or
%left Bitwise_xor
%left Bitwise_and
%left Equals Not_eq
%left Less Greater Less_eq Greater_eq
%left Left_shift Right_shift
%left Plus Minus
%left Star Slash Percent
%right Unary
%nonassoc Then
%left Else_keyword
%right Deref (* Make sure it has highest priority *)
%nonassoc L_bracket Arrow Dot

%start program

(* It's only necessary to provide the type of the start rule,
 * but it can improve the quality of parser type errors to annotate
 * the types of other rules.
 *)
%type <Ast.program_block> gdecl
%type <Ast.mprogram_block> m(gdecl)
%type <Ast.param> param
%type <Ast.param list> param_list
%type <Ast.param list> param_list_follow
%type <Ast.program> program
%type <Ast.mexp list> arg_list
%type <Ast.mexp list> arg_list_follow
%type <Ast.mstm list> stmts
%type <Ast.mstm list> block
%type <Ast.mstm> m(stmt)
%type <Ast.mstm> m(simpopt)
%type <Ast.stm> simpopt
%type <Ast.decl> decl
%type <Ast.stm> stmt
%type <Ast.stm> simp
%type <Ast.stm> control
%type <Ast.stm > if_statement
%type <Ast.exp> exp
%type <Ast.mexp> m(exp)
%type <Core.Int32.t> int_const
%type <Ast.unop> unop
%type <Ast.binop_pure> binop_pure
%type <Ast.binop_impure> binop_impure
%type <Ast.binop_pure> postop
%type <Ast.binop_pure option> asnop_pure
%type <Ast.binop_impure option> asnop_impure
%type <Ast.cmp_binop > cmp_binop
%type <Ast.tau > grammar_type
%type <Ast.tau * Symbol.t> field
%type <(Ast.tau * Symbol.t) list> field_list
%type <Symbol.t> type_or_value
%type <Symbol.t> midrule(__anonymous_0)
%type <Ast.anno> anno_all
%type <Ast.anno> anno_block_list
%type <Ast.anno> anno_line_follow
%type <Ast.anno> anno_line_list
%type <Ast.anno list> list_of_anno
%type <Ast.anno list> rem_anno_list
%type <Ast.stm> non_anno_stmt
%type <Ast.stm> anno_stmt
%type <Ast.spec> spec
%type <String.t> string_const
%type <Int32.t> char_const
%%

type_or_value :
  | ident = Value_ident;
    { ident }
  | ident = Type_ident;
    { ident }
  ;

field :
 (* Resolve the ident in typechecking *)
  | field_type = grammar_type; ident = type_or_value; Semicolon;
    { (field_type, ident) }
  ;

field_list :
  | 
    { [] }
  | field = field; tail = field_list;
    { field :: tail }
  ;

spec :
  | Requires; e = m(exp); Semicolon;
    { Ast.Requires e }
  | Ensures; e = m(exp); Semicolon;
    { Ast.Ensures e }
  | Loop_invariant; e = m(exp); Semicolon;
    { Ast.Loop_invariant e }
  | Anno_assert; e = m(exp); Semicolon;
    { Ast.Assert_spec e }
  ;

anno_line_follow :
  | 
    { [] }
  | s = spec; tail = anno_line_follow;
    { s :: tail }

anno_line_list : 
  | Anno_line; specs = anno_line_follow; New_line;
    { specs }
  ;

anno_block_list :
  | Anno_start; specs = anno_line_follow; Anno_end;
    { specs }

anno_all :
  | a = anno_block_list;
    { a }
  | a = anno_line_list;
    { a }

rem_anno_list :
  | 
    { [] }
  | a = anno_all; tail = rem_anno_list;
    { a :: tail }

list_of_anno :
  | a = anno_all; tail = rem_anno_list;
    { a :: tail }

param :
  | param_type = grammar_type; ident = Value_ident;
    { (param_type, ident) }
  ;

param_list_follow :
  | 
    { [] }
  | Comma; param = param; tail = param_list_follow;
    { param :: tail }

param_list : 
  | L_paren; R_paren;
    { [] }
  | L_paren; param = param; params = param_list_follow; R_paren;
    { param :: params }
  ;

gdecl :
  (* fn decl *)
  | grammar_type = grammar_type; 
    ident = Value_ident;
    param_list = param_list;
    Semicolon;
    { Ast.Function_Decl {ret_type = grammar_type; ident; params = param_list; } }
  (* fn defn *)
  | grammar_type = grammar_type; 
    ident = Value_ident;
    param_list = param_list;
    block = block;
    { Ast.Function_Def_Intermediate {ret_type = grammar_type; ident; params = param_list; fn_block = block } }
  | grammar_type = grammar_type; 
    ident = Value_ident;
    param_list = param_list;
    a = list_of_anno;
    block = block;
    { Ast.Function_Def_Anno_Intermediate {ret_type = grammar_type; ident; params = param_list; anno = a; fn_block = block } }
  (* typedef, add the function here! *)
  (* https://discuss.ocaml.org/t/good-practice-for-interaction-between-mly-and-mll-files/12961 *)
  | Typedef; grammar_type = grammar_type; ident = midrule(
    ident = Value_ident { Check_typedef.add_typedef ident; ident }); Semicolon;
    { Ast.Typedef {original = grammar_type; alias = ident} }
  | Struct; ident = Value_ident; Semicolon;
    { Ast.Struct_Decl { ident } }
  | Struct; ident = Type_ident; Semicolon;
    { Ast.Struct_Decl { ident } }
  | Struct; ident = Value_ident; L_brace; fields = field_list; R_brace; Semicolon;
    { Ast.Struct_Def_Intermediate { ident; fields } }
  | Struct; ident = Type_ident; L_brace; fields = field_list; R_brace; Semicolon;
    { Ast.Struct_Def_Intermediate { ident; fields } }
  
  ;
  
program :
  | (* Empty, epsilon*) Eof;
    { [] }
  | gdecl = m(gdecl); prog_l3 = program;
    { gdecl :: prog_l3 }
  ;

block:
  | L_brace; body = stmts; R_brace; (*  *)
      { body }
  ;

grammar_type :
  | Int;
    { Ast.Int }
  | Bool;
    { Ast.Bool }
  | ident = Type_ident;
    { Ast.Alias ident }
  | Void; (* To check in elaboration or typechecking *)
    { Ast.Void }
  | ident = grammar_type; Star;
    { Ast.Pointer ident }
  | ident = grammar_type; L_bracket; R_bracket;
    { Ast.Array ident }
  (* Struct can be both value and type, see example in parse_cases.txt *)
  | Struct; ident = type_or_value;
    { Ast.Struct ident}
  | String;
    { Ast.String }
  | Char;
    { Ast.Char}
  ;

decl :
  | ident = Value_ident;
      { Ast.New_var ident }
  | ident = Value_ident; Assign; e = m(exp);
      { Ast.Init (ident, e) }
  ;

stmts :
  | (* empty, epsilon *)
      { [] }
  | hd = m(stmt); tl = stmts; (* Statements, stmt :: stmts *)
      { hd :: tl }
  ;

stmt :
  | s = non_anno_stmt;
    { s }
  | a = anno_stmt;
    { a }
  ;

non_anno_stmt : 
  | simp = simp; Semicolon;
   { simp }
  | control = control;
    { control }
  | block = block;
    { Ast.Block_intermediate block }

anno_stmt :
  | a = list_of_anno; s = non_anno_stmt; 
    { Ast.Annotated_stm_intermediate (a, mark s $startpos(s) $endpos(s)) }

simp :
  | lhs = m(exp);
    op = asnop_pure;
    rhs = m(exp);
      { Asnop_pure_mem_intermediate { lhs; op; rhs; }  }
  | lhs = m(exp);
    op = asnop_impure;
    rhs = m(exp);
      { Asnop_impure_mem_intermediate { lhs; op; rhs; }  }
  (* Assumes that for mark, you need end position to mark where is the start and end of this simp *)
  | target = m(exp);
    postop = postop;
    { Postop {postop; target} }
(* Expressions could be statements? *)
  | exp = m(exp);
    { Ast.Expr_stm exp }
  | tau = grammar_type; decl = decl;
    { Ast.Declare_intermediate (decl, tau) }
  ;

simpopt:
  | 
    { Ast.Nop } (* No op? *)
  | simp = simp; 
    { simp }
  ;

control :
  | i = if_statement;
    { i }
  | While_keyword;
    L_paren; exp = m(exp); R_paren;
    stmt = m(stmt);
    { Ast.While (exp, stmt) }
  | For_keyword;
    L_paren; pre_block_simp = m(simpopt); Semicolon;
    exp = m(exp); Semicolon;
    post_block_simp = m(simpopt); R_paren;
    body = m(stmt);
    { Ast.For (pre_block_simp, post_block_simp, exp, body) }
  | Return; e = m(exp); Semicolon;
      { Ast.Return e }
  | Return; Semicolon;
      { Ast.Return_void }  
  | Assert; L_paren; e = m(exp); R_paren; Semicolon;
      { Ast.Assert e}
  ;


if_statement :
  | If_keyword;
    L_paren; exp = m(exp); R_paren;
    stmt = m(stmt);
    Else_keyword; else_stmt = m(stmt);
    { Ast.If (exp, stmt, else_stmt) }
  |  If_keyword;
    L_paren; exp = m(exp); R_paren;
    stmt = m(stmt); %prec Then
    { Ast.If (exp, stmt, (mark Ast.Nop Lexing.dummy_pos Lexing.dummy_pos)) }
;

arg_list_follow :
  | 
    { [] }
  | Comma; mexp = m(exp); tail = arg_list_follow;
    { mexp :: tail }

arg_list : 
  | L_paren; R_paren;
    { [] }
  | L_paren; mexp = m(exp); tail = arg_list_follow; R_paren;
    { mexp :: tail }
  ;


exp :
  | L_paren; e = m(exp); R_paren;
      { Ast.Paren e }
  | c = int_const;
      { Ast.Const {value = c; const_type = Ast.Int} }
  | bool_val = Bool_const; (* For both true and false *)
   { Ast.Const {value = bool_val; const_type = Ast.Bool} }
  | c = char_const;
      { Ast.Const {value = c; const_type = Ast.Char} }
  | s = string_const;
      { Ast.String_const s }
  | ident = Value_ident;
      { Ast.Var { ident; var_type = Ast.Dummy } }
  | op = unop; target = m(exp); %prec Unary
    (* Now will include -, !, ~ *)
    (* %prec Unary to reduce its precedence *)
      { Ast.Unop { op; operand = target; } }
  | lhs = m(exp);
    op = binop_pure;
    rhs = m(exp);
      { Ast.Binop_pure { op; lhs; rhs; } }
  | lhs = m(exp);
    op = binop_impure;
    rhs = m(exp);
      { Ast.Binop_impure { op; lhs; rhs; } }
  | lhs = m(exp);
    op = cmp_binop;
    rhs = m(exp);
      { Ast.Comparison { op; lhs; rhs; } }
  (* Special case of (expr) binop (expr) *)
  | lhs = m(exp); And; rhs = m(exp);
    {Ast.And { lhs ; rhs } }
  | lhs = m(exp); Or; rhs = m(exp);
    {Ast.Or { lhs ; rhs } }
  | condition = m(exp); Ternary_if; lhs = m(exp); Ternary_else; rhs = m(exp); %prec Ternary_if
    { Ast.Ternary {condition; lhs; rhs; result_type = Ast.Dummy } }
  | ident = Value_ident;
    args = arg_list;
    { Ast.Function_call {ident; args = args; return_type = Ast.Dummy } }
  | Null;
    { Ast.Null_pointer }
  | s = m(exp); Dot; field = type_or_value;
    { Ast.Struct_access_parse {s; field = field; field_type = Ast.Dummy } }
  (* struct pointer access *)
  | s = m(exp); Arrow; field = type_or_value;
    { expand_pointer ~s ~field $startpos(s) $endpos(field) }
  | Alloc; L_paren; tau = grammar_type; R_paren;
    { Ast.Alloc tau }
  | Alloc_array; L_paren; array_type = grammar_type; Comma; size = m(exp); R_paren;
    { Ast.Alloc_array {array_type; size} }
  | Star; mexp = m(exp); %prec Deref
    { Ast.Deref {address = mexp; pointer_type = Ast.Dummy} }
  | array = m(exp); L_bracket; index = m(exp); R_bracket;
   {Ast.Array_access { array; index; array_type = Ast.Any } }
  | Anno_result;
    { Ast.Anno_result }
  | Anno_length; L_paren; e = m(exp); R_paren;
    { Ast.Anno_length e }
  | L_paren; g = grammar_type; R_paren; e = m(exp); %prec Deref
    { Ast.Cast {pointer_type = g; operand = e; orig_type = Ast.Dummy} }
  | Arrelement;
    { Ast.Anno_elem Ast.Dummy}
  | Arrindex;
    { Ast.Anno_index }
  | Exist; L_brace; e1 = m(exp); R_brace; L_paren; e2 = m(exp); R_paren;
    { Ast.Exists {arr = e1; condition = e2} }
  | Forall; L_brace; e1 = m(exp); R_brace; L_paren; e2 = m(exp); R_paren;
    { Ast.Forall {arr = e1; condition = e2} }
  ;


(* This higher-order rule produces a marked result of whatever the
 * rule passed as argument will produce.
 *)
m(x) :
  | x = x;
      (* $startpos(s) and $endpos(s) are menhir's replacements for
       * Parsing.symbol_start_pos and Parsing.symbol_end_pos, but,
       * unfortunately, they can only be called from productions. *)
      { mark x $startpos(x) $endpos(x) }
  ;

int_const :
  | c = Dec_const;
      { c }
  | c = Hex_const;
      { c }
  ;

char_const : 
  | c = Char_const;
    { c }

string_const : 
  | c = String_const;
    { c }

(* See the menhir documentation for %inline.
 * This allows us to factor out binary operators while still
 * having the correct precedence for binary operator expressions.
 *)
%inline
binop_pure :
  | Plus;
      { Ast.Plus}
  | Minus;
      { Ast.Minus }
  | Star;
      { Ast.Times }
(* New tokens *)
  | Bitwise_and;
    { Ast.Bitwise_and }
  | Bitwise_xor;
    { Ast.Bitwise_xor }
  | Bitwise_or;
    { Ast.Bitwise_or }
  ;

%inline
binop_impure:
  | Left_shift;
    { Ast.Left_shift }
  | Right_shift;
    { Ast.Right_shift }
  | Slash;
      { Ast.Divided_by }
  | Percent;
      { Ast.Modulo }
  ;


asnop_pure :
  | Assign;
      { None }
  | Plus_eq;
      { Some Ast.Plus }
  | Minus_eq;
      { Some Ast.Minus }
  | Star_eq;
      { Some Ast.Times }
  // Should work since it copies the syntax from above
  | Bitwise_and_eq;
    { Some Ast.Bitwise_and }
  | Bitwise_xor_eq;
    { Some Ast.Bitwise_xor }
  | Bitwise_or_eq;
    { Some Ast.Bitwise_or}
  ;

asnop_impure :
  | Slash_eq;
      { Some Ast.Divided_by }
  | Percent_eq;
      { Some Ast.Modulo }
  | Left_shift_eq;
    { Some Ast.Left_shift }
  | Right_shift_eq;
    { Some Ast.Right_shift }
  ;

%inline
cmp_binop :
  | Less;
    { Ast.Less }
  | Less_eq;
    { Ast.Less_equal }
  | Greater
    { Ast.Greater }
  | Greater_eq;
    { Ast.Greater_equal }
  | Equals;
    { Ast.Equal }
  | Not_eq;
    { Ast.Not_equal }

unop :
  | Not;
    { Ast.Not }
  | Bitwise_not;
    { Ast.Bitwise_not }
  | Minus;
    { Ast.Negative }
  ;

postop :
  | Plus_plus;
    { Ast.Plus }
  | Minus_minus;
    { Ast.Minus }
  ;
%%
