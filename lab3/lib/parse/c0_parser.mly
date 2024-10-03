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

(* expand_asnop (id, "op=", exp) region = "id = id op exps"
 * or = "id = exp" if asnop is "="
 * syntactically expands a compound assignment operator
 *)
let expand_asnop_pure ~lhs ~op ~rhs
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) =
    match lhs, op, rhs with
    | id, None, exp -> Ast.Assign_exp (id, exp)
    | id, Some op, exp ->
      let binop = Ast.Binop_pure {
        op;
        lhs = id;
        rhs = exp;
      }
      in
      Ast.Assign_exp (id, mark binop start_pos end_pos)

let expand_asnop_impure ~lhs ~op ~rhs
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) =
    match lhs, op, rhs with
    | id, None, exp -> Ast.Assign_exp (id, exp)
    | id, Some op, exp ->
      let binop = Ast.Binop_impure {
        op;
        lhs = id;
        rhs = exp;
      }
      in
      Ast.Assign_exp (id, mark binop start_pos end_pos)

  (* Postops always pure *)
  let expand_postop ~postops ~target
    (start_pos: Lexing.position)
    (end_pos: Lexing.position) =
    let (postop, marked_postop) = postops in
    let binop = Ast.Binop_pure {
      op = postop;
      lhs = target;
      rhs = marked_postop;
    } in
    Ast.Assign_exp (target, mark binop start_pos end_pos)

  (* Used for typedef aliasing later. *)
  let symbol_of_type ~c_type =
    match c_type with
    | Ast.Int -> Symbol.symbol "int"
    | Ast.Bool -> Symbol.symbol "bool"
    | Ast.Void -> Symbol.symbol "void"
    | Ast.Alias s -> s
%}

%token Eof
%token Semicolon
%token Ternary_if Ternary_else
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token <Symbol.t> Ident
%token <Int32.t> Bool_const
%token Return
%token Int
%token Bool
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq
%token L_brace R_brace
%token L_paren R_paren
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
%type <Ast.binop_pure * Ast.mexp> m_postop(postop)

%%

param :
  | param_type = grammar_type; ident = Ident;
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
    ident = Ident;
    param_list = param_list;
    Semicolon;
    { Ast.Function_Decl {ret_type = grammar_type; ident; params = param_list; } }
  (* fn defn *)
  | grammar_type = grammar_type; 
    ident = Ident;
    param_list = param_list;
    block = block;
    { Ast.Function_Def_Intermediate {ret_type = grammar_type; ident; params = param_list; fn_block = block } }
  (* typedef *)
  | Typedef; grammar_type = grammar_type; ident = Ident; Semicolon;
    { Ast.Typedef {original = (symbol_of_type ~c_type:grammar_type); alias = ident} }
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

grammar_type:
  | Int;
    { Ast.Int }
  | Bool;
    { Ast.Bool }
  | ident = Ident;
    { Ast.Alias ident }
  | Void; (* To check in elaboration or typechecking *)
    { Ast.Void }
  ;

decl :
  | ident = Ident;
      { Ast.New_var ident }
  | ident = Ident; Assign; e = m(exp);
      { Ast.Init (ident, e) }
  ;

stmts :
  | (* empty, epsilon *)
      { [] }
  | hd = m(stmt); tl = stmts; (* Statements, stmt :: stmts *)
      { hd :: tl }
  ;

stmt :
  | simp = simp; Semicolon;
   { simp }
  | control = control;
    { control }
  | block = block;
    { Ast.Block_intermediate block }
  ;

simp :
  | lhs = m(exp);
    op = asnop_pure;
    rhs = m(exp);
      { expand_asnop_pure ~lhs ~op ~rhs $startpos(lhs) $endpos(rhs) }
  | lhs = m(exp);
    op = asnop_impure;
    rhs = m(exp);
      { expand_asnop_impure ~lhs ~op ~rhs $startpos(lhs) $endpos(rhs) }
  (* Assumes that for mark, you need end position to mark where is the start and end of this simp *)
  | target = m(exp);
    postops = m_postop(postop);
    { expand_postop ~postops ~target $startpos(target) $endpos(postops) }
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
  | L_paren; e = exp; R_paren;
      { e }
  | c = int_const;
      { Ast.Const (c, Ast.Int) }
  | bool_val = Bool_const; (* For both true and false *)
   { Ast.Const (bool_val, Ast.Bool) }
  | ident = Ident;
      { Ast.Var ident }
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
    { Ast.Ternary {condition; lhs; rhs} }
  | ident = Ident;
    args = arg_list;
    { Ast.Function_call {ident; args = args} }
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

(* Goal: mark postop but with an intconst *)
m_postop(x) :
  | x = x;
      (* $startpos(s) and $endpos(s) are menhir's replacements for
       * Parsing.symbol_start_pos and Parsing.symbol_end_pos, but,
       * unfortunately, they can only be called from productions. *)
      { (x, mark (Ast.Const (Core.Int32.of_int_trunc 1, Ast.Int)) $startpos(x) $endpos(x)) }
  ;

%%
