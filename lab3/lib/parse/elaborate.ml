(* L1 Compiler
 * Elaborate on the initial AST
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
 *)

open Core

(* Helper function to Mark something with the lexing positions *)
let mark_with_pos (data : 'a) (start_pos : Lexing.position) (end_pos : Lexing.position)
  : 'a Mark.t
  =
  let src_span = Mark.of_positions start_pos end_pos in
  Mark.mark data src_span
;;

(* Helper function to Mark something with the source span *)
let mark_with_span (data : 'a) (span : Mark.src_span) = Mark.mark data span

(* Helper function to generate the source span, which comes from parsing. 
   Will generate a dummy one if there isn't a span for a given statement *)
let get_start_end marked_stmt =
  match Mark.src_span marked_stmt with
  | Some span -> span
  | None -> Mark.of_positions Lexing.dummy_pos Lexing.dummy_pos
;;

(* Expands on the initial mstm list by recursively going into each of the branches
   and processing each statement *)
let rec expand_ast_list (lst : Ast.mstm list) =
  match lst with
  | [] -> mark_with_pos Ast.Nop Lexing.dummy_pos Lexing.dummy_pos
  | h :: t ->
    (match Mark.data h with
     | Ast.Declare_intermediate (decl, tau) ->
       let decl_span = get_start_end h in
       mark_with_span (process_decl decl tau t) decl_span
     | _ ->
       (* In all other cases, can expand normally *)
       mark_with_pos
         (Ast.Seq (process h, expand_ast_list t))
         Lexing.dummy_pos
         Lexing.dummy_pos)

(* Elaborates on intermediate types and keeps desired types untouched. *)
and process h =
  let stm_data = Mark.data h in
  let stm_src = get_start_end h in
  match stm_data with
  | Ast.Declare_intermediate (decl, tau) ->
    mark_with_span (process_decl decl tau []) stm_src
  | Ast.Assign (_, _) -> h
  | Ast.Return _ -> h
  | Ast.Return_void -> h
  | Ast.Nop -> h
  | Ast.Expr_stm _ -> h
  | Ast.Block_intermediate lst -> expand_ast_list lst
  | Ast.If (mexp, s1, s2) ->
    mark_with_span (Ast.If (mexp, process s1, process s2)) stm_src
  | Ast.Seq (s1, s2) -> mark_with_span (Ast.Seq (process s1, process s2)) stm_src
  | Ast.While (e, s) -> mark_with_span (Ast.While (e, process s)) stm_src
  | Ast.For (s1, s2, e, s3) -> mark_with_span (expand_for s1 s2 e s3) stm_src
  | Ast.Declare (decl, tau, mstm) ->
    mark_with_span (Ast.Declare (decl, tau, process mstm)) stm_src
  | Ast.Assign_exp (exp1, exp2) -> mark_with_span (validate_assign_exp exp1 exp2) stm_src
  | Ast.Assert _ -> h

(* Elaborates on a declaration statement by elaborating the tail. *)
and process_decl decl tau tail =
  match decl with
  | Ast.New_var _ -> Ast.Declare (decl, tau, expand_ast_list tail)
  | Ast.Init _ -> Ast.Declare (decl, tau, expand_ast_list tail)

(* De-sugars for loop into a block that declares a scope and has a while-loop, 
   followed by a step statement if any. For example,
    
    for (pre_block; condition ; post_block) {
        body
    }
    -> 
      pre_block,
      while (condition) {
        body
      } 
      post_block
    *)
and expand_for pre_block post_block condition body =
  let dummy_marked_post_block = validate post_block in
  let dummy_marked_seq =
    mark_with_pos
      (Ast.Seq (process body, dummy_marked_post_block))
      Lexing.dummy_pos
      Lexing.dummy_pos
  in
  let dummy_marked_while =
    mark_with_pos
      (Ast.While (condition, dummy_marked_seq))
      Lexing.dummy_pos
      Lexing.dummy_pos
  in
  match Mark.data pre_block with
  | Ast.Declare_intermediate (decl, tau) -> process_decl decl tau [ dummy_marked_while ]
  | _ -> Ast.Seq (process pre_block, dummy_marked_while)

(* Ensures assignment expressions have only variables 
   (needed as lvalues are parsed as expressions) *)
and validate_assign_exp mexp1 mexp2 =
  match Mark.data mexp1 with
  | Ast.Var s -> Ast.Assign (s, mexp2)
  | _ -> failwith "Assign_exp, lhs is not a symbol"

(* Validates for loops to ensure step statements do not have declarations.
   We can't do this in typechecking since elaboration might produce valid code
   that did not come from a valid for loop. *)
and validate h =
  let stm_data = Mark.data h in
  match stm_data with
  | Ast.Declare _ -> failwith "For loop: Declaration cannot be step statement"
  | Ast.Declare_intermediate _ ->
    failwith "For loop: Declaration_intermediate cannot be step statement"
  | _ -> process h
;;

(* DEPRECATED *)
(* let elaborate (initial_ast_raw : Ast.program) : Ast.mstm =
  expand_ast_list initial_ast_raw
;; *)

(* Goal:
  1. Elaborate the main file into seq of seq
  2. De-sugar all the expressions/statements
  3. Re-arrange tree in this order:
  3a. Typedefs first (in order it is seen)
  3b. Function declarations (any order)
  3c. Function definitions (any order)    

  By the end, function definitions will always have a declaration.
  Similar to: (Fn_Defn: Assign, Fn_Decl: Decl)

  Method:
  1. 3 Lists and 1 Hashtable
  1a. Typedef, Decl, Defn
  1b. Hashtable to track symbol for decl/defn
  2. Iterate through program
  2a. Each time see a typedef, decl, defn, put into each one
  2b. Each time see a defn/decl, check if they already exist
  2b.1. Throw error if they already exist
  2b.2. If don't exist, add to hashmap
  2b.3. If fn_defn, then de-sugar. Create a new decl from the defn and append
  3. Concat all the lists together

  Processing each type:
  1. Typedef: Just put into the list and continue recursing
  1a. To check if an ident has been used, check in the typechecker
  2. Declaration: Check if the declaration table contains the symbol
  3. Definition: Check if the declaration table contains the symbol
*)
let expand_void_fn ~(prog : Ast.program_block) : Ast.program_block =
  match prog with
  | Ast.Function_Def_Intermediate _ | Ast.Function_Decl _ | Ast.Typedef _ -> prog
  | Ast.Function_Def { ret_type; ident; params; fn_block } ->
    (match ret_type with
     | Void ->
       Ast.Function_Def
         { ret_type
         ; ident
         ; params
         ; fn_block =
             mark_with_pos
               (Ast.Seq
                  ( fn_block
                  , mark_with_pos Ast.Return_void Lexing.dummy_pos Lexing.dummy_pos ))
               Lexing.dummy_pos
               Lexing.dummy_pos
         }
     | _ -> prog)
;;

let rec expand_program (program_list : Ast.program) : Ast.program =
  expand_helper program_list []

and expand_helper program_list acc =
  match program_list with
  | [] -> acc
  | h :: t -> expand_helper t (match_program h @ acc)

and match_program (mprogram : Ast.mprogram_block) : Ast.mprogram_block list =
  let program_span = get_start_end mprogram in
  let program = Mark.data mprogram in
  match program with
  | Ast.Function_Def_Intermediate { ret_type; ident; params; fn_block } ->
    let decl = Ast.Function_Decl { ret_type; ident; params } in
    let defn_intermediate =
      Ast.Function_Def { ret_type; ident; params; fn_block = expand_ast_list fn_block }
    in
    let defn = expand_void_fn ~prog:defn_intermediate in
    [ mark_with_span defn program_span; mark_with_span decl program_span ]
  | Ast.Function_Decl _ -> [ mprogram ]
  | Ast.Typedef _ -> [ mprogram ]
  | Ast.Function_Def _ ->
    failwith "Not supposed to encounter function def before elaboration"
;;

let elaborate (prog : Ast.program) : Ast.program = List.rev (expand_program prog)
