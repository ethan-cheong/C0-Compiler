(* L1 Compiler
 * Elaborate on the initial AST
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
 *)

open Core
module FieldMap = Type_modules.FieldMap
module SymbolTable = Type_modules.SymbolTable

let is_mem_access lhs =
  let lhs_data = Mark.data lhs in
  Ast.(
    match lhs_data with
    | Var _ -> false
    | Deref _ | Array_access _ | Struct_access_parse _ | Cast _ -> true
    | _ -> failwith "only var/deref/arr access/struct access allowed")
;;

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

let rec extract_paren (e : Ast.mexp) : Ast.mexp =
  let e_span = get_start_end e in
  let e_data = Mark.data e in
  Ast.(
    match e_data with
    | Paren e' -> extract_paren e'
    | Var _ | Const _ | Alloc _ | Null_pointer -> e
    | Binop_pure { op; lhs; rhs } ->
      mark_with_span
        (Binop_pure { op; lhs = extract_paren lhs; rhs = extract_paren rhs })
        e_span
    | Binop_impure { op; lhs; rhs } ->
      mark_with_span
        (Binop_impure { op; lhs = extract_paren lhs; rhs = extract_paren rhs })
        e_span
    | Unop { op; operand } ->
      mark_with_span (Unop { op; operand = extract_paren operand }) e_span
    | Function_call { ident; args; return_type } ->
      let extracted_args = List.map args ~f:(fun x -> extract_paren x) in
      mark_with_span (Function_call { ident; args = extracted_args; return_type }) e_span
    | Comparison { op; lhs; rhs } ->
      mark_with_span
        (Comparison { op; lhs = extract_paren lhs; rhs = extract_paren rhs })
        e_span
    | And { lhs; rhs } ->
      mark_with_span (And { lhs = extract_paren lhs; rhs = extract_paren rhs }) e_span
    | Or { lhs; rhs } ->
      mark_with_span (Or { lhs = extract_paren lhs; rhs = extract_paren rhs }) e_span
    | Ternary { condition; lhs; rhs; result_type } ->
      mark_with_span
        (Ternary
           { condition = extract_paren condition
           ; lhs = extract_paren lhs
           ; rhs = extract_paren rhs
           ; result_type
           })
        e_span
    | Deref { address; pointer_type } ->
      mark_with_span (Deref { address = extract_paren address; pointer_type }) e_span
    | Alloc_array { array_type; size } ->
      mark_with_span (Alloc_array { array_type; size = extract_paren size }) e_span
    | Array_access { array; index; array_type } ->
      mark_with_span
        (Array_access
           { array = extract_paren array; index = extract_paren index; array_type })
        e_span
    | Struct_access_parse { s; field; field_type } ->
      mark_with_span
        (Struct_access_parse { s = extract_paren s; field; field_type })
        e_span
    | Struct_access _ -> failwith "no struct access yet"
    | Anno_length e' -> mark_with_span (Anno_length (extract_paren e')) e_span
    | Cast { pointer_type; operand; orig_type } ->
      mark_with_span
        (Cast { pointer_type; operand = extract_paren operand; orig_type })
        e_span
    | String_const _ | Anno_result | Anno_elem _ | Anno_index -> e
    | Forall { arr; condition } ->
      mark_with_span
        (Forall { arr = extract_paren arr; condition = extract_paren condition })
        e_span
    | Exists { arr; condition } ->
      mark_with_span
        (Exists { arr = extract_paren arr; condition = extract_paren condition })
        e_span)
;;

let process_anno (annos : Ast.spec list list) =
  let a = List.concat annos in
  List.map a ~f:(fun spec ->
    Ast.(
      match spec with
      | Requires mexp -> Requires (extract_paren mexp)
      | Ensures mexp -> Ensures (extract_paren mexp)
      | Loop_invariant mexp -> Loop_invariant (extract_paren mexp)
      | Assert_spec mexp -> Assert_spec (extract_paren mexp)))
;;

let expand_postop postop target =
  let target_span = get_start_end target in
  let target_data = Mark.data target in
  let (_ : unit) =
    match target_data with
    | Ast.Deref _ -> failwith "*(exp)++ or *(exp)-- not allowed"
    | _ -> ()
  in
  let elab_target = extract_paren target in
  let const_mexp =
    mark_with_span (Ast.Const { value = Int32.one; const_type = Ast.Int }) target_span
  in
  Ast.Asnop_pure_mem { lhs = elab_target; op = postop; rhs = const_mexp }
;;

(* Expands on the initial mstm list by recursively going into each of the branches
   and processing each statement *)
let rec expand_ast_list (lst : Ast.mstm list) =
  match lst with
  | [] -> mark_with_pos Ast.Nop Lexing.dummy_pos Lexing.dummy_pos
  | h :: t ->
    let h_span = get_start_end h in
    (match Mark.data h with
     | Ast.Declare_intermediate (decl, tau) ->
       mark_with_span (process_decl decl tau t) h_span
     | Ast.Annotated_stm_intermediate (anno_list, mstm) ->
       mark_with_span (process_anno_stm anno_list (mstm :: t)) h_span
     | Ast.Asnop_pure_mem_intermediate { lhs; op; rhs } ->
       let asnop_stm =
         match op with
         | None ->
           mark_with_span (Ast.Assign (extract_paren lhs, extract_paren rhs)) h_span
         | Some x ->
           let extracted_lhs = extract_paren lhs in
           if is_mem_access extracted_lhs
           then
             mark_with_span
               (Ast.Asnop_pure_mem
                  { lhs = extracted_lhs; op = x; rhs = extract_paren rhs })
               h_span
           else
             mark_with_span
               (Ast.Assign
                  ( extracted_lhs
                  , mark_with_span
                      (Ast.Binop_pure
                         { op = x; lhs = extracted_lhs; rhs = extract_paren rhs })
                      h_span ))
               h_span
       in
       mark_with_span (Ast.Seq (asnop_stm, expand_ast_list t)) h_span
     | Asnop_impure_mem_intermediate { lhs; op; rhs } ->
       let asnop_stm =
         match op with
         | None -> failwith "impure should never have None"
         | Some x ->
           let extracted_lhs = extract_paren lhs in
           if is_mem_access extracted_lhs
           then
             mark_with_span
               (Ast.Asnop_impure_mem
                  { lhs = extracted_lhs; op = x; rhs = extract_paren rhs })
               h_span
           else
             mark_with_span
               (Ast.Assign
                  ( extracted_lhs
                  , mark_with_span
                      (Ast.Binop_impure
                         { op = x; lhs = extracted_lhs; rhs = extract_paren rhs })
                      h_span ))
               h_span
       in
       mark_with_span (Ast.Seq (asnop_stm, expand_ast_list t)) h_span
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
  Ast.(
    match stm_data with
    | Declare_intermediate (decl, tau) ->
      mark_with_span (process_decl decl tau []) stm_src
    | Assign (e1, e2) ->
      mark_with_span (Assign (extract_paren e1, extract_paren e2)) stm_src
    | Return e -> mark_with_span (Return (extract_paren e)) stm_src
    | Return_void -> h
    | Nop -> h
    | Expr_stm e -> mark_with_span (Expr_stm (extract_paren e)) stm_src
    | Block_intermediate lst -> expand_ast_list lst
    | If (mexp, s1, s2) ->
      mark_with_span (If (extract_paren mexp, process s1, process s2)) stm_src
    | Seq (s1, s2) -> mark_with_span (Seq (process s1, process s2)) stm_src
    | While (e, s) -> mark_with_span (While (extract_paren e, process s)) stm_src
    | For (s1, s2, e, s3) ->
      mark_with_span (expand_for s1 s2 (extract_paren e) s3) stm_src
    | Declare _ -> h
    | Assert e -> mark_with_span (Assert (extract_paren e)) stm_src
    | Asnop_pure_mem _ -> h
    | Asnop_impure_mem _ -> h
    (* Still required as the ops are options right now *)
    | Asnop_pure_mem_intermediate { lhs; op; rhs } ->
      (match op with
       | None -> mark_with_span (Assign (extract_paren lhs, extract_paren rhs)) stm_src
       | Some x ->
         mark_with_span
           (Asnop_pure_mem { lhs = extract_paren lhs; op = x; rhs = extract_paren rhs })
           stm_src)
    | Asnop_impure_mem_intermediate { lhs; op; rhs } ->
      (match op with
       | None -> failwith "impure asnops always have value"
       | Some x ->
         mark_with_span
           (Asnop_impure_mem { lhs = extract_paren lhs; op = x; rhs = extract_paren rhs })
           stm_src)
    | Postop { postop; target } -> mark_with_span (expand_postop postop target) stm_src
    | Annotated_stm _ -> h
    | Annotated_stm_intermediate (anno_list, h) ->
      mark_with_span (process_anno_stm anno_list [ h ]) stm_src)

(* Elaboration for declarations now only happen after typechecking *)
and process_decl decl tau tail =
  Ast.(
    match decl with
    | New_var _ -> Declare (decl, tau, expand_ast_list tail)
    | Init (s, e) ->
      let new_init = Init (s, extract_paren e) in
      Declare (new_init, tau, expand_ast_list tail))

and process_anno_stm anno_list tail =
  Ast.(Annotated_stm (process_anno anno_list, expand_ast_list tail))

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
  (* Body might have  *)
  let processed_body = process body in
  match Mark.data processed_body with
  | Annotated_stm (anno, true_body) ->
    let dummy_post_block = validate post_block in
    let dummy_post_block_loop_invar =
      Mark.naked (Ast.Annotated_stm (anno, dummy_post_block))
    in
    let dummy_loop_invar = Mark.naked (Ast.Annotated_stm (anno, Mark.naked Ast.Nop)) in
    let anno_post =
      Mark.naked (Ast.Seq (dummy_post_block_loop_invar, dummy_loop_invar))
    in
    let true_body_loop_invar = Mark.naked (Ast.Annotated_stm (anno, true_body)) in
    let dummy_marked_seq = Mark.naked (Ast.Seq (true_body_loop_invar, anno_post)) in
    let dummy_marked_while = Mark.naked (Ast.While (condition, dummy_marked_seq)) in
    (match Mark.data pre_block with
     | Ast.Declare_intermediate (decl, tau) ->
       process_decl decl tau [ dummy_marked_while ]
     | _ -> Ast.Seq (process pre_block, dummy_marked_while))
  | _ ->
    let dummy_marked_post_block = validate post_block in
    let dummy_marked_seq =
      mark_with_pos
        (Ast.Seq (processed_body, dummy_marked_post_block))
        Lexing.dummy_pos
        Lexing.dummy_pos
    in
    let dummy_marked_while =
      mark_with_pos
        (Ast.While (condition, dummy_marked_seq))
        Lexing.dummy_pos
        Lexing.dummy_pos
    in
    (match Mark.data pre_block with
     | Ast.Declare_intermediate (decl, tau) ->
       process_decl decl tau [ dummy_marked_while ]
     | _ -> Ast.Seq (process pre_block, dummy_marked_while))

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
  | Ast.Function_Def_Intermediate _
  | Ast.Function_Decl _
  | Ast.Typedef _
  | Ast.Struct_Def _
  | Ast.Struct_Decl _
  | Ast.Function_Def_Anno_Intermediate _
  | Ast.Struct_Def_Intermediate _ -> prog
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
  | Ast.Function_Def_Anno { ret_type; ident; params; anno; fn_block } ->
    (match ret_type with
     | Void ->
       Ast.Function_Def_Anno
         { ret_type
         ; ident
         ; params
         ; anno
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
  | Function_Def_Anno_Intermediate { ret_type; ident; params; anno; fn_block } ->
    let new_anno = process_anno anno in
    let decl = Ast.Function_Decl { ret_type; ident; params } in
    let defn_intermediate =
      Ast.Function_Def_Anno
        { ret_type; ident; params; anno = new_anno; fn_block = expand_ast_list fn_block }
    in
    let defn = expand_void_fn ~prog:defn_intermediate in
    [ mark_with_span defn program_span; mark_with_span decl program_span ]
  | Ast.Function_Decl _ -> [ mprogram ]
  | Ast.Typedef _ -> [ mprogram ]
  | Ast.Function_Def _ ->
    failwith "Not supposed to encounter function def before elaboration"
  | Ast.Struct_Decl _ -> [ mprogram ]
  | Ast.Struct_Def _ -> failwith "Not supposed to encounter struct_def before elaboration"
  | Ast.Struct_Def_Intermediate { ident; fields } ->
    let field_list_mapped =
      List.map fields ~f:(fun (tau, field_name) -> field_name, tau)
    in
    let (_ : Ast.tau SymbolTable.t) =
      match SymbolTable.of_alist ~growth_allowed:true ~size:10 field_list_mapped with
      | `Ok x -> x
      | `Duplicate_key a ->
        failwith
          (sprintf "duplicate key %s for struct %s" (Symbol.name a) (Symbol.name ident))
    in
    let sdef = Ast.Struct_Def { ident; fields = field_list_mapped } in
    let sdecl = Ast.Struct_Decl { ident } in
    [ mark_with_span sdef program_span; mark_with_span sdecl program_span ]
  | Function_Def_Anno _ -> failwith "no function_def_annno yet"
;;

let elaborate (prog : Ast.program) : Ast.program = List.rev (expand_program prog)
