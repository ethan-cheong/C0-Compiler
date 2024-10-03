(* L1 Compiler
 * Elaborate on the initial AST
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
 * Elaborate out the initialisation of a declaration after type checking
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

(* Helper function to generate the source span, will generate a dummy one if there isn't a span for a given statement *)
let get_start_end marked_stmt =
  match Mark.src_span marked_stmt with
  | Some span -> span
  | None -> Mark.of_positions Lexing.dummy_pos Lexing.dummy_pos
;;

(* Expands on the initial mstm list by recursively going into each of the branches
   and processing each statement *)
let rec process h =
  let stm_data = Mark.data h in
  let stm_src = get_start_end h in
  match stm_data with
  (* If have declare intermediate, need to process it... *)
  | Ast.Declare_intermediate _ -> failwith "no more declare_intermediates after typecheck"
  | Ast.Block_intermediate _ -> failwith "no more blocks after typecheck"
  | Ast.For _ -> failwith "no more for after typecheck"
  | Ast.Assign (_, _) -> h
  | Ast.Return _ -> h
  | Ast.Return_void -> h
  | Ast.Nop -> h
  | Ast.Expr_stm _ -> h
  | Ast.Assign_exp _ -> h
  | Ast.Assert _ -> h
  | Ast.If (mexp, s1, s2) ->
    mark_with_span (Ast.If (mexp, process s1, process s2)) stm_src
  | Ast.Seq (s1, s2) -> mark_with_span (Ast.Seq (process s1, process s2)) stm_src
  | Ast.While (e, s) -> mark_with_span (Ast.While (e, process s)) stm_src
  | Ast.Declare (decl, tau, mstm) -> mark_with_span (process_decl decl tau mstm) stm_src

(* Elaborates on a declaration statement. Splits up a declare that initialises a value
  into a declaration of a new variable and an assignment *)
and process_decl decl tau mstm =
  match decl with
  | Ast.New_var _ -> Ast.Declare (decl, tau, process mstm)
  | Ast.Init (sym, mexp) ->
    let assign_mstm =
      mark_with_pos (Ast.Assign (sym, mexp)) Lexing.dummy_pos Lexing.dummy_pos
    in
    let mstm_span = get_start_end mstm in
    Ast.Declare
      ( Ast.New_var sym
      , tau
      , mark_with_span (Ast.Seq (assign_mstm, process mstm)) mstm_span )
;;

let elaborate_decl (program_list : Ast.program) : Ast.program =
  List.map program_list ~f:(fun mprog ->
    let span = get_start_end mprog in
    let prog = Mark.data mprog in
    match prog with
    | Ast.Function_Def { ret_type; ident; params; fn_block } ->
      mark_with_span
        (Ast.Function_Def { ret_type; ident; params; fn_block = process fn_block })
        span
    | Ast.Function_Decl _ | Ast.Typedef _ -> mprog
    | Ast.Function_Def_Intermediate _ ->
      failwith "no more function def intermediate after typecheck")
;;
