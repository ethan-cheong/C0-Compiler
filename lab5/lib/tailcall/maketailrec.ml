(* L5 Compiler
 * Basic Accumulation 
 * Author: Wu Meng Hui
 *
 * Transforms ASTs for eligible functions into tail-recursive form.  
 *)

open Core
module A = Ast
module S = Symbol

let fn_to_new = Hashtbl.create (module Symbol)
let fn_to_base = Hashtbl.create (module Symbol)
let base_case = ref None
let ret_fn = ref None
let fn_call = ref None
let new_acc = Ast.(Mark.naked (Var { ident = Symbol.symbol "_acc"; var_type = Dummy }))

let op_is_fn operand fn_ident =
  Ast.(
    match operand with
    | Function_call { ident; _ } when String.(Symbol.name fn_ident = Symbol.name ident) ->
      true
    | _ -> false)
;;

let op_is_const operand =
  Ast.(
    match operand with
    | Const _ -> true
    | _ -> false)
;;

(* Need to return the value as well, either a binop or const *)
let binop_can_tailrec lhs rhs op fn_ident =
  Ast.(
    match op with
    | Plus ->
      if op_is_fn lhs fn_ident && op_is_const rhs
      then (
        match !ret_fn with
        | Some _ -> false
        | None ->
          (match lhs with
           | Function_call { args; ident; return_type } ->
             let new_binop = Binop_pure { rhs = Mark.naked rhs; lhs = new_acc; op } in
             let new_args = List.rev (Mark.naked new_binop :: List.rev args) in
             let new_fn_call = Function_call { ident; args = new_args; return_type } in
             ret_fn := Some new_fn_call;
             true
           | _ -> failwith "lhs is fn"))
      else if op_is_fn rhs fn_ident && op_is_const lhs
      then (
        match !ret_fn with
        | Some _ -> false
        | None ->
          (match rhs with
           | Function_call { args; ident; return_type } ->
             let new_binop = Binop_pure { lhs = Mark.naked lhs; rhs = new_acc; op } in
             let new_args = List.rev (Mark.naked new_binop :: List.rev args) in
             let new_fn_call = Function_call { ident; args = new_args; return_type } in
             ret_fn := Some new_fn_call;
             true
           | _ -> failwith "lhs is fn"))
      else false
    | _ -> false)
;;

(* 
   Exp contains function call AND is commutative 
   1. Assume no nesting.
   2. 
*)
let exp_can_tailrec exp fn_ident =
  Ast.(
    match exp with
    | Paren _ -> failwith "should be elaborated out"
    | Const _ ->
      (match !base_case with
       | None ->
         base_case := Some (Mark.naked exp);
         Hashtbl.set fn_to_base ~key:fn_ident ~data:exp;
         true
       | Some _ -> false)
    | Var _ -> false
    | Binop_pure { lhs; rhs; op } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      binop_can_tailrec lhs_data rhs_data op fn_ident
    | Binop_impure _ -> false
    | Unop _ -> false
    | Comparison _ -> false
    | And _ -> false
    | Or _ -> false
    | Ternary _ -> false
    | Function_call _ ->
      (*False because only want function call in return statement binop *) false
    | _ -> false)
;;

(*  *)
let rec stmt_can_tailrec orig_stmt fn_ident =
  Ast.(
    match orig_stmt with
    | Declare (_, _, mstmt) ->
      let stmt = Mark.data mstmt in
      stmt_can_tailrec stmt fn_ident
    | Return mexp ->
      let exp = Mark.data mexp in
      exp_can_tailrec exp fn_ident
    | If (_, mlt, mlf) ->
      let lt = Mark.data mlt in
      let lf = Mark.data mlf in
      stmt_can_tailrec lt fn_ident && stmt_can_tailrec lf fn_ident
    | While (_, mstmt) ->
      let stmt = Mark.data mstmt in
      stmt_can_tailrec stmt fn_ident
    | Seq (mstmt1, mstmt2) ->
      let stmt1 = Mark.data mstmt1 in
      let stmt2 = Mark.data mstmt2 in
      stmt_can_tailrec stmt1 fn_ident && stmt_can_tailrec stmt2 fn_ident
    | For (_, _, _, mstmt) ->
      let stmt = Mark.data mstmt in
      stmt_can_tailrec stmt fn_ident
    | Asnop_pure_mem_intermediate _
    | Asnop_impure_mem_intermediate _
    | Block_intermediate _
    | Declare_intermediate _ -> failwith "should be elaborated out "
    | Nop -> true
    | _ -> false)
;;

(* Only used for non-ret statements *)
let rec replace_rec_fn operand =
  Ast.(
    match operand with
    | Paren _ -> failwith "paren gone"
    | Var _ | Const _ -> operand
    | Binop_impure { op; lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (replace_rec_fn lhs_data) in
      let new_rhs = Mark.naked (replace_rec_fn rhs_data) in
      Binop_impure { op; lhs = new_lhs; rhs = new_rhs }
    | Unop { op; operand } ->
      let operand_data = Mark.data operand in
      let new_operand = Mark.naked (replace_rec_fn operand_data) in
      Unop { op; operand = new_operand }
    | Comparison { op; lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (replace_rec_fn lhs_data) in
      let new_rhs = Mark.naked (replace_rec_fn rhs_data) in
      Comparison { op; lhs = new_lhs; rhs = new_rhs }
    | And { lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (replace_rec_fn lhs_data) in
      let new_rhs = Mark.naked (replace_rec_fn rhs_data) in
      And { lhs = new_lhs; rhs = new_rhs }
    | Or { lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (replace_rec_fn lhs_data) in
      let new_rhs = Mark.naked (replace_rec_fn rhs_data) in
      Or { lhs = new_lhs; rhs = new_rhs }
    | Ternary { condition; lhs; rhs; result_type } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let condition_data = Mark.data condition in
      let new_lhs = Mark.naked (replace_rec_fn lhs_data) in
      let new_rhs = Mark.naked (replace_rec_fn rhs_data) in
      let new_condition = Mark.naked (replace_rec_fn condition_data) in
      Ternary { condition = new_condition; lhs = new_lhs; rhs = new_rhs; result_type }
    | Alloc _ | Null_pointer -> operand
    | Deref { address; pointer_type } ->
      let address_data = Mark.data address in
      let new_address = Mark.naked (replace_rec_fn address_data) in
      Deref { address = new_address; pointer_type }
    | Alloc_array { size; array_type } ->
      let size_data = Mark.data size in
      let new_size = Mark.naked (replace_rec_fn size_data) in
      Alloc_array { size = new_size; array_type }
    | Array_access { array_type; array; index } ->
      let array_data = Mark.data array in
      let index_data = Mark.data index in
      let new_array = Mark.naked (replace_rec_fn array_data) in
      let new_index = Mark.naked (replace_rec_fn index_data) in
      Array_access { array = new_array; index = new_index; array_type }
    | Struct_access { s; offset; field_type } ->
      let s_data = Mark.data s in
      let new_s = Mark.naked (replace_rec_fn s_data) in
      Struct_access { s = new_s; offset; field_type }
    | Function_call _ ->
      (match !fn_call with
       | Some x -> x
       | None -> failwith "fn_call should exist")
    | _ -> operand)
;;

let update_ret_fn exp =
  Ast.(
    match exp with
    | Const _ -> Mark.data new_acc
    | Binop_pure _ ->
      (match !ret_fn with
       | None -> failwith "ret fn should exit"
       | Some x -> x)
    | _ -> failwith "all other types not allowed in ret fn")
;;

(* Might need to pass in an accumulator as the starting value? *)
(* Also!!! Requires that the "val binop fn()" *)
let rec build_new_function orig_stmt =
  Ast.(
    match orig_stmt with
    | Declare (decl, tau, mstm) ->
      let stmt = Mark.data mstm in
      let stmt_new = Mark.naked (build_new_function stmt) in
      Declare (decl, tau, stmt_new)
    | Assign (mx1, mx2) ->
      let x1 = Mark.data mx1 in
      let x2 = Mark.data mx2 in
      let x1_new = Mark.naked (replace_rec_fn x1) in
      let x2_new = Mark.naked (replace_rec_fn x2) in
      Assign (x1_new, x2_new)
    | Asnop_pure_mem { lhs; op; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let lhs_new = Mark.naked (replace_rec_fn lhs_data) in
      let rhs_new = Mark.naked (replace_rec_fn rhs_data) in
      Asnop_pure_mem { lhs = lhs_new; op; rhs = rhs_new }
    | Asnop_impure_mem { lhs; op; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let lhs_new = Mark.naked (replace_rec_fn lhs_data) in
      let rhs_new = Mark.naked (replace_rec_fn rhs_data) in
      Asnop_impure_mem { lhs = lhs_new; op; rhs = rhs_new }
    | Return mexp ->
      let exp = Mark.data mexp in
      let mexp_new = Mark.naked (update_ret_fn exp) in
      Return mexp_new
    | Return_void -> Return_void
    | If (mexp, mlt, mlf) ->
      let mexp_data = Mark.data mexp in
      let new_mexp = replace_rec_fn mexp_data in
      let lt = Mark.data mlt in
      let lt_new = Mark.naked (build_new_function lt) in
      let lf = Mark.data mlf in
      let lf_new = Mark.naked (build_new_function lf) in
      If (Mark.naked new_mexp, lt_new, lf_new)
    | While (mexp, mstm) ->
      let mexp_data = Mark.data mexp in
      let new_mexp = replace_rec_fn mexp_data in
      let mstm_data = Mark.data mstm in
      let mstm_new = Mark.naked (build_new_function mstm_data) in
      While (Mark.naked new_mexp, mstm_new)
    | Expr_stm mexp ->
      let mexp_data = Mark.data mexp in
      let new_mexp = replace_rec_fn mexp_data in
      Expr_stm (Mark.naked new_mexp)
    | Assert mexp ->
      let mexp_data = Mark.data mexp in
      let new_mexp = replace_rec_fn mexp_data in
      Assert (Mark.naked new_mexp)
    | Seq (mstm1, mstm2) ->
      let mstm_data1 = Mark.data mstm1 in
      let mstm_new1 = Mark.naked (build_new_function mstm_data1) in
      let mstm_data2 = Mark.data mstm2 in
      let mstm_new2 = Mark.naked (build_new_function mstm_data2) in
      Seq (mstm_new1, mstm_new2)
    | Nop -> Nop
    | For _
    | Asnop_pure_mem_intermediate _
    | Asnop_impure_mem_intermediate _
    | Block_intermediate _
    | Declare_intermediate _
    | Postop _ -> failwith "should be elaborated out ")
;;

let update_tail_rec program_block =
  base_case := None;
  ret_fn := None;
  fn_call := None;
  Ast.(
    match program_block with
    | Typedef _
    | Function_Def_Intermediate _
    | Struct_Def _
    | Struct_Def_Intermediate _
    | Struct_Decl _
    | Function_Decl _ -> program_block
    | Function_Def { ret_type; ident; params; fn_block } ->
      let fn_block_data = Mark.data fn_block in
      if not (stmt_can_tailrec fn_block_data ident)
      then program_block
      else (
        match !ret_fn, !base_case with
        | None, _ -> program_block
        | _, None -> program_block
        | Some call, Some base ->
          (match call, base with
           | Function_call { ident; args; return_type }, _ ->
             let args' = List.rev args in
             let args'' = List.tl_exn args' in
             let args''' = List.rev (base :: args'') in
             fn_call := Some (Function_call { ident; args = args'''; return_type });
             let new_params =
               List.rev ((ret_type, Symbol.symbol "_acc") :: List.rev params)
             in
             Hashtbl.set
               fn_to_new
               ~key:ident
               ~data:(Function_call { ident; args = args'''; return_type });
             Function_Def
               { ret_type
               ; ident
               ; params = new_params
               ; fn_block = Mark.naked (build_new_function fn_block_data)
               }
           | _ -> failwith "fn call and const only")))
;;

let rec update_fn_calls_exp ident operand =
  Ast.(
    match operand with
    | Paren _ -> failwith "paren gone"
    | Var _ | Const _ -> operand
    | Binop_impure { op; lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let new_rhs = Mark.naked (update_fn_calls_exp ident rhs_data) in
      Binop_impure { op; lhs = new_lhs; rhs = new_rhs }
    | Unop { op; operand } ->
      let operand_data = Mark.data operand in
      let new_operand = Mark.naked (update_fn_calls_exp ident operand_data) in
      Unop { op; operand = new_operand }
    | Comparison { op; lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let new_rhs = Mark.naked (update_fn_calls_exp ident rhs_data) in
      Comparison { op; lhs = new_lhs; rhs = new_rhs }
    | And { lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let new_rhs = Mark.naked (update_fn_calls_exp ident rhs_data) in
      And { lhs = new_lhs; rhs = new_rhs }
    | Or { lhs; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let new_lhs = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let new_rhs = Mark.naked (update_fn_calls_exp ident rhs_data) in
      Or { lhs = new_lhs; rhs = new_rhs }
    | Ternary { condition; lhs; rhs; result_type } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let condition_data = Mark.data condition in
      let new_lhs = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let new_rhs = Mark.naked (update_fn_calls_exp ident rhs_data) in
      let new_condition = Mark.naked (update_fn_calls_exp ident condition_data) in
      Ternary { condition = new_condition; lhs = new_lhs; rhs = new_rhs; result_type }
    | Alloc _ | Null_pointer -> operand
    | Deref { address; pointer_type } ->
      let address_data = Mark.data address in
      let new_address = Mark.naked (update_fn_calls_exp ident address_data) in
      Deref { address = new_address; pointer_type }
    | Alloc_array { size; array_type } ->
      let size_data = Mark.data size in
      let new_size = Mark.naked (update_fn_calls_exp ident size_data) in
      Alloc_array { size = new_size; array_type }
    | Array_access { array_type; array; index } ->
      let array_data = Mark.data array in
      let index_data = Mark.data index in
      let new_array = Mark.naked (update_fn_calls_exp ident array_data) in
      let new_index = Mark.naked (update_fn_calls_exp ident index_data) in
      Array_access { array = new_array; index = new_index; array_type }
    | Struct_access { s; offset; field_type } ->
      let s_data = Mark.data s in
      let new_s = Mark.naked (update_fn_calls_exp ident s_data) in
      Struct_access { s = new_s; offset; field_type }
    (* Assume that if ident is in hashtable, then it does not need any replacement? *)
    | Function_call { ident = fn_ident; args; return_type } ->
      (match Hashtbl.find fn_to_new ident with
       | Some _ -> operand
       | None ->
         (match Hashtbl.find fn_to_new fn_ident with
          | None -> operand
          | Some _ ->
            let last_arg = Hashtbl.find_exn fn_to_base fn_ident in
            Function_call
              { ident = fn_ident
              ; args = List.rev (Mark.naked last_arg :: List.rev args)
              ; return_type
              }))
    | _ -> operand)
;;

let mark_declare ident decl =
  Ast.(
    match decl with
    | New_var _ -> decl
    | Init (s, mexp) ->
      let mexp_data = Mark.data mexp in
      let decl_new = Mark.naked (update_fn_calls_exp ident mexp_data) in
      Init (s, decl_new))
;;

let rec update_fn_calls_stm ident orig_stmt =
  Ast.(
    match orig_stmt with
    | Declare (mdecl, tau, mstm) ->
      let decl = mark_declare ident mdecl in
      let stmt = Mark.data mstm in
      let stmt_new = Mark.naked (update_fn_calls_stm ident stmt) in
      Declare (decl, tau, stmt_new)
    | Assign (mx1, mx2) ->
      let x1 = Mark.data mx1 in
      let x2 = Mark.data mx2 in
      let x1_new = Mark.naked (update_fn_calls_exp ident x1) in
      let x2_new = Mark.naked (update_fn_calls_exp ident x2) in
      Assign (x1_new, x2_new)
    | Asnop_pure_mem { lhs; op; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let lhs_new = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let rhs_new = Mark.naked (update_fn_calls_exp ident rhs_data) in
      Asnop_pure_mem { lhs = lhs_new; op; rhs = rhs_new }
    | Asnop_impure_mem { lhs; op; rhs } ->
      let lhs_data = Mark.data lhs in
      let rhs_data = Mark.data rhs in
      let lhs_new = Mark.naked (update_fn_calls_exp ident lhs_data) in
      let rhs_new = Mark.naked (update_fn_calls_exp ident rhs_data) in
      Asnop_impure_mem { lhs = lhs_new; op; rhs = rhs_new }
    | Return mexp ->
      (* if the label is in hash table, assume that the return statements are correct *)
      (match Hashtbl.find fn_to_new ident with
       | None ->
         let exp = Mark.data mexp in
         Return (Mark.naked (update_fn_calls_exp ident exp))
       | Some _ -> Return mexp)
    | Return_void -> Return_void
    | If (mexp, mlt, mlf) ->
      let mexp_data = Mark.data mexp in
      let new_mexp = update_fn_calls_exp ident mexp_data in
      let lt = Mark.data mlt in
      let lt_new = Mark.naked (update_fn_calls_stm ident lt) in
      let lf = Mark.data mlf in
      let lf_new = Mark.naked (update_fn_calls_stm ident lf) in
      If (Mark.naked new_mexp, lt_new, lf_new)
    | While (mexp, mstm) ->
      let mexp_data = Mark.data mexp in
      let new_mexp = update_fn_calls_exp ident mexp_data in
      let mstm_data = Mark.data mstm in
      let mstm_new = Mark.naked (update_fn_calls_stm ident mstm_data) in
      While (Mark.naked new_mexp, mstm_new)
    | Expr_stm mexp ->
      let mexp_data = Mark.data mexp in
      let new_mexp = update_fn_calls_exp ident mexp_data in
      Expr_stm (Mark.naked new_mexp)
    | Assert mexp ->
      let mexp_data = Mark.data mexp in
      let new_mexp = update_fn_calls_exp ident mexp_data in
      Assert (Mark.naked new_mexp)
    | Seq (mstm1, mstm2) ->
      let mstm_data1 = Mark.data mstm1 in
      let mstm_new1 = Mark.naked (update_fn_calls_stm ident mstm_data1) in
      let mstm_data2 = Mark.data mstm2 in
      let mstm_new2 = Mark.naked (update_fn_calls_stm ident mstm_data2) in
      Seq (mstm_new1, mstm_new2)
    | Nop -> Nop
    | For _
    | Asnop_pure_mem_intermediate _
    | Asnop_impure_mem_intermediate _
    | Block_intermediate _
    | Declare_intermediate _
    | Postop _ -> failwith "should be elaborated out ")
;;

let update_all_calls program_block =
  base_case := None;
  ret_fn := None;
  fn_call := None;
  Ast.(
    match program_block with
    | Typedef _
    | Function_Def_Intermediate _
    | Struct_Def _
    | Struct_Def_Intermediate _
    | Struct_Decl _
    | Function_Decl _ -> program_block
    | Function_Def { ret_type; ident; params; fn_block } ->
      let fn_block_data = Mark.data fn_block in
      let fn_block_new = Mark.naked (update_fn_calls_stm ident fn_block_data) in
      Function_Def { ret_type; ident; params; fn_block = fn_block_new })
;;

let update_program program =
  Hashtbl.clear fn_to_new;
  let mapped_indiv =
    List.map program ~f:(fun mprog_block ->
      let res = Mark.data mprog_block in
      Mark.naked (update_tail_rec res))
  in
  List.map mapped_indiv ~f:(fun mprog_block ->
    let res = Mark.data mprog_block in
    Mark.naked (update_all_calls res))
;;
