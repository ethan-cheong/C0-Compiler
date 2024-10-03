(* L1 Compiler
 * TypeChecker
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core
module A = Ast
module SymbolMap = Symbol.Map
module SymbolSet = Type_modules.SymbolSet
module SymbolTable = Type_modules.SymbolTable

(* Typechecking scope *)
type env =
  { gamma : A.tau SymbolMap.t (* Map from variables to their types*)
  ; delta : SymbolSet.t (* Set of variables that are initialized and declared in scope *)
  ; epsilon :
      (* (tau * param_name) list * return_type * defined *)
      (A.param list * A.tau * bool) SymbolTable.t
      (* Set of functions that are declared or defined *)
  ; omega : A.tau SymbolTable.t (* Maps from typedef alias to type *)
  ; used :
      unit SymbolTable.t (* true iff the function is called anywhere in the program *)
  ; returns : bool
      (* if every control flow path through the program terminates with an explicit return statement. *)
  }

let tc_errors : Error_msg.t = Error_msg.create ()

let format_tau = function
  | A.Bool -> "bool"
  | A.Int -> "int"
  | A.Void -> "void"
  | A.Alias s -> Symbol.name s
;;

(* Checks for the main function *)
let validate_ident ~function_name =
  let name_str = Symbol.name function_name in
  String.compare name_str "main" <> 0
;;

(* Ensures that types and number of params of functions are the same across 
   contexts (for example, ensuring called function params match with their 
   declaration) *)
let match_args_params ~(arg_types : A.tau list) ~(declared_param_list : A.param list)
  : bool
  =
  let map2_res =
    List.map2 arg_types declared_param_list ~f:(fun arg_tau (param_tau, _) ->
      match arg_tau, param_tau with
      | A.Int, A.Int -> A.Int
      | A.Bool, A.Bool -> A.Bool
      | _ ->
        failwith
          (sprintf "incompatible types %s %s" (format_tau arg_tau) (format_tau param_tau)))
  in
  match map2_res with
  | Ok _ -> true
  | Unequal_lengths -> failwith "parameters have different lengths"
;;

let match_symbol sym target_sym : bool = Symbol.compare sym target_sym = 0

let extract_tau ~ctx tau' =
  match tau' with
  | A.Int | A.Bool | A.Void -> tau'
  | A.Alias s ->
    (match SymbolTable.find ctx.omega s with
     | Some x -> x
     | None -> failwith (sprintf "%s not a valid decl type" (format_tau tau')))
;;

(** Typechecks expressions recursively, and returns the type that they should 
    typecheck to. Throws an error if synthesizing the type fails. *)
let rec syn_exp (ctx : env) (mexp : A.mexp) : A.tau =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span mexp) ~msg;
    raise Error_msg.Error
  in
  match Mark.data mexp with
  | A.Var curr_sym ->
    let search = SymbolMap.find ctx.gamma curr_sym in
    (match search with
     | None -> error ~msg:(sprintf "Var %s has no associated type" (Symbol.name curr_sym))
     | Some x ->
       let (_ : unit) =
         match SymbolSet.find ctx.delta ~f:(match_symbol curr_sym) with
         | None ->
           error ~msg:(sprintf "Var %s not initialized before use" (Symbol.name curr_sym))
         | Some _ -> ()
       in
       x)
  | A.Const (_, tau) -> tau
  | A.Binop_pure { op = _; lhs; rhs } ->
    let lhs_type = syn_exp ctx lhs in
    let rhs_type = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Int, Int -> lhs_type
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for int binop (expected int, int)"
              (format_tau a)
              (format_tau b)))
  | A.Binop_impure { lhs; rhs; _ } ->
    (* Currently only uses ints *)
    let lhs_type = syn_exp ctx lhs in
    let rhs_type = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Int, Int -> lhs_type
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for int binop (expected int, int)"
              (format_tau a)
              (format_tau b)))
  | A.Unop { op; operand } ->
    let operand_type = syn_exp ctx operand in
    (match op with
     | Negative | Bitwise_not ->
       (match operand_type with
        | Int -> operand_type
        | b ->
          error
            ~msg:
              (sprintf "Incompatible type (%s) for - or ~ (expected int)" (format_tau b)))
     | Not ->
       (match operand_type with
        | Bool -> operand_type
        | i ->
          error
            ~msg:(sprintf "incompatible type (%s) for ! (expected bool)" (format_tau i))))
  | A.Comparison { op; lhs; rhs } ->
    let lhs_type = syn_exp ctx lhs in
    let rhs_type = syn_exp ctx rhs in
    (match op with
     | Less | Less_equal | Greater | Greater_equal ->
       (match lhs_type, rhs_type with
        | Int, Int -> Bool
        | a, b ->
          error
            ~msg:
              (sprintf
                 "Incompatible types (%s, %s) for comparison  (expected int, int)"
                 (format_tau a)
                 (format_tau b)))
     | Equal | Not_equal ->
       (match lhs_type, rhs_type with
        | Bool, Bool | Int, Int -> Bool
        | a, b ->
          error
            ~msg:
              (sprintf
                 "incompatible types for (%s, %s) an eq/neq operation (types not the \
                  same)"
                 (format_tau a)
                 (format_tau b))))
  | And { lhs; rhs } | Or { lhs; rhs } ->
    let lhs_type = syn_exp ctx lhs in
    let rhs_type = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Bool, Bool -> lhs_type
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for comparison  (expected bool, bool)"
              (format_tau a)
              (format_tau b)))
  | Ternary { condition; lhs; rhs } ->
    let cond_type = syn_exp ctx condition in
    let lhs_type = syn_exp ctx lhs in
    let rhs_type = syn_exp ctx rhs in
    (match cond_type with
     | Int | Void | Alias _ ->
       error ~msg:"Incompatible types (condition of a ternary operator is not bool)"
     | Bool ->
       (match lhs_type, rhs_type with
        | Bool, Bool | Int, Int -> lhs_type
        | a, b ->
          error
            ~msg:
              (sprintf
                 "incompatible types (%s, %s) for ternary operator (expected 't, 't)"
                 (format_tau a)
                 (format_tau b))))
  | A.Function_call { ident; args } ->
    assert (
      match SymbolMap.find ctx.gamma ident with
      | None -> true
      | Some _ -> failwith (sprintf "%s has been declared in gamma" (Symbol.name ident)));
    (* Need to get the return type of the function call, and match the args with the function in epsilon *)
    let arg_types = extract_exp_type ctx ~args in
    let params, fn_tau =
      match SymbolTable.find ctx.epsilon ident with
      | Some (lst, fn_tau, _) -> lst, fn_tau
      | None -> failwith "function not declared before use"
    in
    assert (match_args_params ~arg_types ~declared_param_list:params);
    let (_ : unit) = SymbolTable.find_or_add ctx.used ident ~default:(fun () -> ()) in
    fn_tau

and extract_exp_type ctx ~args = List.map args ~f:(fun arg -> syn_exp ctx arg)

(** Returns [env] if the statement typechecks. 
    [tau] is the return type of the function that mstm is contained in, 
    and only checked during returns. *)
let rec chk_stm (ctx : env) (mstm : A.mstm) (tau : A.tau) : env =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span mstm) ~msg;
    raise Error_msg.Error
  in
  let stm = Mark.data mstm in
  match stm with
  | Declare (decl, tau', s) ->
    (* Need to ensure that the tau is valid in omega *)
    let validated_tau =
      match extract_tau ~ctx tau' with
      | A.Int -> A.Int
      | A.Bool -> A.Bool
      | A.Alias _ -> failwith "no more aliases allowed after validation"
      | Void -> failwith "void used as declaration type"
    in
    (* Need to ensure that the declaration is not in omega or epsilon *)
    (match decl with
     | A.New_var id ->
       assert (
         match SymbolTable.find ctx.omega id with
         | None -> true
         | Some _ -> failwith (sprintf "declaration %s is a typedef" (Symbol.name id)));
       (match SymbolMap.find ctx.gamma id with
        | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name id))
        | None ->
          chk_stm
            { ctx with
              gamma = SymbolMap.set ctx.gamma ~key:id ~data:validated_tau
            ; delta = SymbolSet.remove ctx.delta id
            }
            s
            tau)
       (* If s returns, it sets this returns to be true. *)
     | A.Init (id, assign_exp) ->
       assert (
         match SymbolTable.find ctx.omega id with
         | None -> true
         | Some _ -> failwith (sprintf "declaration %s is a typedef" (Symbol.name id)));
       let assign_tau = syn_exp ctx assign_exp in
       assert (
         match validated_tau, assign_tau with
         | A.Int, A.Int | A.Bool, A.Bool -> true
         | _ -> false);
       (match SymbolMap.find ctx.gamma id with
        | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name id))
        | None ->
          chk_stm
            { ctx with
              gamma = SymbolMap.set ctx.gamma ~key:id ~data:validated_tau
            ; delta = SymbolSet.add ctx.delta id
            }
            s
            tau)
       (* Validate the expression, match the find, then do the update and everything *))
  | Assign (x, e) ->
    let search = SymbolMap.find ctx.gamma x in
    let var_type =
      match search with
      | None ->
        error ~msg:(sprintf "Not declared before initialization: `%s`" (Symbol.name x))
      | Some t -> t
    in
    let exp_type = syn_exp ctx e in
    (match var_type, exp_type with
     | Int, Int | Bool, Bool ->
       { ctx with gamma = ctx.gamma; delta = SymbolSet.add ctx.delta x; returns = false }
       (* Assign will never return*)
     | a, b ->
       error
         ~msg:
           (sprintf
              "Expression of type %s was assigned to variable of type %s for %s"
              (format_tau b)
              (format_tau a)
              (Symbol.name x)))
  | Return e ->
    let exp_type = syn_exp ctx e in
    let validated_tau =
      match extract_tau ~ctx tau with
      | A.Bool -> A.Bool
      | A.Int -> A.Int
      | A.Alias _ | A.Void ->
        error
          ~msg:
            (sprintf
               "Return expression tau should only be bool or int, got %s"
               (format_tau tau))
    in
    (match validated_tau, exp_type with
     (* Return always returns *)
     | Bool, Bool | Int, Int ->
       { ctx with
         gamma = ctx.gamma
       ; delta = SymbolSet.of_list (SymbolMap.keys ctx.gamma)
       ; returns = true
       }
     | t, e ->
       error
         ~msg:
           (sprintf
              "Return expression was expected to have type %s but returned type %s"
              (format_tau t)
              (format_tau e)))
  | If (e, s1, s2) ->
    (match syn_exp ctx e with
     | Bool ->
       let ctx' = chk_stm ctx s1 tau in
       let ctx'' = chk_stm ctx s2 tau in
       { ctx with
         delta = SymbolSet.inter ctx'.delta ctx''.delta
       ; returns = ctx'.returns && ctx''.returns
       }
       (* If returns if both s1 and s2 return *)
     | Int | Void | Alias _ ->
       error ~msg:"Expression in if statement was expected to have type bool")
  | While (e, s) ->
    (match syn_exp ctx e with
     | A.Bool ->
       let (_ : env) = chk_stm ctx s tau in
       { ctx with returns = false }
       (* While will never return *)
     | A.Int | A.Void | A.Alias _ ->
       error ~msg:"Expression in if statement was expected to have type bool")
  | Nop -> { ctx with returns = false } (* Nop will never return *)
  | Seq (s1, s2) ->
    let ctx' = chk_stm ctx s1 tau in
    let ctx'' = chk_stm { ctx with delta = ctx'.delta } s2 tau in
    { ctx with delta = ctx''.delta; returns = ctx'.returns || ctx''.returns }
    (* Seq returns if either s1 or s2 return*)
  | For _ -> failwith "for loops should have been elaborated away before typechecking"
  | Expr_stm e ->
    let (_ : A.tau) = syn_exp ctx e in
    ctx (* Just check the expression and keep the original context *)
  | Block_intermediate _ ->
    failwith "Block intermediates should have been elaborated away before typechecking"
  | Declare_intermediate _ ->
    failwith "Declare intermediates should have been elaborated away before typechecking"
  | Assign_exp _ ->
    failwith "Assign_exp should have been elaborated away before typechecking"
  | Assert e ->
    let (exp_type : A.tau) = syn_exp ctx e in
    assert (
      match exp_type with
      | A.Bool -> true
      | A.Int | A.Void | A.Alias _ -> false);
    ctx
  | Return_void ->
    (match tau with
     (* Return_void doesn't return *)
     | A.Void ->
       { ctx with
         gamma = ctx.gamma
       ; delta = SymbolSet.of_list (SymbolMap.keys ctx.gamma)
       ; returns = false
       }
     | _ -> error ~msg:(sprintf "fails, function of type tau returns %s" (format_tau tau)))
;;

(* Check that there are no duplicate parameter names *)
let unique_fn_params ~(params : A.param list) : unit SymbolTable.t =
  let param_table = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let (_ : unit) =
    List.iter params ~f:(fun (_, x) ->
      assert (
        match SymbolTable.add param_table ~key:x ~data:() with
        | `Ok -> true
        | `Duplicate ->
          failwith (sprintf "duplicate parameter name {%s} found" (Symbol.name x))))
  in
  param_table
;;

(* Make sure that the types are all in omega and return them *)
let valid_type_fn_params (ctx : env) ~(params : A.param list) : A.param list =
  List.map params ~f:(fun (x_tau, x) ->
    let ret_tau =
      match x_tau with
      | A.Int | A.Bool -> x_tau
      | Void -> failwith "void not a valid type"
      | Alias s ->
        (match SymbolTable.find ctx.omega s with
         | Some tau_type -> tau_type
         | None -> failwith (sprintf "%s is not a valid type" (format_tau x_tau)))
    in
    ret_tau, x)
;;

(* Get return type of the function *)
let valid_fn_type (ctx : env) ~(ret_type : A.tau) : A.tau =
  match ret_type with
  | A.Int | A.Bool | A.Void -> ret_type
  | A.Alias s ->
    (match SymbolTable.find ctx.omega s with
     | Some tau_type -> tau_type
     | None -> failwith (sprintf "%s is not a valid type" (Symbol.name s)))
;;

(* Identifiers must not be in omega *)
let ident_not_in_omega (ctx : env) ~ident : bool =
  match SymbolTable.find ctx.omega ident with
  | Some _ ->
    failwith (sprintf "Alias t %s has already been type-defed" (Symbol.name ident))
  | None -> true
;;

let args_not_in_omega ~(ctx : env) ~(params : A.param list) : bool =
  List.iter params ~f:(fun (_, ident) -> assert (ident_not_in_omega ctx ~ident));
  true
;;

(* Check that function parameters are the same across declarations *)
let match_declared_fn_params ~param_list_updated ~declared_param_list =
  let map2_res =
    List.map2 param_list_updated declared_param_list ~f:(fun (tau_x1, _) (tau_x2, _) ->
      match tau_x1, tau_x2 with
      | A.Int, A.Int -> A.Int
      | A.Bool, A.Bool -> A.Bool
      | _ ->
        failwith
          (sprintf "incompatible types %s %s" (format_tau tau_x1) (format_tau tau_x2)))
  in
  match map2_res with
  | Ok a -> a
  | Unequal_lengths -> failwith "parameters have different lengths"
;;

(* Ensure that the actual return types of functions match with their declarations *)
let match_ret_types ~tau_ret_type ~declared_ret_type =
  match tau_ret_type, declared_ret_type with
  | A.Int, A.Int -> A.Int
  | A.Bool, A.Bool -> A.Bool
  | A.Void, A.Void -> A.Void
  | _ ->
    failwith
      (sprintf
         "incompatible types %s %s"
         (format_tau tau_ret_type)
         (format_tau declared_ret_type))
;;

let add_args_to_table ~ctx ~params =
  let added_gamma =
    List.fold_left params ~init:ctx.gamma ~f:(fun gamma (param_tau, ident) ->
      let extracted_tau = extract_tau ~ctx param_tau in
      let extracted_tau' =
        match extracted_tau with
        | A.Int | A.Bool -> extracted_tau
        | A.Alias _ -> failwith "alias not allowed after extracting tau"
        | A.Void -> failwith "void not allowed in params for function definition"
      in
      SymbolMap.set gamma ~key:ident ~data:extracted_tau')
  in
  let added_delta =
    List.fold_left params ~init:ctx.delta ~f:(fun delta (_, ident) ->
      SymbolSet.add delta ident)
  in
  { ctx with gamma = added_gamma; delta = added_delta }
;;

(* Typecheck a function definition, which comprise the function bodies. *)
let typecheck_fndef ctx ~ret_type ~param_list ~fn_block =
  (* All the args have to be added into the context like a declaration *)
  let curr_ctx =
    { gamma = SymbolMap.empty
    ; delta = SymbolSet.empty
    ; omega = ctx.omega
    ; epsilon = ctx.epsilon
    ; used = ctx.used
    ; returns = false
    }
  in
  let curr_ctx' = add_args_to_table ~ctx:curr_ctx ~params:param_list in
  let new_ctx = chk_stm curr_ctx' fn_block ret_type in
  let validated_tau =
    match extract_tau ~ctx:new_ctx ret_type with
    | A.Int -> A.Int
    | A.Bool -> A.Bool
    | A.Void -> A.Void (* Should be allowed here, for function definition *)
    | A.Alias _ -> failwith "no more aliases allowed after validation"
  in
  match new_ctx.returns, validated_tau with
  | true, A.Int | true, A.Bool | false, A.Void -> new_ctx
  | _ ->
    failwith
      (sprintf
         "ret_type %s does not align with function return %s"
         (format_tau validated_tau)
         (string_of_bool new_ctx.returns))
;;

let rec check_program (ctx : env) (program : A.program_block) : env =
  match program with
  | Function_Def { ret_type; ident; params; fn_block } ->
    check_fndef ctx ~ret_type ~ident ~params ~fn_block
  | Function_Decl { ret_type; ident; params } -> check_fndecl ctx ~ret_type ~ident ~params
  | Typedef { original; alias } -> check_typedef ctx ~original ~alias
  | Function_Def_Intermediate _ ->
    failwith "fn_defn_intermediate not allowed after elaboration"

(* Typecheck a function definition *)
and check_typedef (ctx : env) ~(original : Symbol.t) ~(alias : Symbol.t) : env =
  let original_type =
    match SymbolTable.find ctx.omega original with
    | Some x -> x
    | None -> failwith (sprintf "Original t %s has no type" (Symbol.name original))
  in
  assert (
    match SymbolTable.find ctx.omega alias with
    | Some _ ->
      failwith (sprintf "Alias t %s has already been type-defed" (Symbol.name alias))
    | None -> true);
  assert (
    (* Cannot have been defined as a function *)
    match SymbolTable.find ctx.epsilon alias with
    | Some _ -> failwith (sprintf "Alias %s used as function name" (Symbol.name alias))
    | None -> true);
  assert (
    match SymbolTable.add ctx.omega ~key:alias ~data:original_type with
    | `Ok -> true
    | `Duplicate -> failwith "adding alias to omega failed");
  ctx

(* Need to return the fresh context *)
and check_fndecl (ctx : env) ~ret_type ~ident ~params =
  assert (ident_not_in_omega ctx ~ident);
  assert (args_not_in_omega ~ctx ~params);
  match SymbolTable.find ctx.epsilon ident with
  | Some (declared_param_list, declared_ret_type, _) ->
    let (_ : unit SymbolTable.t) = unique_fn_params ~params in
    let param_list_updated = valid_type_fn_params ctx ~params in
    let (_ : A.tau list) =
      match_declared_fn_params ~param_list_updated ~declared_param_list
    in
    let tau_ret_type = valid_fn_type ctx ~ret_type in
    let (_ : A.tau) = match_ret_types ~tau_ret_type ~declared_ret_type in
    ctx
  | None ->
    let (_ : unit SymbolTable.t) = unique_fn_params ~params in
    let param_list_updated = valid_type_fn_params ctx ~params in
    let tau_ret_type = valid_fn_type ctx ~ret_type in
    (* Since there is nothing in epsilon yet, function is not yet defined *)
    assert (
      match
        SymbolTable.add
          ctx.epsilon
          ~key:ident
          ~data:(param_list_updated, tau_ret_type, false)
      with
      (* Declaration after definition is fine because if it returns, it will not update hashtable *)
      | `Ok -> true
      | `Duplicate -> false);
    ctx

and check_fndef (ctx : env) ~ret_type ~ident ~params ~fn_block =
  (* 
     1. Assume that the declaration typechecks (since it is elaborated out)
     1a. Means can ignore the checks that we do for function declaration
     2. Make sure that the function has not yet been defined
     2a. Function body must typecheck
  *)
  match SymbolTable.find ctx.epsilon ident with
  | Some (_, _, defined) ->
    assert (not defined);
    let (param_list : A.param list) = valid_type_fn_params ctx ~params in
    let ret_ctx = typecheck_fndef ctx ~ret_type ~param_list ~fn_block in
    let (_ : unit) =
      SymbolTable.update ret_ctx.epsilon ident ~f:(fun some_key ->
        match some_key with
        | None -> failwith "need to have the function declared"
        | Some (params, curr_tau, returns) ->
          assert (not returns);
          params, curr_tau, true)
    in
    ret_ctx
  | None -> failwith "a declaration should have been made before a definition"

and check_header (ctx : env) (program : A.program_block) : env =
  match program with
  | Function_Def _ -> failwith "function defs not allowed in headers"
  | Function_Decl { ret_type; ident; params } ->
    assert (validate_ident ~function_name:ident);
    check_fndecl ctx ~ret_type ~ident ~params
  | Typedef { original; alias } -> check_typedef ctx ~original ~alias
  | Function_Def_Intermediate _ -> failwith "fn_defn_intermediate not allowed in headers"
;;

let validate_used ~used ~epsilon =
  SymbolTable.iter_keys used ~f:(fun key ->
    match SymbolTable.find epsilon key with
    | Some (_, _, defines) -> assert defines
    | None -> failwith "function somehow used but not declared")
;;

let typecheck (program : A.program) (header_ctx : env) =
  let omega = header_ctx.omega in
  let epsilon = header_ctx.epsilon in
  let used = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let ctx =
    { gamma = SymbolMap.empty
    ; delta = SymbolSet.empty
    ; omega
    ; epsilon
    ; used
    ; returns = false
    }
  in
  (* Main function is always declared before the start of the c0 file*)
  let (_ : unit) =
    match
      SymbolTable.add epsilon ~key:(Symbol.symbol "main") ~data:([], A.Int, false)
    with
    | `Ok -> ()
    | `Duplicate -> failwith "wtf is gg on here lol"
  in
  (* main can be called by any function in a c0 file *)
  let (_ : unit) =
    match SymbolTable.add used ~key:(Symbol.symbol "main") ~data:() with
    | `Ok -> ()
    | `Duplicate -> failwith "wtf is gg on here lol"
  in
  (* *)
  let rec helper helper_ctx progs =
    match progs with
    | [] -> helper_ctx
    | h :: t ->
      let checked_ctx = check_program helper_ctx (Mark.data h) in
      helper checked_ctx t
  in
  let { used; epsilon; _ } = helper ctx program in
  validate_used ~used ~epsilon
;;

let header_typecheck (program : A.program) =
  let omega = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let epsilon = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let used = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let ctx =
    { gamma = SymbolMap.empty
    ; delta = SymbolSet.empty
    ; omega
    ; epsilon
    ; used
    ; returns = false
    }
  in
  (* Int and bool are always valid type names, so they can be aliased to *)
  let (_ : unit) =
    match SymbolTable.add omega ~key:(Symbol.symbol "int") ~data:A.Int with
    | `Ok -> ()
    | `Duplicate -> failwith "wtf is gg on here lol"
  in
  let (_ : unit) =
    match SymbolTable.add omega ~key:(Symbol.symbol "bool") ~data:A.Bool with
    | `Ok -> ()
    | `Duplicate -> failwith "wtf is gg on here lol"
  in
  let rec helper helper_ctx progs =
    match progs with
    | [] -> helper_ctx
    | h :: t ->
      let checked_ctx = check_header helper_ctx (Mark.data h) in
      helper checked_ctx t
  in
  let res_ctx = helper ctx program in
  let (_ : unit) =
    SymbolTable.map_inplace res_ctx.epsilon ~f:(fun (params, tau, _) -> params, tau, true)
  in
  res_ctx
;;
