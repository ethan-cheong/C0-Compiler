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
  ; sigma : (A.tau SymbolTable.t * bool) SymbolTable.t
      (* namespace for structs and whether defined *)
  ; used :
      unit SymbolTable.t (* true iff the function is called anywhere in the program *)
  ; returns : bool
      (* if every control flow path through the program terminates with an explicit return statement. *)
  }

let tc_errors : Error_msg.t = Error_msg.create ()

let get_start_end marked_stmt =
  match Mark.src_span marked_stmt with
  | Some span -> span
  | None -> Mark.of_positions Lexing.dummy_pos Lexing.dummy_pos
;;

let rec format_tau = function
  | A.Bool -> "bool"
  | A.Int -> "int"
  | A.Void -> "void"
  | A.Alias s -> Symbol.name s
  | Any -> "any*"
  | Struct s -> sprintf "struct %s" (Symbol.name s)
  | Pointer tau -> sprintf "*%s" (format_tau tau)
  | Array tau -> sprintf "array %s" (format_tau tau)
  | Dummy -> "dummy"
;;

let assert_struct_defined ~ctx s_name =
  match SymbolTable.find ctx.sigma s_name with
  | Some (_, defined) -> assert defined
  | None -> failwith (sprintf "%s not defined" (Symbol.name s_name))
;;

let rec extract_tau ~ctx ?(function_call = false) ?(req_struct_defined = false) tau =
  A.(
    match tau with
    | Int | Bool -> tau
    (* In case it's an alias *)
    (* If pointer, then struct does not have to be defined *)
    | Pointer tau' -> Pointer (extract_tau ~ctx ~function_call tau')
    | Array tau' -> Array (extract_tau ~ctx ~function_call tau')
    | Struct s ->
      if req_struct_defined then assert_struct_defined ~ctx s;
      Struct s
    | Any -> tau
    | Void ->
      if function_call then Void else failwith "void used when not in function call"
    | Alias s ->
      (match SymbolTable.find ctx.omega s with
       | Some x -> extract_tau ~ctx ~function_call ~req_struct_defined x
       | None -> failwith (sprintf "%s not a valid alias" (Symbol.name s)))
    | Dummy -> failwith (sprintf "dummy not a valid tau"))
;;

(* Need to compare  *)
let rec compare_tau ~ctx ?(is_ret_type = false) t1 t2 : A.tau =
  match t1, t2 with
  | A.Int, A.Int -> A.Int
  | Bool, Bool -> Bool
  | Pointer t1', Pointer t2' -> Pointer (compare_tau ~ctx t1' t2')
  | Struct s1, Struct s2 ->
    if String.compare (Symbol.name s1) (Symbol.name s2) <> 0
    then
      failwith
        (sprintf "struct %s and %s are incompatible" (Symbol.name s1) (Symbol.name s2));
    Struct s1
  | Array t1', Array t2' -> Array (compare_tau ~ctx t1' t2')
  (* Type subsumption rule *)
  | Any, Pointer p -> Pointer (extract_tau ~ctx p)
  | Pointer p, Any -> Pointer (extract_tau ~ctx p)
  | Any, Any -> Any
  | Void, Void ->
    if is_ret_type then Void else failwith "void, void received but not a return type"
  | _, _ ->
    failwith
      (sprintf
         "incompatible types (%s, %s), (expected 't, 't)"
         (format_tau t1)
         (format_tau t2))
;;

(* Checks for the main function *)
let validate_ident ~function_name =
  let name_str = Symbol.name function_name in
  String.compare name_str "main" <> 0
;;

(* Ensures that types and number of params of functions are the same across 
   contexts (for example, ensuring called function params match with their 
   declaration) *)
let match_args_params
  ~(ctx : env)
  ~(arg_types : (A.tau * A.mexp) list)
  ~(declared_param_list : A.param list)
  : A.mexp list
  =
  let map2_res =
    List.map2 arg_types declared_param_list ~f:(fun (arg_tau, arg_exp) (param_tau, _) ->
      let (_ : A.tau) = compare_tau ~ctx arg_tau param_tau in
      arg_exp)
  in
  match map2_res with
  | Ok x -> x
  | Unequal_lengths -> failwith "parameters have different lengths"
;;

let match_symbol sym target_sym : bool = Symbol.compare sym target_sym = 0

let extract_field_tau ~ctx struct_name field_name : A.tau =
  match SymbolTable.find ctx.sigma struct_name with
  | None -> failwith (sprintf "%s not a struct name" (Symbol.name struct_name))
  | Some (fields, _) ->
    (match SymbolTable.find fields field_name with
     | None ->
       failwith
         (sprintf
            "%s not a valid field for %s"
            (Symbol.name field_name)
            (Symbol.name struct_name))
     | Some tau -> tau)
;;

let validate_lvalue exp : bool =
  A.(
    match exp with
    | Var _ -> true
    | Const _ -> failwith "const not lvalue"
    | Binop_pure _ | Binop_impure _ -> failwith "binop not lvalue"
    | Unop _ -> failwith "unop not lvalue"
    | Function_call _ -> failwith "function_call not lvalue"
    | Comparison _ -> failwith "comparison not lvalue"
    | And _ -> failwith "and not lvalue"
    | Or _ -> failwith "or not lvalue"
    | Ternary _ -> failwith "ternary exp not lvalue"
    | Alloc _ -> failwith "alloc not lvalue"
    | Alloc_array _ -> failwith "alloc_array not lvalue"
    | Null_pointer -> failwith "NULL not lvalue"
    | Paren _ -> failwith "no more paren"
    | Array_access _ -> true
    | Deref _ -> true
    | Struct_access_parse _ -> true
    | Struct_access _ -> failwith "no struct access elab yet")
;;

let rec extract_lvalue_symbol exp : Symbol.t =
  A.(
    match exp with
    | Var { ident; _ } -> ident
    | Const _
    | Binop_pure _
    | Binop_impure _
    | Unop _
    | Function_call _
    | Comparison _
    | And _
    | Or _
    | Ternary _
    | Alloc _
    | Alloc_array _
    | Paren _
    | Struct_access _
    | Null_pointer -> failwith "cannot extract lvalue"
    | Array_access { array; _ } -> extract_lvalue_symbol (Mark.data array)
    | Deref { address; _ } -> extract_lvalue_symbol (Mark.data address)
    | Struct_access_parse { s; _ } -> extract_lvalue_symbol (Mark.data s))
;;

let assert_small_type tau =
  A.(
    match tau with
    | Void | Int | Bool | Pointer _ | Array _ | Any -> ()
    | Struct _ -> failwith "struct used where a small type should be used"
    | Dummy | Alias _ -> failwith "Alias and dummy should no longer exist")
;;

(* Needs to return both the tau and the exp so that it can replace the exp wherever its called *)

(** Typechecks expressions recursively, and returns the type that they should 
    typecheck to. Throws an error if synthesizing the type fails. *)
let rec syn_exp (ctx : env) ?(initializing = false) (mexp : A.mexp) : A.tau * A.mexp =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span mexp) ~msg;
    raise Error_msg.Error
  in
  let exp_data = Mark.data mexp in
  let span = get_start_end mexp in
  match exp_data with
  | A.Var { ident; _ } ->
    let search = SymbolMap.find ctx.gamma ident in
    (match search with
     | None -> error ~msg:(sprintf "Var %s has no associated type" (Symbol.name ident))
     | Some x ->
       if not initializing
       then (
         match SymbolSet.find ctx.delta ~f:(match_symbol ident) with
         | None ->
           error ~msg:(sprintf "Var %s not initialized before use" (Symbol.name ident))
         | Some _ -> ());
       x, Mark.mark (A.Var { ident; var_type = x }) span)
  | A.Const { value; const_type } ->
    let validated_tau = extract_tau ~ctx const_type in
    validated_tau, Mark.mark (A.Const { value; const_type = validated_tau }) span
  | A.Binop_pure { op; lhs; rhs } ->
    (* Must only be ints, because we only do operations on these *)
    let lhs_type, lhs_exp = syn_exp ctx lhs in
    let rhs_type, rhs_exp = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Int, Int ->
       lhs_type, Mark.mark (A.Binop_pure { lhs = lhs_exp; rhs = rhs_exp; op }) span
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for int binop (expected int, int)"
              (format_tau a)
              (format_tau b)))
  | A.Binop_impure { op; lhs; rhs } ->
    (* Only ever uses ints *)
    let lhs_type, lhs_exp = syn_exp ctx lhs in
    let rhs_type, rhs_exp = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Int, Int ->
       lhs_type, Mark.mark (A.Binop_impure { lhs = lhs_exp; rhs = rhs_exp; op }) span
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for int binop (expected int, int)"
              (format_tau a)
              (format_tau b)))
  | A.Unop { op; operand } ->
    let operand_type, op_exp = syn_exp ctx operand in
    (match op with
     | Negative | Bitwise_not ->
       (match operand_type with
        | Int -> operand_type, Mark.mark (A.Unop { op; operand = op_exp }) span
        | b ->
          error
            ~msg:
              (sprintf "Incompatible type (%s) for - or ~ (expected int)" (format_tau b)))
     | Not ->
       (match operand_type with
        | Bool -> operand_type, Mark.mark (A.Unop { op; operand = op_exp }) span
        | i ->
          error
            ~msg:(sprintf "incompatible type (%s) for ! (expected bool)" (format_tau i))))
  | A.Comparison { op; lhs; rhs } ->
    let lhs_type, lhs_exp = syn_exp ctx lhs in
    let rhs_type, rhs_exp = syn_exp ctx rhs in
    (match op with
     | Less | Less_equal | Greater | Greater_equal ->
       (match lhs_type, rhs_type with
        | Int, Int ->
          Bool, Mark.mark (A.Comparison { op; lhs = lhs_exp; rhs = rhs_exp }) span
        | a, b ->
          error
            ~msg:
              (sprintf
                 "Incompatible types (%s, %s) for comparison  (expected int, int)"
                 (format_tau a)
                 (format_tau b)))
       (* Equality and Disequality must have small type *)
     | Equal | Not_equal ->
       let binop_tau = compare_tau ~ctx lhs_type rhs_type in
       assert_small_type binop_tau;
       Bool, Mark.mark (A.Comparison { op; lhs = lhs_exp; rhs = rhs_exp }) span)
  | A.And { lhs; rhs } ->
    let lhs_type, lhs_exp = syn_exp ctx lhs in
    let rhs_type, rhs_exp = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Bool, Bool -> lhs_type, Mark.mark (A.And { lhs = lhs_exp; rhs = rhs_exp }) span
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for comparison  (expected bool, bool)"
              (format_tau a)
              (format_tau b)))
  | Or { lhs; rhs } ->
    let lhs_type, lhs_exp = syn_exp ctx lhs in
    let rhs_type, rhs_exp = syn_exp ctx rhs in
    (match lhs_type, rhs_type with
     | Bool, Bool -> lhs_type, Mark.mark (A.Or { lhs = lhs_exp; rhs = rhs_exp }) span
     | a, b ->
       error
         ~msg:
           (sprintf
              "Incompatible types (%s, %s) for comparison  (expected bool, bool)"
              (format_tau a)
              (format_tau b)))
  (* Conditional Expressions must have small type *)
  | A.Ternary { condition; lhs; rhs; _ } ->
    let cond_type, cond_exp = syn_exp ctx condition in
    let lhs_type, lhs_exp = syn_exp ctx lhs in
    let rhs_type, rhs_exp = syn_exp ctx rhs in
    (match cond_type with
     | A.Bool ->
       let ternary_tau = compare_tau ~ctx lhs_type rhs_type in
       assert_small_type ternary_tau;
       ( ternary_tau
       , Mark.mark
           (A.Ternary
              { condition = cond_exp
              ; lhs = lhs_exp
              ; rhs = rhs_exp
              ; result_type = ternary_tau
              })
           span )
     | _ -> error ~msg:"Incompatible types (condition of a ternary operator is not bool)")
  | A.Function_call { ident; args; _ } ->
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
    let validated_args = match_args_params ~ctx ~arg_types ~declared_param_list:params in
    let (_ : unit) = SymbolTable.find_or_add ctx.used ident ~default:(fun () -> ()) in
    ( fn_tau
    , Mark.mark
        (A.Function_call { ident; args = validated_args; return_type = fn_tau })
        span )
  | A.Alloc tau ->
    let validated_tau = extract_tau ~ctx ~req_struct_defined:true tau in
    let validated_tau' = extract_tau ~ctx ~req_struct_defined:true validated_tau in
    A.Pointer validated_tau, Mark.mark (A.Alloc validated_tau') span
  | A.Deref { address; _ } ->
    let pointer_type, validated_address = syn_exp ctx address in
    (* address_tau must not be any, its type must be de-refed too *)
    let derefed_tau =
      match pointer_type with
      | A.Pointer p -> p
      | _ -> error ~msg:(sprintf "Dereferencing a type %s" (A.Print.pp_tau pointer_type))
    in
    ( derefed_tau
    , Mark.mark (A.Deref { address = validated_address; pointer_type = derefed_tau }) span
    )
  | A.Null_pointer -> A.Any, mexp
  | A.Alloc_array { array_type; size } ->
    let arr_type = extract_tau ~ctx ~req_struct_defined:true array_type in
    let arr_type' = extract_tau ~ctx ~req_struct_defined:true arr_type in
    let size_type, size_exp = syn_exp ctx size in
    (match size_type with
     | Int ->
       ( Array arr_type'
       , Mark.mark (A.Alloc_array { array_type = arr_type'; size = size_exp }) span )
     | _ ->
       error
         ~msg:
           (sprintf
              "Only ints allowed for array alloc and not %s"
              (A.Print.pp_tau size_type)))
  | A.Array_access { array; index; _ } ->
    let arr_type, arr_exp = syn_exp ctx array in
    let ind_type, ind_exp = syn_exp ctx index in
    let (_ : unit) =
      match ind_type with
      | Int -> ()
      | _ -> error ~msg:(sprintf "%s used for arr access" (A.Print.pp_tau ind_type))
    in
    let arr_inner_type =
      match arr_type with
      | Array t -> t
      | _ -> error ~msg:(sprintf "%s used as array" (A.Print.pp_tau arr_type))
    in
    ( arr_inner_type
    , Mark.mark
        (A.Array_access { array = arr_exp; index = ind_exp; array_type = arr_inner_type })
        span )
  | Struct_access_parse { s; field; _ } ->
    (* fuck me man this shit need to store in the context *)
    (* circle back to this later *)
    (* Some bullshit man fuck *)
    let s_type, s_exp = syn_exp ctx s in
    let struct_name =
      match s_type with
      | A.Struct s_name -> s_name
      | _ -> error ~msg:(sprintf "%s not a valid struct" (A.Print.pp_tau s_type))
    in
    let field_tau = extract_field_tau ~ctx struct_name field in
    ( field_tau
    , Mark.mark (A.Struct_access_parse { s = s_exp; field; field_type = field_tau }) span
    )
  | Paren _ -> failwith "no more parens"
  | Struct_access _ -> failwith "no struct access yet"

and extract_exp_type ctx ~args = List.map args ~f:(fun arg -> syn_exp ctx arg)

(** Returns [env] if the statement typechecks. 
    [tau] is the return type of the function that mstm is contained in, 
    and only checked during returns. *)
let rec chk_stm (ctx : env) (mstm : A.mstm) (tau : A.tau) : env * A.mstm =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span mstm) ~msg;
    raise Error_msg.Error
  in
  let stm = Mark.data mstm in
  let span = get_start_end mstm in
  match stm with
  | Declare (decl, tau', s) ->
    (* Need to ensure that the tau is valid in omega
       and Local variables must have small type *)
    let validated_tau = extract_tau ~ctx tau' in
    assert_small_type validated_tau;
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
          let new_env, new_s =
            chk_stm
              { ctx with
                gamma = SymbolMap.set ctx.gamma ~key:id ~data:validated_tau
              ; delta = SymbolSet.remove ctx.delta id
              }
              s
              tau
          in
          new_env, Mark.mark (A.Declare (decl, validated_tau, new_s)) span)
     (* If s returns, it sets this returns to be true. *)
     | A.Init (id, assign_exp) ->
       assert (
         match SymbolTable.find ctx.omega id with
         | None -> true
         | Some _ -> failwith (sprintf "declaration %s is a typedef" (Symbol.name id)));
       let assign_tau, validated_exp = syn_exp ctx assign_exp in
       let (_ : A.tau) = compare_tau ~ctx validated_tau assign_tau in
       (match SymbolMap.find ctx.gamma id with
        | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name id))
        | None ->
          let stm_env, new_s =
            chk_stm
              { ctx with
                gamma = SymbolMap.set ctx.gamma ~key:id ~data:validated_tau
              ; delta = SymbolSet.add ctx.delta id
              }
              s
              tau
          in
          (* let new_env = { stm_env with delta = SymbolSet.remove ctx.delta id } in *)
          let new_init = A.Init (id, validated_exp) in
          stm_env, Mark.mark (A.Declare (new_init, validated_tau, new_s)) span)
       (* Validate the expression, match the find, then do the update and everything *))
  | Assign (x, e) ->
    (* Assignments must have small type *)
    let lhs_type, validated_lhs = syn_exp ctx ~initializing:true x in
    let lhs_data = Mark.data validated_lhs in
    assert (validate_lvalue lhs_data);
    let x_symbol = extract_lvalue_symbol lhs_data in
    let search = SymbolMap.find ctx.gamma x_symbol in
    let (_ : A.tau) =
      match search with
      | None ->
        error
          ~msg:(sprintf "Not declared before initialization: `%s`" (Symbol.name x_symbol))
      | Some t -> t
    in
    let exp_type, validated_exp = syn_exp ctx e in
    (* Printf.printf "\n%s | %s\n" (A.Print.pp_tau exp_type) (A.Print.pp_tau lhs_type); *)
    let compared_tau = compare_tau ~ctx lhs_type exp_type in
    assert_small_type compared_tau;
    ( { ctx with
        gamma = ctx.gamma
      ; delta = SymbolSet.add ctx.delta x_symbol
      ; returns = false
      }
    , Mark.mark (A.Assign (validated_lhs, validated_exp)) span )
  | Return e ->
    let exp_type, validated_exp = syn_exp ctx e in
    let validated_tau = extract_tau ~ctx tau in
    let (_ : A.tau) = compare_tau ~ctx validated_tau exp_type in
    ( { ctx with
        gamma = ctx.gamma
      ; delta = SymbolSet.of_list (SymbolMap.keys ctx.gamma)
      ; returns = true
      }
    , Mark.mark (A.Return validated_exp) span )
  | If (e, s1, s2) ->
    let exp_type, validated_exp = syn_exp ctx e in
    (match exp_type with
     | Bool ->
       let ctx', validated_s1 = chk_stm ctx s1 tau in
       let ctx'', validated_s2 = chk_stm ctx s2 tau in
       ( { ctx with
           delta = SymbolSet.inter ctx'.delta ctx''.delta
         ; returns = ctx'.returns && ctx''.returns
         }
       , Mark.mark (A.If (validated_exp, validated_s1, validated_s2)) span )
       (* If returns if both s1 and s2 return *)
     | _ -> error ~msg:"Expression in if statement was expected to have type bool")
  | While (e, s) ->
    let exp_type, validated_exp = syn_exp ctx e in
    (match exp_type with
     | A.Bool ->
       let _, validated_stm = chk_stm ctx s tau in
       ( { ctx with returns = false }
       , Mark.mark (A.While (validated_exp, validated_stm)) span )
       (* While will never return *)
     | _ -> error ~msg:"Expression in if statement was expected to have type bool")
  | Nop -> { ctx with returns = false }, Mark.mark A.Nop span (* Nop will never return *)
  | Seq (s1, s2) ->
    let ctx', validated_s1 = chk_stm ctx s1 tau in
    let ctx'', validated_s2 = chk_stm { ctx with delta = ctx'.delta } s2 tau in
    ( { ctx with delta = ctx''.delta; returns = ctx'.returns || ctx''.returns }
    , Mark.mark (A.Seq (validated_s1, validated_s2)) span )
    (* Seq returns if either s1 or s2 return*)
  | For _ -> failwith "for loops should have been elaborated away before typechecking"
  | Expr_stm e ->
    let exp_type, validated_exp = syn_exp ctx e in
    assert_small_type exp_type;
    (* Just check the expression and keep the original context *)
    ctx, Mark.mark (A.Expr_stm validated_exp) span
  | Block_intermediate _ ->
    failwith "Block intermediates should have been elaborated away before typechecking"
  | Declare_intermediate _ ->
    failwith "Declare intermediates should have been elaborated away before typechecking"
  | Assert e ->
    let exp_type, validated_exp = syn_exp ctx e in
    assert (
      match exp_type with
      | A.Bool -> true
      | _ -> false);
    ctx, Mark.mark (A.Assert validated_exp) span
  | Return_void ->
    (match tau with
     (* Return_void doesn't return *)
     | A.Void ->
       ( { ctx with
           gamma = ctx.gamma
         ; delta = SymbolSet.of_list (SymbolMap.keys ctx.gamma)
         ; returns = false
         }
       , Mark.mark A.Return_void span )
     | _ -> error ~msg:(sprintf "fails, function of type tau returns %s" (format_tau tau)))
  | Asnop_pure_mem { lhs; op; rhs } ->
    let lhs_type, validated_lhs = syn_exp ctx lhs in
    let lhs_data = Mark.data validated_lhs in
    assert (validate_lvalue lhs_data);
    let lhs_symbol = extract_lvalue_symbol lhs_data in
    let search = SymbolMap.find ctx.gamma lhs_symbol in
    (match search with
     | None ->
       error ~msg:(sprintf "Var %s has no associated type" (Symbol.name lhs_symbol))
     | Some _ -> ());
    let (_ : unit) =
      match SymbolSet.find ctx.delta ~f:(match_symbol lhs_symbol) with
      | None ->
        error ~msg:(sprintf "Var %s not initialized before use" (Symbol.name lhs_symbol))
      | Some _ -> ()
    in
    let rhs_type, validated_rhs = syn_exp ctx rhs in
    let (_ : A.tau) = compare_tau ~ctx lhs_type rhs_type in
    ( { ctx with
        gamma = ctx.gamma
      ; delta = SymbolSet.add ctx.delta lhs_symbol
      ; returns = false
      }
    , Mark.mark (A.Asnop_pure_mem { lhs = validated_lhs; op; rhs = validated_rhs }) span )
  | Asnop_impure_mem { lhs; op; rhs } ->
    let lhs_type, validated_lhs = syn_exp ctx lhs in
    let lhs_data = Mark.data validated_lhs in
    assert (validate_lvalue lhs_data);
    let lhs_symbol = extract_lvalue_symbol lhs_data in
    let search = SymbolMap.find ctx.gamma lhs_symbol in
    (match search with
     | None ->
       error ~msg:(sprintf "Var %s has no associated type" (Symbol.name lhs_symbol))
     | Some _ -> ());
    let (_ : unit) =
      match SymbolSet.find ctx.delta ~f:(match_symbol lhs_symbol) with
      | None ->
        error ~msg:(sprintf "Var %s not initialized before use" (Symbol.name lhs_symbol))
      | Some _ -> ()
    in
    let rhs_type, validated_rhs = syn_exp ctx rhs in
    let (_ : A.tau) = compare_tau ~ctx lhs_type rhs_type in
    ( { ctx with
        gamma = ctx.gamma
      ; delta = SymbolSet.add ctx.delta lhs_symbol
      ; returns = false
      }
    , Mark.mark (A.Asnop_impure_mem { lhs = validated_lhs; op; rhs = validated_rhs }) span
    )
  | Asnop_pure_mem_intermediate _ | Asnop_impure_mem_intermediate _ ->
    failwith "asnop intermediates to be elaborated out"
  | Postop _ -> failwith "postops to be elaborated out"
;;

(* Check that there are no duplicate parameter names *)
let unique_fn_params ~(params : A.param list) : unit SymbolTable.t =
  let param_table = SymbolTable.create ~growth_allowed:true ~size:10 () in
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

let validate_struct_fields ~ctx ~(fields : (Symbol.t * A.tau) List.t)
  : A.tau SymbolTable.t * (Symbol.t * A.tau) List.t
  =
  (* For each value, extract the tau. Unique fields enforced during elaboration *)
  let mapped_fields =
    List.map fields ~f:(fun (field, tau) ->
      let extracted_tau = extract_tau ~ctx ~req_struct_defined:true tau in
      (* Printf.printf
      "\ntau: %s, extracted_tau: %s\n"
      (A.Print.pp_tau tau)
      (A.Print.pp_tau extracted_tau); *)
      field, extracted_tau)
  in
  match SymbolTable.of_alist mapped_fields with
  | `Ok x -> x, mapped_fields
  | `Duplicate_key _ -> failwith "duplicate key found"
;;

(* Make sure that the types are all in omega and return them *)
(* Function parameters must have a small type *)
let valid_type_fn_params (ctx : env) ~(params : A.param list) : A.param list =
  List.map params ~f:(fun (x_tau, x) ->
    let ret_tau = extract_tau ~ctx x_tau in
    assert_small_type ret_tau;
    ret_tau, x)
;;

(* Get return type of the function *)
(* Return type must have small type *)
let valid_fn_type (ctx : env) ~(ret_type : A.tau) : A.tau =
  extract_tau ~ctx ~function_call:true ret_type
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
let match_declared_fn_params ~ctx ~param_list_updated ~declared_param_list =
  let map2_res =
    List.map2 param_list_updated declared_param_list ~f:(fun (tau_x1, _) (tau_x2, _) ->
      let param_tau = compare_tau ~ctx tau_x1 tau_x2 in
      assert_small_type param_tau;
      param_tau)
  in
  match map2_res with
  | Ok a -> a
  | Unequal_lengths -> failwith "parameters have different lengths"
;;

(* Ensure that the actual return types of functions match with their declarations *)
let match_ret_types ~ctx ~tau_ret_type ~declared_ret_type =
  let ret_tau = compare_tau ~ctx ~is_ret_type:true tau_ret_type declared_ret_type in
  assert_small_type ret_tau;
  ret_tau
;;

let add_args_to_table ~ctx ~params =
  let added_gamma =
    List.fold_left params ~init:ctx.gamma ~f:(fun gamma (param_tau, ident) ->
      let extracted_tau = extract_tau ~ctx param_tau in
      SymbolMap.set gamma ~key:ident ~data:extracted_tau)
  in
  let added_delta =
    List.fold_left params ~init:ctx.delta ~f:(fun delta (_, ident) ->
      SymbolSet.add delta ident)
  in
  { ctx with gamma = added_gamma; delta = added_delta }
;;

(* Typecheck a function definition, which comprise the function bodies. *)
let typecheck_fndef ctx ~ret_type ~param_list ~fn_block : env * A.mstm =
  (* All the args have to be added into the context like a declaration *)
  let curr_ctx =
    { gamma = SymbolMap.empty
    ; delta = SymbolSet.empty
    ; omega = ctx.omega
    ; sigma = ctx.sigma
    ; epsilon = ctx.epsilon
    ; used = ctx.used
    ; returns = false
    }
  in
  let curr_ctx' = add_args_to_table ~ctx:curr_ctx ~params:param_list in
  let new_ctx, new_fn_block = chk_stm curr_ctx' fn_block ret_type in
  let validated_tau = extract_tau ~ctx:new_ctx ~function_call:true ret_type in
  match new_ctx.returns, validated_tau with
  | true, A.Int
  | true, A.Bool
  | true, A.Pointer _
  | true, A.Array _
  | true, A.Any
  | false, A.Void -> new_ctx, new_fn_block
  | _ ->
    failwith
      (sprintf
         "ret_type %s does not align with function return %s"
         (format_tau validated_tau)
         (string_of_bool new_ctx.returns))
;;

let rec check_program (ctx : env) (program : A.program_block) : env * A.program_block =
  match program with
  | Function_Def { ret_type; ident; params; fn_block } ->
    check_fndef ctx ~ret_type ~ident ~params ~fn_block
  | Function_Decl { ret_type; ident; params } -> check_fndecl ctx ~ret_type ~ident ~params
  | Typedef { original; alias } -> check_typedef ctx ~original ~alias, program
  | Struct_Decl { ident } -> check_structdecl ctx ~ident, program
  | Struct_Def { ident; fields } -> check_structdef ctx ~ident ~fields
  | Function_Def_Intermediate _ ->
    failwith "fn_defn_intermediate not allowed after elaboration"
  | Struct_Def_Intermediate _ ->
    failwith "struct_def_intermediate not allowed after elaboration"

and check_header (ctx : env) (program : A.program_block) : env * A.program_block =
  match program with
  | Function_Def _ -> failwith "function defs not allowed in headers"
  | Function_Decl { ret_type; ident; params } ->
    assert (validate_ident ~function_name:ident);
    check_fndecl ctx ~ret_type ~ident ~params
  | Typedef { original; alias } -> check_typedef ctx ~original ~alias, program
  | Struct_Decl { ident } -> check_structdecl ctx ~ident, program
  | Struct_Def { ident; fields } -> check_structdef ctx ~ident ~fields
  | Function_Def_Intermediate _ -> failwith "fn_defn_intermediate not allowed in headers"
  | Struct_Def_Intermediate _ -> failwith "fn_defn_intermediate not allowed in headers"

(* Typecheck a function definition *)
and check_typedef (ctx : env) ~(original : A.tau) ~(alias : Symbol.t) : env =
  (* Use extract_tau to validate the original tau *)
  let original_type = extract_tau ~ctx original in
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
      match_declared_fn_params ~ctx ~param_list_updated ~declared_param_list
    in
    let tau_ret_type = valid_fn_type ctx ~ret_type in
    let (_ : A.tau) = match_ret_types ~ctx ~tau_ret_type ~declared_ret_type in
    ctx, A.Function_Decl { ret_type = tau_ret_type; ident; params = param_list_updated }
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
    ctx, A.Function_Decl { ret_type = tau_ret_type; ident; params = param_list_updated }

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
    let ret_ctx, updated_fn_block = typecheck_fndef ctx ~ret_type ~param_list ~fn_block in
    let (_ : unit) =
      SymbolTable.update ret_ctx.epsilon ident ~f:(fun some_key ->
        match some_key with
        | None -> failwith "need to have the function declared"
        | Some (params, curr_tau, returns) ->
          assert (not returns);
          params, curr_tau, true)
    in
    let tau_ret_type = valid_fn_type ctx ~ret_type in
    ( ret_ctx
    , A.Function_Def
        { ret_type = tau_ret_type
        ; ident
        ; params = param_list
        ; fn_block = updated_fn_block
        } )
  | None -> failwith "a declaration should have been made before a definition"

and check_structdecl ctx ~(ident : Symbol.t) : env =
  (* Structs idents can exist in delta/epsilon/omega/sigma *)
  match SymbolTable.add ctx.sigma ~key:ident ~data:(SymbolTable.create (), false) with
  | `Ok -> ctx
  | `Duplicate -> ctx (* Ok if it already exists for struct decl *)

and check_structdef ctx ~(ident : Symbol.t) ~(fields : (Symbol.t * A.tau) List.t)
  : env * A.program_block
  =
  (* Only allowed to be defined once no matter what *)
  match SymbolTable.find ctx.sigma ident with
  | None ->
    let field_table, val_fields = validate_struct_fields ~ctx ~fields in
    (match SymbolTable.add ctx.sigma ~key:ident ~data:(field_table, true) with
     | `Ok -> ctx, A.Struct_Def { ident; fields = val_fields }
     | `Duplicate -> failwith "wtf?")
  | Some (_, defined) ->
    assert (not defined);
    let field_table, val_fields = validate_struct_fields ~ctx ~fields in
    SymbolTable.set ctx.sigma ~key:ident ~data:(field_table, true);
    ctx, A.Struct_Def { ident; fields = val_fields }
;;

let validate_used ~used ~epsilon =
  SymbolTable.iter_keys used ~f:(fun key ->
    match SymbolTable.find epsilon key with
    | Some (_, _, defines) -> assert defines
    | None -> failwith "function somehow used but not declared")
;;

let typecheck (program : A.program) (header_ctx : env) : A.program * env =
  let omega = header_ctx.omega in
  let epsilon = header_ctx.epsilon in
  let sigma = header_ctx.sigma in
  let used = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let ctx =
    { gamma = SymbolMap.empty
    ; delta = SymbolSet.empty
    ; omega
    ; sigma
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
  let rec helper helper_ctx progs acc =
    match progs with
    | [] -> helper_ctx, acc
    | h :: t ->
      let span = get_start_end h in
      let checked_ctx, checked_prog = check_program helper_ctx (Mark.data h) in
      let marked_prog = Mark.mark checked_prog span in
      helper checked_ctx t (marked_prog :: acc)
  in
  let final_ctx, acc = helper ctx program [] in
  validate_used ~used:final_ctx.used ~epsilon:final_ctx.epsilon;
  List.rev acc, final_ctx
;;

let header_typecheck (program : A.program) =
  let omega = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let epsilon = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let used = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let sigma = SymbolTable.create ~growth_allowed:true ~size:500 () in
  let ctx =
    { gamma = SymbolMap.empty
    ; delta = SymbolSet.empty
    ; omega
    ; sigma
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
  let rec helper helper_ctx progs acc =
    match progs with
    | [] -> helper_ctx, acc
    | h :: t ->
      let span = get_start_end h in
      let checked_ctx, checked_prog = check_header helper_ctx (Mark.data h) in
      let marked_prog = Mark.mark checked_prog span in
      helper checked_ctx t (marked_prog :: acc)
  in
  let res_ctx, acc = helper ctx program [] in
  let (_ : unit) =
    SymbolTable.map_inplace res_ctx.epsilon ~f:(fun (params, tau, _) -> params, tau, true)
  in
  List.rev acc, res_ctx
;;
