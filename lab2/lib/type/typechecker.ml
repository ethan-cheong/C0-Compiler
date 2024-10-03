(* L1 Compiler
 * TypeChecker
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core
module A = Ast
module S = Symbol.Map
module SymbolSet = Set.Make (Symbol)

type env =
  { gamma : A.tau S.t
  ; delta : SymbolSet.t
  ; returns : bool
  }

let tc_errors : Error_msg.t = Error_msg.create ()

let format_tau = function
  | A.Bool -> "bool"
  | A.Int -> "int"
;;

(* For debugging purposes*)
(* 
let print_env e : unit =
  print_string "Gamma:\n";
  S.iteri
    ~f:(fun ~key:k ~data:v -> Printf.printf "%s -> %s\n" (format_tau v) (Symbol.name k))
    e.gamma;
  print_string "Delta:\n";
  SymbolSet.iter
    ~f:(fun i -> Printf.printf "%s was initialized\n" (Symbol.name i))
    e.delta;
  Printf.printf "Returns is %s\n" (string_of_bool e.returns)
;; *)

let match_symbol sym target_sym : bool = Symbol.compare sym target_sym = 0

let rec syn_exp (ctx : env) (mexp : A.mexp) : A.tau =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span mexp) ~msg;
    raise Error_msg.Error
  in
  match Mark.data mexp with
  | A.Var curr_sym ->
    let search = S.find ctx.gamma curr_sym in
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
  | A.Function _ -> failwith "function typechecking not needed for l2"
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
     | Int ->
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
;;

(** Returns [env] if ... *)
let rec chk_stm (ctx : env) (mstm : A.mstm) (tau : A.tau) : env =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span mstm) ~msg;
    raise Error_msg.Error
  in
  let stm = Mark.data mstm in
  match stm with
  | Declare (decl, tau', s) ->
    (* Declare is the only stm that modifies Gamma. *)
    (match decl with
     | A.New_var id ->
       (match S.find ctx.gamma id with
        | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name id))
        | None ->
          chk_stm
            { ctx with
              gamma = S.set ctx.gamma ~key:id ~data:tau'
            ; delta = SymbolSet.remove ctx.delta id
            }
            s
            tau)
       (* If s returns, it sets this returns to be true. *)
     | _ ->
       failwith "Assignment together with declations should have been elaborated away.")
  | Assign (x, e) ->
    let search = S.find ctx.gamma x in
    let var_type =
      match search with
      | None ->
        error ~msg:(sprintf "Not declared before initialization: `%s`" (Symbol.name x))
      | Some t -> t
    in
    let exp_type = syn_exp ctx e in
    (match var_type, exp_type with
     | Int, Int | Bool, Bool ->
       { gamma = ctx.gamma; delta = SymbolSet.add ctx.delta x; returns = false }
       (* Assign will never return*)
     | a, b ->
       error
         ~msg:
           (sprintf
              "Expression of type %s was assigned to variable of type %s"
              (format_tau b)
              (format_tau a)))
  | Return e ->
    let exp_type = syn_exp ctx e in
    (match tau, exp_type with
     (* Return always returns *)
     | Bool, Bool | Int, Int ->
       { gamma = ctx.gamma; delta = SymbolSet.of_list (S.keys ctx.gamma); returns = true }
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
     | Int ->
       error
         ~msg:"Expression in if statement was expected to have type bool but had type int")
  | While (e, s) ->
    (match syn_exp ctx e with
     | Bool ->
       let (_ : env) = chk_stm ctx s tau in
       { ctx with returns = false }
       (* While will never return *)
     | Int ->
       error
         ~msg:"Expression in if statement was expected to have type bool but had type int")
  | Nop -> { ctx with returns = false } (* Nop will never return *)
  | Seq (s1, s2) ->
    (* print_string "Context in first block of seq:\n"; *)
    let ctx' = chk_stm ctx s1 tau in
    (* print_env ctx';
    print_string "Context in second block of seq:\n"; *)
    let ctx'' = chk_stm { ctx with delta = ctx'.delta } s2 tau in
    (* print_env ctx''; *)
    { ctx with delta = ctx''.delta; returns = ctx'.returns || ctx''.returns }
    (* There might be a problem here with the current test cases *)
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
;;

let typecheck ast =
  let ctx =
    chk_stm { gamma = S.empty; delta = SymbolSet.empty; returns = false } ast A.Int
  in
  if not ctx.returns
  then (
    Error_msg.error tc_errors None ~msg:"main does not return";
    raise Error_msg.Error)
;;
