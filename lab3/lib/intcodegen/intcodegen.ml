(* L1 Compiler
 * Assembly Code Generator for Three Address assembly
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Implements a "convenient munch" algorithm
 * Always create a temp whenever a subexpression has to be evaluated. The result is stored in the temp
 * New temps are assigned during arithmetic operations (binop pure, impure, cmp)
 *)

open Core
module T = Tree
module ThreeAS = Threeaddrassem

(* Helper functions for Tree to ThreeAS conversion *)
let munch_binop_pure : T.binop_pure -> ThreeAS.operation = function
  | T.Add -> ThreeAS.Add
  | T.Sub -> ThreeAS.Sub
  | T.Mul -> ThreeAS.Mul
  | T.Or -> ThreeAS.Or
  | T.Xor -> ThreeAS.Xor
  | T.And -> ThreeAS.And
;;

let munch_binop_cmp = function
  | T.Lt -> ThreeAS.Lt
  | T.Leq -> ThreeAS.Leq
  | T.Gt -> ThreeAS.Gt
  | T.Geq -> ThreeAS.Geq
  | T.Eq -> ThreeAS.Eq
  | T.Neq -> ThreeAS.Neq
;;

let munch_binop_impure : T.binop_impure -> ThreeAS.operation = function
  | T.Div -> ThreeAS.Div
  | T.Mod -> ThreeAS.Mod
  | T.Sal -> ThreeAS.Sal
  | T.Sar -> ThreeAS.Sar
;;

let munch_const_or_temp : T.exp -> ThreeAS.operand = function
  | Const c ->
    (match c with
     | Int i -> Imm i
     | MAX_INT -> MAX_INT)
  | Temp t -> Temp t
  | _ -> failwith "munch_const_or_temp called on a non-const/temp"
;;

let munch_label (label : T.label) : string = fst label ^ "_" ^ string_of_int (snd label)
let munch_label_cmd (label : T.label) : ThreeAS.instr = ThreeAS.Label (munch_label label)

(* munch_exp dest exp rev_acc
     *
     * Suppose we have the statement:
     *   dest <-- exp
     *
     * If the codegened statements for this are:
     *   s1; s2; s3; s4;
     *
     * Then this function returns the result:
     *   s4 :: s3 :: s2 :: s1 :: rev_acc
     *
     * I.e., rev_acc is an accumulator argument where the codegen'ed
     * statements are built in reverse. This allows us to create the
     * statements in linear time rather than quadratic time (for highly
     * nested expressions).
     *)
let rec munch_exp (dest : ThreeAS.operand) (exp : T.exp) (rev_acc : ThreeAS.instr list)
  : ThreeAS.instr list
  =
  match exp with
  | T.Const n ->
    (match n with
     | Int i -> ThreeAS.Mov { dest; src = ThreeAS.Imm i } :: rev_acc
     | MAX_INT -> ThreeAS.Mov { dest; src = ThreeAS.MAX_INT } :: rev_acc)
  | T.Temp t ->
    (* Any temps that are already there will stay the same *)
    ThreeAS.Mov { dest; src = Temp t } :: rev_acc
  | T.Binop_pure { lhs; op; rhs } ->
    (* TODO: find a better way to do this casing *)
    let op = munch_binop_pure op in
    (match lhs, rhs with
     | Const _, Const _ | Temp _, Const _ | Const _, Temp _ | Temp _, Temp _ ->
       ThreeAS.Binop
         { op; dest; lhs = munch_const_or_temp lhs; rhs = munch_const_or_temp rhs }
       :: rev_acc
     | Const _, _ | Temp _, _ ->
       let rhs_temp = ThreeAS.Temp (Temp.create ()) in
       let rev_acc' = rev_acc |> munch_exp rhs_temp rhs in
       ThreeAS.Binop { op; dest; lhs = munch_const_or_temp lhs; rhs = rhs_temp }
       :: rev_acc'
     | _, Const _ | _, Temp _ ->
       let lhs_temp = ThreeAS.Temp (Temp.create ()) in
       let rev_acc' = rev_acc |> munch_exp lhs_temp lhs in
       ThreeAS.Binop { op; dest; lhs = lhs_temp; rhs = munch_const_or_temp rhs }
       :: rev_acc'
     | _ ->
       let lhs_temp = ThreeAS.Temp (Temp.create ()) in
       let rhs_temp = ThreeAS.Temp (Temp.create ()) in
       let rev_acc' = rev_acc |> munch_exp lhs_temp lhs |> munch_exp rhs_temp rhs in
       ThreeAS.Binop { op; dest; lhs = lhs_temp; rhs = rhs_temp } :: rev_acc')
  | T.Binop_cmp _ ->
    (* This should never happen, since boolean expressions are elaborated to if statements and jumps. *)
    failwith
      "For now, assume this fails - we never try to munch on an if. Boolean expressions \
       are elaborated to if statements and jumps"

(* munch_cmd : T.cmd list -> AS.instr list *)
(* munch_cmd cmd generates code to execute cmd. *)
and munch_cmd cmd_list rev_acc : ThreeAS.instr list =
  (* To reduce the number of temps we create, we do not assign temps if the
     nested expressions are temps or consts. *)
  match cmd_list with
  | [] -> List.rev rev_acc
  | T.Move mv :: tl ->
    let munched_exps = munch_exp (ThreeAS.Temp mv.dest) mv.src rev_acc in
    munch_cmd tl munched_exps
  | T.Return e :: tl ->
    (* return e becomes t <- e, ret t *)
    (* if the expression is already a temp or a const, don't make a new one! *)
    let munched_exps =
      match e with
      | Temp _ | Const _ -> ThreeAS.Ret { src = munch_const_or_temp e } :: rev_acc
      | _ ->
        let t = ThreeAS.Temp (Temp.create ()) in
        ThreeAS.Ret { src = t } :: munch_exp t e rev_acc
    in
    (* Munch the remaining commands *)
    munch_cmd tl munched_exps
    (* return becomes ret 0xFFFFFFFF. We can do this since the result of void functions will not be assigned anywhere *)
  | T.Return_void :: tl -> munch_cmd tl (ThreeAS.Ret { src = ThreeAS.MAX_INT } :: rev_acc)
  | T.Binop_impure { lhs; op; rhs; dest } :: tl ->
    (* Similar logic to pure binops; however, idiv cannot have an immediate as 
       a register, so we need to make a temp for the rhs if it is a const
      (refer to instrsel). *)
    let op = munch_binop_impure op in
    let dest = ThreeAS.Temp dest in
    let munched_exps =
      match lhs, rhs with
      | Const _, Temp _ | Temp _, Temp _ ->
        ThreeAS.Binop
          { op; dest; lhs = munch_const_or_temp lhs; rhs = munch_const_or_temp rhs }
        :: rev_acc
      | Const _, _ | Temp _, _ ->
        let rhs_temp = ThreeAS.Temp (Temp.create ()) in
        let rev_acc' = rev_acc |> munch_exp rhs_temp rhs in
        ThreeAS.Binop { op; dest; lhs = munch_const_or_temp lhs; rhs = rhs_temp }
        :: rev_acc'
      | _, Temp _ ->
        let lhs_temp = ThreeAS.Temp (Temp.create ()) in
        let rev_acc' = rev_acc |> munch_exp lhs_temp lhs in
        ThreeAS.Binop { op; dest; lhs = lhs_temp; rhs = munch_const_or_temp rhs }
        :: rev_acc'
      | _ ->
        let lhs_temp = ThreeAS.Temp (Temp.create ()) in
        let rhs_temp = ThreeAS.Temp (Temp.create ()) in
        let rev_acc' = rev_acc |> munch_exp lhs_temp lhs |> munch_exp rhs_temp rhs in
        ThreeAS.Binop { op; dest; lhs = lhs_temp; rhs = rhs_temp } :: rev_acc'
    in
    munch_cmd tl munched_exps
  (* For if statements, we treat it differently depending on if the condition 
      is true or false. If the condition is known to be true at compile-time then
       we can immediately substitute it in. *)
  | T.If { condition; lt; lf } :: tl ->
    (match condition with
     | Const i ->
       (match i with
        | MAX_INT ->
          failwith "MAX_INT should not be in the condition of a boolean statement"
        | Int i ->
          if Int32.equal i Int32.one
          then ThreeAS.Jump (munch_label lt) :: munch_cmd tl rev_acc
          else if Int32.equal i Int32.zero
          then ThreeAS.Jump (munch_label lf) :: munch_cmd tl rev_acc
          else
            failwith
              (Printf.sprintf
                 "How interesting... somehow %d ended up in the condition of a boolean \
                  statement"
                 (Int32.to_int_exn i)))
     | Binop_cmp { lhs; op; rhs } ->
       let op = munch_binop_cmp op in
       (* Similar to binops; if lhs / rhs are consts/temps, we don't have to 
         munch them. However, in final assembly, the immediates must be on the 
         left; so if we have lhs: Const, rhs: _ in Tree, we still have to munch
         it. *)
       let munched_exps =
         match lhs, rhs with
         | Temp _, Const _ | Temp _, Temp _ ->
           [ ThreeAS.Jump (munch_label lf)
           ; ThreeAS.JumpC { cmp = op; label = munch_label lt }
             (* Remember that assembly compares are the opposite of when we write them on paper*)
           ; Cmp { lhs = munch_const_or_temp rhs; rhs = munch_const_or_temp lhs }
           ]
           @ rev_acc
         | Temp _, _ ->
           let rhs_temp = ThreeAS.Temp (Temp.create ()) in
           let rev_acc' = rev_acc |> munch_exp rhs_temp rhs in
           [ ThreeAS.Jump (munch_label lf)
           ; ThreeAS.JumpC { cmp = op; label = munch_label lt }
           ; Cmp { lhs = rhs_temp; rhs = munch_const_or_temp lhs }
           ]
           @ rev_acc'
         | _, Const _ | _, Temp _ ->
           let lhs_temp = ThreeAS.Temp (Temp.create ()) in
           let rev_acc' = rev_acc |> munch_exp lhs_temp lhs in
           [ ThreeAS.Jump (munch_label lf)
           ; ThreeAS.JumpC { cmp = op; label = munch_label lt }
           ; Cmp { lhs = munch_const_or_temp rhs; rhs = lhs_temp }
           ]
           @ rev_acc'
         | _ ->
           let lhs_temp = ThreeAS.Temp (Temp.create ()) in
           let rhs_temp = ThreeAS.Temp (Temp.create ()) in
           let rev_acc' = rev_acc |> munch_exp lhs_temp lhs |> munch_exp rhs_temp rhs in
           [ ThreeAS.Jump (munch_label lf)
           ; ThreeAS.JumpC { cmp = op; label = munch_label lt }
           ; Cmp { lhs = rhs_temp; rhs = lhs_temp }
           ]
           @ rev_acc'
       in
       munch_cmd tl munched_exps
     | _ -> failwith "Condition of an if statement should always evaluate to a bool")
  | T.Goto l :: tl -> munch_cmd tl (ThreeAS.Jump (munch_label l) :: rev_acc)
  | T.Label l :: tl -> munch_cmd tl (munch_label_cmd l :: rev_acc)
  (* d <- f(e1,...,en) becomes:
        t1 <- e1, 
        ..., 
        tn <- en, 
        Callf(t1,...,tn) 
       *)
  | T.Function_call { dest; ident; args; assign_res } :: tl ->
    let munched_exps, temp_list =
      List.fold_map args ~init:rev_acc ~f:(fun acc exp ->
        let ti = ThreeAS.Temp (Temp.create ()) in
        munch_exp ti exp acc, ti)
    in
    munch_cmd
      tl
      (ThreeAS.CallF { dest = ThreeAS.Temp dest; ident; args = temp_list; assign_res }
       :: munched_exps)
;;

(** [munch_func func] produces Three-Address Assembly code for [func]. *)
let munch_func (func : T.func) : ThreeAS.func =
  let signature, body = func in
  match signature with
  | { ident; args; tail_rec; num_temps } ->
    let init_temp_count = Temp.get_counter () in
    let munched_body = munch_cmd body [] in
    let end_temp_count = Temp.get_counter () in
    (* Matches temp with corresponding argument if it comes from an argument *)
    let new_args =
      List.map args ~f:(fun arg ->
        match arg with
        | Temp t -> ThreeAS.Temp t
        | _ -> failwith "Tree args should not contain non-temps")
    in
    ( ThreeAS.
        { ident
        ; args = new_args
        ; tail_rec
        ; num_temps = num_temps + (end_temp_count - init_temp_count)
        }
    , munched_body )
;;

(** Codegen each function in sequence. 
    Requires: Temp.counter must already be in scope before the function is called, 
    by calling Temp.create () in the caller.
       *)
let int_code_gen program = List.map program ~f:munch_func

(*********** TESTING ***********)

(* let%expect_test "Test what conditionals do in tree" =
    Temp.reset ();
    let lexbuf =
      Lexing.from_string
        "\n\
        \  int main() {\n\
        \    bool x = ((5< (10+6)) || (54 <= (6*(20+(99)))));\n\
        \  }\n\
        \      "
    in
    let program = C0_parser.program C0_lexer.initial lexbuf in
    let ast = Elaborate.elaborate program in
    let ir = Trans.translate ast in
    let assem = int_code_gen ir in
    Printf.printf
      "----------AST------------\n\
       %s\n\
       ------------IR--------------\n\
       %s\n\
       ------------Assem-----------\n"
      (Ast.Print.pp_mstm ast)
      (T.Print.pp_program ir);
    let output_assem line = Printf.printf "\t%s\n" (AS.format line) in
    List.iter ~f:output_assem assem;
    [%expect {|
      Something ... something should print
    |}]
  ;; *)
