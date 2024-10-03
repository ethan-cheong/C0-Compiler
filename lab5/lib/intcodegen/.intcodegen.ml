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

let munch_label (label : T.label) : string = fst label ^ "_" ^ string_of_int (snd label)
let munch_label_cmd (label : T.label) : ThreeAS.instr = ThreeAS.Label (munch_label label)

(* munch_exp_acc dest exp rev_acc
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
let rec munch_exp_acc
  (dest : ThreeAS.operand)
  (exp : T.exp)
  (rev_acc : ThreeAS.instr list)
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
    let op = munch_binop_pure op in
    let t1 = ThreeAS.Temp (Temp.create ()) in
    let t2 = ThreeAS.Temp (Temp.create ()) in
    let rev_acc' = rev_acc |> munch_exp_acc t1 lhs |> munch_exp_acc t2 rhs in
    ThreeAS.Binop { op; dest; lhs = t1; rhs = t2 } :: rev_acc'
  | T.Binop_cmp _ ->
    (* This should never happen, since boolean expressions are elaborated to if statements and jumps. *)
    failwith
      "For now, assume this fails - we never try to munch on an if. Boolean expressions \
       are elaborated to if statements and jumps"

(* munch_exp dest exp
 *
 * Generates instructions for dest <-- exp.
 *)
and munch_exp (dest : ThreeAS.operand) (exp : T.exp) : ThreeAS.instr list =
  List.rev (munch_exp_acc dest exp [])

(* munch_cmd : T.cmd -> AS.instr list *)
(* munch_cmd cmd generates code to execute cmd *)
and munch_cmd = function
  | T.Move mv -> munch_exp (ThreeAS.Temp mv.dest) mv.src
  | T.Return e ->
    (* return e becomes t <- e, ret t *)
    let t = ThreeAS.Temp (Temp.create ()) in
    (* Runs the munching on the expression to be returned *)
    let rev_acc = [] |> munch_exp_acc t e in
    List.rev (ThreeAS.Ret { src = t } :: rev_acc)
    (* return becomes ret 0xFFFFFFFF. We can do this since the result of void functions will not be assigned anywhere *)
  | T.Return_void -> [ ThreeAS.Ret { src = ThreeAS.MAX_INT } ]
  | T.Binop_impure { lhs; op; rhs; dest } ->
    let op = munch_binop_impure op in
    let t1 = ThreeAS.Temp (Temp.create ()) in
    let t2 = ThreeAS.Temp (Temp.create ()) in
    let rev_acc = [] |> munch_exp_acc t1 lhs |> munch_exp_acc t2 rhs in
    List.rev (ThreeAS.Binop { op; dest = Temp dest; lhs = t1; rhs = t2 } :: rev_acc)
  | T.If { condition; lt; lf } ->
    (match condition with
     | Const i ->
       (match i with
        | MAX_INT ->
          failwith "MAX_INT should not be in the condition of a boolean statement"
        | Int i ->
          if Int32.equal i Int32.one
          then [ ThreeAS.Jump (munch_label lt) ]
          else if Int32.equal i Int32.zero
          then [ ThreeAS.Jump (munch_label lf) ]
          else
            failwith
              (Printf.sprintf
                 "How interesting... somehow %d ended up in the condition of a boolean \
                  statement"
                 (Int32.to_int_exn i)))
     | Binop_cmp { lhs; op; rhs } ->
       let op = munch_binop_cmp op in
       let t1 = ThreeAS.Temp (Temp.create ()) in
       let t2 = ThreeAS.Temp (Temp.create ()) in
       let rev_acc = [] |> munch_exp_acc t1 lhs |> munch_exp_acc t2 rhs in
       List.rev
         (ThreeAS.Jump (munch_label lf)
          :: ThreeAS.JumpC { cmp = op; label = munch_label lt }
          :: Cmp { lhs = t2; rhs = t1 }
             (* Remember that assembly compares are the opposite of when we write them on paper*)
          :: rev_acc)
     | _ -> failwith "Condition of an if statement should always evaluate to a bool")
  | T.Goto l -> [ ThreeAS.Jump (munch_label l) ]
  | T.Label l -> [ munch_label_cmd l ]
  (* d <- f(e1,...,en) becomes:
      t1 <- e1, 
      ..., 
      tn <- en, 
      Callf(t1,...,tn) 
     *)
  | T.Function_call { dest; ident; args; assign_res } ->
    let munched_exps, temp_list =
      List.fold_map args ~init:[] ~f:(fun acc exp ->
        let ti = ThreeAS.Temp (Temp.create ()) in
        munch_exp_acc ti exp acc, ti)
    in
    List.rev
      (ThreeAS.CallF { dest = ThreeAS.Temp dest; ident; args = temp_list; assign_res }
       :: munched_exps)
;;

(** On each function (represented by a T.func), concat the results of codegen-ing
    each statement. *)
let munch_func (func : T.func) arg_to_temp : ThreeAS.func =
  let signature, body = func in
  match signature with
  | { ident; args; tail_rec } ->
    let munched_body = List.concat_map body ~f:munch_cmd in
    (* Create a new temp for each function argument *)
    let prologue =
      List.fold args ~init:[] ~f:(fun acc arg ->
        let ti = ThreeAS.Temp (Temp.create ()) in
        (* keep track of all temps created *)
        Hashtbl.add_exn arg_to_temp ~key:arg ~data:ti;
        ThreeAS.Mov { src = Temp arg; dest = ti } :: acc)
    in
    (* Matches temp with corresponding argument if it comes from an argument *)
    let search_temp_table (op : ThreeAS.operand) =
      match op with
      | Temp t ->
        (match Hashtbl.find arg_to_temp t with
         | Some x -> x
         | None -> op)
      | _ -> op
    in
    let replace_temps_helper (instr : ThreeAS.instr) : ThreeAS.instr =
      match instr with
      | Binop { op; dest; lhs; rhs } ->
        Binop
          { op
          ; dest = search_temp_table dest
          ; lhs = search_temp_table lhs
          ; rhs = search_temp_table rhs
          }
      | Mov { dest; src } ->
        Mov { dest = search_temp_table dest; src = search_temp_table src }
      | Cmp { lhs; rhs } ->
        Cmp { lhs = search_temp_table lhs; rhs = search_temp_table rhs }
      | Ret { src } -> Ret { src = search_temp_table src }
      | CallF { ident; dest; args; assign_res } ->
        CallF
          { ident
          ; dest = search_temp_table dest
          ; args = List.map args ~f:search_temp_table
          ; assign_res
          }
      | _ -> instr
    in
    let replaced_temps_body = List.map ~f:replace_temps_helper munched_body in
    (* TODO: try to remove the @ by using replaced_temps_body as the acc for prologue.
       We can't remove this for now, since we have to do the prologue before we 
       do the body... *)
    ThreeAS.{ ident; args; tail_rec }, prologue @ replaced_temps_body
;;

(** Codegen each function in sequence. 
    Requires: Temp.counter must already be in scope before the function is called, 
    by calling Temp.create () in the caller.

    TODO: initialize a global hash table that is cleared OR use map in each
     *)
let int_code_gen program =
  (* Global Hashtbl so we don't have to keep making new ones*)
  let arg_to_temp = Hashtbl.create ~growth_allowed:true ~size:10 (module Temp) in
  (* Mov all arguments into temps*)
  List.map program ~f:(fun func ->
    let result = munch_func func arg_to_temp in
    Hashtbl.clear arg_to_temp;
    result)
;;

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
