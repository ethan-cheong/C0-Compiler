(* L1 Compiler
 * Elaborated AST -> IR Translator
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 * Translates elaborated Abstract Syntax Tree into IR.
 *)
open Core
module A = Ast
module S = Symbol
module T = Tree

let trans_binop_pure = function
  | A.Plus -> T.Add
  | A.Minus -> T.Sub
  | A.Times -> T.Mul
  | A.Bitwise_or -> T.Or
  | A.Bitwise_xor -> T.Xor
  | A.Bitwise_and -> T.And
;;

let trans_binop_cmp = function
  | A.Less -> T.Lt
  | A.Less_equal -> T.Leq
  | A.Greater -> T.Gt
  | A.Greater_equal -> T.Geq
  | A.Equal -> T.Eq
  | A.Not_equal -> T.Neq
;;

let trans_binop_impure = function
  | A.Divided_by -> T.Div
  | A.Modulo -> T.Mod
  | A.Left_shift -> T.Sal
  | A.Right_shift -> T.Sar
;;

let trans_unop = function
  (* unary to binary!*)
  | A.Negative -> T.Sub
  | A.Bitwise_not -> T.Xor (* To take bitwise not, Xor with all 1 mask*)
  | A.Not -> failwith "We handle this manually this in stage"
;;

let func_name_of_ident ~ident ~defined_functions =
  if String.equal (S.name ident) "main"
  then "_c0_main"
  else if Hashtbl.mem defined_functions ident
  then "_f_" ^ S.name ident
  else S.name ident
;;

(** Takes [elaborated_ast] and returns an IR as a T.func.
    Requires: [elaborated_ast] has been fully elaborated:
      1. There are no more asops e.g. +=, -= 
      2. For expressions have been elaborated into while expressions
      3. int x = 0 (declare with init expressions) have been elaborated into 
        a sequence of declare + assign expressions
      4. There are no more Declare_intermediate statements 
        of the form decl * tau * mstm list; these have been elaborated into 
        sequences
      5. Expr_stms are included in case they cause a runtime exception
      6. There are no Blocks; these have been elaborated into chains of sequences
        Block \[a; b; c] -> seq(a, seq(b, seq(c, nop)))
    Requires: [elaborated_ast] has passed typechecking
    Requires: Temp.counter is already in scope when this function is called, so 
    that changes to temp numbers are persistent across compiler phases
 *)
let translate_ast (ast : A.mprogram_block) defined_functions env : T.func =
  (*
    Maintain a global Hashtbl env which maps variables (Symbol.t) to Temps.
    We can do this because:
    - Type checking ensures that variables are used only after they are declared
    - According to l2 semantics, variables CANNOT shadow other variables. 
    - So if we traverse our tree using DFS, "replacing" variables in the global 
      Hashtbl is ok, since if we set a variable with the same name, 
      it means the previous variable is out of scope.  
  *)
  let init_num_temps = Temp.get_counter () in
  let raw_ast = Mark.data ast in
  (* let elaborated_ast =
    match raw_ast with
    | Function_Decl _ -> failwith "function declarations should have been elaborated away"
    | Typedef _ -> failwith "typedefs should have been elaborated away"
    | Function_Def_Intermediate _ ->
      failwith "Intermediate function definitions should have been elaborated away"
    | Function_Def { fn_block; _ } -> fn_block
  in *)
  match raw_ast with
  | Function_Decl _ | Typedef _ | Function_Def_Intermediate _ ->
    failwith "No body to translated"
  | Function_Def { fn_block; params; ident; _ } ->
    let elaborated_ast = fn_block in
    (* Add all params to the environment so they can be referenced*)
    List.iter params ~f:(fun (_, param) ->
      let t = Temp.create () in
      Hashtbl.set env ~key:param ~data:t);
    (* Commands are appended to a doubly-linked list. *)
    let result_dll = Doubly_linked.create () in
    let append_to_dll list =
      Doubly_linked.transfer ~src:(Doubly_linked.of_list list) ~dst:result_dll
    in
    let function_args =
      List.map params ~f:(fun (_, param) -> Tree.Temp (Hashtbl.find_exn env param))
    in
    let caller_ident = ident in
    let func_name = func_name_of_ident ~ident ~defined_functions in
    (* if there are any function calls NOT in the tail recursive position, then 
       the function is not tail recursive. *)
    let tail_rec_position = ref true in
    (* Don't spill to the stack if the function isn't even recursive. *)
    let recursive = ref false in
    (* If there is a function call in this position, it can't be tail recursive.*)
    let check_tail_rec_mexp (mexp : Ast.mexp) =
      match Mark.data mexp with
      | Function_call _ -> tail_rec_position := false
      | _ -> ()
    in
    let label_counter = ref 0 in
    let next_label () =
      incr label_counter;
      !label_counter
    in
    (* In the lecture notes, translation of expressions returns a (ins, res) tuple
      such that ins is a list of stms with side effects, and res is a pure expression
      with the result of the computation.
      Here, we only return res, and immediately append ins to the global DLL. 
      tail_recursive is a special flag we use only to mark tail-recursive functions. *)
    let rec trans_exp ?(call_as_stm = false) exp =
      match exp with
      (* To translate variables, get the corresponding temp. *)
      | A.Var id -> T.Temp (Hashtbl.find_exn env id)
      (* For now, all variables have size double*)
      (* Ints and bools are converted to T.Int's *)
      | A.Const (c, _) -> T.Const (T.Int c)
      (* tr(e1 + e2) = ([ins(e1); ins(e2)], e1+e2) *)
      | A.Binop_pure { lhs; op; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        let lhs_res = trans_mexp lhs in
        (* because we force the evaluation of the left subtree here, this does DFS *)
        let rhs_res = trans_mexp rhs in
        T.Binop_pure { lhs = lhs_res; op = trans_binop_pure op; rhs = rhs_res }
      | A.Unop { op = A.Negative; operand = e } ->
        check_tail_rec_mexp e;
        let res = trans_mexp e in
        T.Binop_pure
          { op = trans_unop A.Negative; lhs = T.Const (T.Int Int32.zero); rhs = res }
      | A.Unop { op = A.Bitwise_not; operand = e } ->
        check_tail_rec_mexp e;
        let res = trans_mexp e in
        T.Binop_pure
          { op = trans_binop_pure A.Bitwise_xor; lhs = T.Const MAX_INT; rhs = res }
      (* Expression e that happens to be boolean:
         tr (e) = (
          [cp(e,l1, l2) ;
          l1: ;
          t <- 1; 
          goto l3; 
          l2: ;
          t <- 0;
          goto l3;
          l3: ],
          t
         )
      *)
      | A.Unop { operand; _ } ->
        check_tail_rec_mexp operand;
        let label_id = next_label () in
        let true_label = "bool_exp_true" ^ func_name, label_id in
        let false_label = "bool_exp_false" ^ func_name, label_id in
        let end_label = "bool_exp_end" ^ func_name, label_id in
        let t = Temp.create () in
        trans_boolean_exp exp true_label false_label;
        append_to_dll
          [ T.Label true_label
          ; T.Move { dest = t; src = Const (Int Int32.one) }
          ; T.Goto end_label
          ; T.Label false_label
          ; T.Move { dest = t; src = Const (Int Int32.zero) }
          ; T.Goto end_label
          ; T.Label end_label
          ];
        T.Temp t
        (* Expression e that happens to be boolean:
         tr (e) = (
          [cp(e,l1, l2) ;
          l1: ;
          t <- 1; 
          goto l3; 
          l2: ;
          t <- 0;
          goto l3;
          l3: ],
          t
         )
      *)
      | A.Comparison { lhs; rhs; _ } | A.And { lhs; rhs } | A.Or { lhs; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        let label_id = next_label () in
        let true_label = "bool_exp_true" ^ func_name, label_id in
        let false_label = "bool_exp_false" ^ func_name, label_id in
        let end_label = "bool_exp_end" ^ func_name, label_id in
        let t = Temp.create () in
        trans_boolean_exp exp true_label false_label;
        append_to_dll
          [ T.Label true_label
          ; T.Move { dest = t; src = Const (Int Int32.one) }
          ; T.Goto end_label
          ; T.Label false_label
          ; T.Move { dest = t; src = Const (Int Int32.zero) }
          ; T.Goto end_label
          ; T.Label end_label
          ];
        T.Temp t
      (* tr(e1 @ e2) = ([ins(e1); ins(e2); t<- res(e1) @ res(e2)], t) *)
      | A.Binop_impure { op; lhs; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        let t = Temp.create () in
        (* Same effect as adding ins(e1) to the output *)
        let lhs_res = trans_mexp lhs in
        let rhs_res = trans_mexp rhs in
        append_to_dll
          [ T.Binop_impure
              { lhs = lhs_res; op = trans_binop_impure op; rhs = rhs_res; dest = t }
          ];
        T.Temp t
      (* Binops resolve to quad for now *)
      (* tr(c ? e1 : e2) -> 
         ([
          cp(c, l1, l2);
          l1: ;
          ins(e1);
          t <- res(e1);
          goto l3;
          l2: ;
          ins(e2);
          t <- res(e2);
          l3:
         ]
         ,t
         )
      *)
      | Ternary { condition; lhs; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        let label_id = next_label () in
        let ternary_true_label = "ternary_true" ^ func_name, label_id in
        let ternary_false_label = "ternary_false" ^ func_name, label_id in
        let ternary_end_label = "ternary_end" ^ func_name, label_id in
        let t = Temp.create () in
        trans_boolean_exp (Mark.data condition) ternary_true_label ternary_false_label;
        append_to_dll [ T.Label ternary_true_label ];
        let lhs_res = trans_mexp lhs in
        append_to_dll
          [ T.Move { dest = t; src = lhs_res }
          ; T.Goto ternary_end_label
          ; T.Label ternary_false_label
          ];
        let rhs_res = trans_mexp rhs in
        append_to_dll [ T.Move { dest = t; src = rhs_res }; T.Label ternary_end_label ];
        T.Temp t
        (* tr(f(e1,...,en)) = ([ins(e1);...;ins(en);t<-f(res(e1), ..., res(en))], t) *)
      | Function_call { ident; args } ->
        if S.(ident = caller_ident) then recursive := true;
        let t = Temp.create () in
        let res_args =
          List.map args ~f:(fun arg ->
            check_tail_rec_mexp arg;
            trans_mexp arg)
        in
        (* translate each element of the list in order *)
        let callee_name =
          if String.equal (S.name ident) "main"
          then "_c0_main"
          else if Hashtbl.mem defined_functions ident
          then "_f_" ^ S.name ident
          else S.name ident
        in
        (* If you call as statement, you don't assign result *)
        append_to_dll
          [ T.Function_call
              { dest = t
              ; ident = callee_name
              ; args = res_args
              ; assign_res = not call_as_stm
              }
          ];
        T.Temp t
    (* Wrapper for mexps *)
    and trans_mexp ?(call_as_stm = false) mexp = trans_exp ~call_as_stm (Mark.data mexp)
    (* Helper function used for translating boolean expressions. Refer to 
        Intermediate Representation lecture notes section 6. 
        Appends to DLL a sequence of commands that jumps to [if_true] if 
        [boolean_exp]; otherwise, it jumps to [if_false]. *)
    and trans_boolean_exp (boolean_exp : A.exp) (if_true : T.label) (if_false : T.label) =
      match boolean_exp with
      | Var _ | Function_call _ ->
        (* cp(e, l, l') and cp(f(...), l, l')*)
        let res = trans_exp boolean_exp in
        append_to_dll
          [ T.If
              { condition =
                  Binop_cmp { lhs = res; op = Neq; rhs = Const (Int Int32.zero) }
              ; lt = if_true
              ; lf = if_false
              }
          ]
      | Comparison { op; lhs; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        (* cp(e1?e2, l, l') *)
        let res_lhs = trans_mexp lhs in
        let res_rhs = trans_mexp rhs in
        append_to_dll
          [ T.If
              { condition =
                  Binop_cmp { lhs = res_lhs; op = trans_binop_cmp op; rhs = res_rhs }
              ; lt = if_true
              ; lf = if_false
              }
          ]
      | Unop { op = Not; operand } ->
        check_tail_rec_mexp operand;
        (* cp(!e, l, l') *)
        trans_boolean_exp (Mark.data operand) if_false if_true
      | And { lhs; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        (* cp(e1 && e2, l, l') *)
        let label_id = next_label () in
        let lhs_true_label = "and_lhs_true" ^ func_name, label_id in
        trans_boolean_exp (Mark.data lhs) lhs_true_label if_false;
        append_to_dll [ T.Label lhs_true_label ];
        trans_boolean_exp (Mark.data rhs) if_true if_false
      | Or { lhs; rhs } ->
        check_tail_rec_mexp lhs;
        check_tail_rec_mexp rhs;
        (* cp(e1 || e1, l, l') *)
        let label_id = next_label () in
        let lhs_false_label = "or_lhs_false" ^ func_name, label_id in
        trans_boolean_exp (Mark.data lhs) if_true lhs_false_label;
        append_to_dll [ T.Label lhs_false_label ];
        trans_boolean_exp (Mark.data rhs) if_true if_false
      | Const (c, A.Bool) ->
        Int32.(
          if c = zero
          then append_to_dll [ T.Goto if_false ]
          else if c = one
          then append_to_dll [ T.Goto if_true ])
      | Const (_, A.Int) ->
        failwith
          "Int was used in a boolean expression. This should've been caught in type \
           checking"
      (* Ternary expressions can be boolean expressions as well. 
         Compute the result of the ternary, then do a conditional jump to if_true
          or if_false depending on the result.*)
      | Ternary _ ->
        let ternary_res = trans_exp boolean_exp in
        append_to_dll
          [ T.If
              { condition =
                  Binop_cmp
                    { lhs = ternary_res; op = T.Eq; rhs = T.Const (T.Int Int32.one) }
              ; lt = if_true
              ; lf = if_false
              }
          ]
      | _ -> failwith "A non-boolean was used in a boolean expression"
    (* Translates a statement. Env is a reference to a global symbol Hashtbl.
    The symbol table maps Symbol.t to Temp.t. Appends the result to the global 
    dll. *)
    and trans_stm (stm : A.stm) : unit =
      match stm with
      | A.Declare (d, _, sub_stm) ->
        (match d with
         | A.New_var id ->
           let t = Temp.create () in
           Hashtbl.set env ~key:id ~data:t;
           trans_mstm sub_stm
         | A.Init _ -> failwith "Declare with init should have been elaborated out")
      | A.Assign (id, e) ->
        check_tail_rec_mexp e;
        let res = trans_mexp e in
        let t = Hashtbl.find_exn env id in
        (* An error here means we assigned a value before initializing it *)
        Hashtbl.set env ~key:id ~data:t;
        append_to_dll [ T.Move { dest = t; src = res } ]
      | A.Return e ->
        (* Here we have to check if a function is called that it has the same 
           ident. *)
        (match Mark.data e with
         | A.Function_call { ident; _ } ->
           if S.(ident <> caller_ident) then tail_rec_position := false
         | _ -> ());
        let res = trans_mexp e in
        append_to_dll [ T.Return res ]
      | A.Return_void -> append_to_dll [ T.Return_void ]
      (*
          tr(assert(e)) : cp (e, l1, l2); 
            l2 : t = function_call abort
            l1: 
        *)
      | A.Assert e ->
        (* Since functions with assert must call abort(), 
             it can never be tail recursive. *)
        tail_rec_position := false;
        let label_id = next_label () in
        let fail_label = "assert_fail" ^ func_name, label_id in
        let pass_label = "assert_pass" ^ func_name, label_id in
        let t = Temp.create () in
        trans_boolean_exp (Mark.data e) pass_label fail_label;
        append_to_dll
          [ T.Label fail_label
          ; T.Function_call { dest = t; ident = "abort"; args = []; assign_res = false }
          ; T.Label pass_label
          ]
      | A.Nop -> ()
      | A.Seq (s1, s2) ->
        trans_mstm s1;
        trans_mstm s2
      (* Translation of while using cp:
         tr(while(b, s)) = goto cmp;
                          l1: tr(s);
                          cmp: cp(b, l1, l2);
                          l2:  
        *)
      | A.While (condition, body) ->
        check_tail_rec_mexp condition;
        let label_id = next_label () in
        let while_true_label = "while_true" ^ func_name, label_id in
        let while_cmp_label = "while_cmp" ^ func_name, label_id in
        let while_end_label = "while_end" ^ func_name, label_id in
        append_to_dll [ T.Goto while_cmp_label; T.Label while_true_label ];
        trans_mstm body;
        append_to_dll [ T.Label while_cmp_label ];
        trans_boolean_exp (Mark.data condition) while_true_label while_end_label;
        append_to_dll [ T.Label while_end_label ]
      | A.If (condition, if_true, if_false) ->
        check_tail_rec_mexp condition;
        let label_id = next_label () in
        let if_true_label = "if_true" ^ func_name, label_id in
        let if_false_label = "if_false" ^ func_name, label_id in
        let if_end_label = "if_end" ^ func_name, label_id in
        trans_boolean_exp (Mark.data condition) if_true_label if_false_label;
        append_to_dll [ T.Label if_true_label ];
        trans_mstm if_true;
        append_to_dll [ T.Goto if_end_label; T.Label if_false_label ];
        trans_mstm if_false;
        append_to_dll [ T.Goto if_end_label; T.Label if_end_label ]
      | A.Expr_stm e ->
        (* 
            Expression statement is not appended, but the expressions are appended.
            Throw away the result and keep only the side effects *)
        check_tail_rec_mexp e;
        ignore (trans_mexp ~call_as_stm:true e : T.exp)
      | A.For _ -> failwith "There should not be any for loops in elaborated AST"
      | A.Block_intermediate _ -> failwith "Blocks should have been elaborated away"
      | A.Declare_intermediate _ ->
        failwith "Decl intermediates should be elaborated away"
      | A.Assign_exp _ -> failwith "Assign expressions should be elaborated away"
    and trans_mstm mstm : unit = trans_stm (Mark.data mstm) in
    trans_mstm elaborated_ast;
    let body = Doubly_linked.to_list result_dll in
    let tail_rec = !tail_rec_position && !recursive in
    Hashtbl.clear env;
    let num_temps = Temp.get_counter () - init_num_temps in
    (* Empty the env for the next function decl translation *)
    let signature = T.{ ident = func_name; args = function_args; tail_rec; num_temps } in
    (match body with
     (* If the body is empty (void function) then add a return statement *)
     | [] -> signature, [ T.Return_void ]
     | _ -> signature, body)
;;

let get_defined_functions program_list =
  let defined_names = Hashtbl.create ~growth_allowed:true ~size:10 (module Symbol) in
  List.iter program_list ~f:(fun e ->
    match Mark.data e with
    | Ast.Function_Def { ident; _ } -> Hashtbl.add_exn defined_names ~key:ident ~data:()
    | _ -> ());
  defined_names
;;

let keep_only_function_defs program_list =
  List.filter program_list ~f:(fun e ->
    match Mark.data e with
    | Ast.Function_Def _ -> true
    | _ -> false)
;;

let translate (ast_list : Ast.program) : T.program =
  let defined_functions = get_defined_functions ast_list in
  (* Keep only function definitions in subsequent program *)
  let ast_list_only_defs = keep_only_function_defs ast_list in
  let env = Hashtbl.create ~growth_allowed:true ~size:10 (module Symbol) in
  List.map ast_list_only_defs ~f:(fun ast -> translate_ast ast defined_functions env)
;;

(************************TESTING**********************)
(* 
 let%expect_test "Test illustrating importance of intcodegen / max munch" =
   let lexbuf =
     Lexing.from_string
       "int main()\n\
       \      {\n\
       \        int a;\n\
       \        int b;\n\
       \        int c;\n\
       \        int d;\n\
       \        int e;\n\
       \        int f;\n\
       \        int g;\n\
       \        int h;\n\
       \      \n\
       \        a = 9 / 4; b = 9 % 4;\t\t// 2 1\n\
       \        c = -9 / 4; d = -9 % 4;\t// -2 -1\n\
       \        e = 9 / -4; f = 9 % -4;\t// -2 1\n\
       \        g = -9 / -4; h = -9 % -4;\t// 2 -1\n\
       \        return -h+10*(g+10*(f+10*(-e+10*(-d+10*(-c+10*(b+10*a))))));\n\
       \      }\n\
       \      "
   in
   let program = C0_parser.program C0_lexer.initial lexbuf in
   let ast = Elaborate.elaborate program in
   Printf.printf
     "----------AST------------\n%s\n------------IR--------------\n"
     (A.Print.pp_mstm ast);
   let ir = fst (translate ast) in
   let output_tree line = Printf.printf "\t%s\n" (T.Print.pp_cmd line) in
   List.iter ~f:output_tree ir;
   [%expect {|
     Something ... something should print
   |}]
 ;;
 
 let%expect_test "Test illustrating importance of basic blocks" =
   let lexbuf =
     Lexing.from_string
       "int main ()\n\
       \      {\n\
       \        int n;\n\
       \        int m;\n\
       \        int b;\n\
       \        bool d0;\n\
       \      \n\
       \        n = 254;\n\
       \        m = 1;\n\
       \        for (b = 0 ; n > 0 ; n /= 2) {\n\
       \          if ((n % 2) == 0)\n\
       \            d0 = false;\n\
       \          else\n\
       \            d0 = true;\n\
       \          if (m < 0) return 1/0;\t/* raise exception on overflow */\n\
       \          if (!d0) { m *= 10; }\n\
       \          else { b = m + b;  m *= 10; }\n\
       \        }\n\
       \        return b;\n\
       \      }\n\
       \      "
   in
   let program = C0_parser.program C0_lexer.initial lexbuf in
   let ast = Elaborate.elaborate program in
   Printf.printf
     "----------AST------------\n%s\n------------IR--------------\n"
     (A.Print.pp_mstm ast);
   let ir = fst (translate ast) in
   let output_tree line = Printf.printf "\t%s\n" (T.Print.pp_cmd line) in
   List.iter ~f:output_tree ir;
   [%expect {|
     Something ... something should print
   |}]
 ;;
 
 let%expect_test "Test to see separation of statements with side effects and pure binops" =
   Temp.reset ();
   let lexbuf =
     Lexing.from_string
       "int main(){\n\
       \        int a = 33;\n\
       \        int b = 0x00D;\n\
       \        int c = a + b; // 45\n\
       \        int d = c / a; // 1\n\
       \        int e = c + (d - b); // 56\n\
       \        return (a+(c/(d*(e%(6-(c%2))))))\n\
       \        \n\
       \    }"
   in
   let program = C0_parser.program C0_lexer.initial lexbuf in
   let ast = Elaborate.elaborate program in
   Printf.printf
     "----------AST------------\n%s\n------------IR--------------\n"
     (A.Print.pp_mstm ast);
   let ir = fst (translate ast) in
   let output_tree line = Printf.printf "\t%s\n" (T.Print.pp_cmd line) in
   List.iter ~f:output_tree ir;
   [%expect {|
     Something ... something should print
   |}]
 ;;
 
 let%expect_test "Test what conditionals do in tree" =
   Temp.reset ();
   let lexbuf =
     Lexing.from_string
       "int main() {\n\
       \        bool x = true;\n\
       \        bool y = false;\n\
       \        bool z = true;\n\
       \  int x = 5;\n\
       \  int y = 6;\n\
       \  int z;\n\
       \  z = 7;\n\n\
       \        if ((x&&y)||z) {\n\
       \          if (((x*y) / z) > ((z - x)* y)) {\n\
       \            return 1;\n\
       \          }\n\
       \        }\n\
       \        return 0;\n\
       \      } "
   in
   let program = C0_parser.program C0_lexer.initial lexbuf in
   let ast = Elaborate.elaborate program in
   Printf.printf
     "----------AST------------\n%s\n------------IR--------------\n"
     (A.Print.pp_mstm ast);
   let ir = fst (translate ast) in
   let output_tree line = Printf.printf "\t%s\n" (T.Print.pp_cmd line) in
   List.iter ~f:output_tree ir;
   [%expect {|
     Something ... something should print
   |}]
 ;; *)

(* 
 (*
 Test case based on return21.l2
 //test return 5050
 
 int main ()
 {
   int n;
   int sum;
   int i;
 
   n = 100;
   sum = 0;
   i = 0;
   while (i <= n) {
     sum = sum + i;
     i = i + 1;
   }
   return sum;
 }
 *)
 let%expect_test "Test case based on return21.l2" =
   let n = S.symbol "n" in
   let sum = S.symbol "sum" in
   let i = S.symbol "i" in
   let mstm (stm : A.stm) = Mark.naked stm in
   let mexp (exp : A.exp) = Mark.naked exp in
   let ast =
     A.(
       mstm
         (Declare
            ( New_var n
            , Int
            , mstm
                (Declare
                   ( New_var sum
                   , Int
                   , mstm
                       (Declare
                          ( New_var i
                          , Int
                          , mstm
                              (Seq
                                 ( mstm
                                     (Assign (n, mexp (Const (Int (Int32.of_int_exn 100)))))
                                 , mstm
                                     (Seq
                                        ( mstm
                                            (Assign
                                               ( sum
                                               , mexp (Const (Int (Int32.of_int_exn 0))) ))
                                        , mstm
                                            (Seq
                                               ( mstm
                                                   (Assign
                                                      ( i
                                                      , mexp
                                                          (Const (Int (Int32.of_int_exn 1)))
                                                      ))
                                               , mstm
                                                   (Seq
                                                      ( mstm
                                                          (While
                                                             ( mexp
                                                                 (Comparison
                                                                    { op = Less_equal
                                                                    ; lhs = mexp (Var i)
                                                                    ; rhs = mexp (Var n)
                                                                    })
                                                             , mstm
                                                                 (Seq
                                                                    ( mstm
                                                                        (Assign
                                                                           ( sum
                                                                           , mexp
                                                                               (Binop_pure
                                                                                  { op =
                                                                                      Plus
                                                                                  ; lhs =
                                                                                      mexp
                                                                                        (Var
                                                                                           sum)
                                                                                  ; rhs =
                                                                                      mexp
                                                                                        (Var
                                                                                           i)
                                                                                  }) ))
                                                                    , mstm
                                                                        (Seq
                                                                           ( mstm
                                                                               (Assign
                                                                                  ( i
                                                                                  , mexp
                                                                                      (Binop_pure
                                                                                         { op =
                                                                                           Plus
                                                                                         ; lhs =
                                                                                           mexp
                                                                                           (
                                                                                           Var
                                                                                           i)
                                                                                         ; rhs =
                                                                                           mexp
                                                                                           (
                                                                                           Const
                                                                                           (
                                                                                           Int
                                                                                           (
                                                                                           Int32
                                                                                           .of_int_exn
                                                                                           1)))
                                                                                         })
                                                                                  ))
                                                                           , mstm Nop )) ))
                                                             ))
                                                      , mstm
                                                          (Seq
                                                             ( mstm
                                                                 (Return (mexp (Var sum)))
                                                             , mstm Nop )) )) )) )) )) ))
                   )) )))
   in
   let ir = translate ast in
   let output_line line = Printf.printf "\t%s\n" (T.Print.pp_cmd line) in
   List.iter ~f:output_line ir;
   [%expect {|
     Some ..something should print
   |}]
 ;; *)
