(* L1 Compiler
 * Elaborate on the initial AST
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
 * Gluing together the pieces produced by ocamllex and ocamlyacc
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
let rec expand_ast_list (lst : Ast.program) =
  match lst with
  | [] -> mark_with_pos Ast.Nop Lexing.dummy_pos Lexing.dummy_pos
  | h :: t ->
    (* Need to now consider what happens if h is declare. *)
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
  (* If have declare intermediate, need to process it... *)
  | Ast.Declare_intermediate (decl, tau) ->
    mark_with_span (process_decl decl tau []) stm_src
  | Ast.Assign (_, _) -> h
  | Ast.Return _ -> h
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

(* Elaborates on a declaration statement. Splits up a declare that initialises a value
  into a declaration of a new variable and an assignment *)
and process_decl decl tau tail =
  match decl with
  | Ast.New_var _ -> Ast.Declare (decl, tau, expand_ast_list tail)
  | Ast.Init (sym, mexp) ->
    let assign_expr =
      mark_with_pos (Ast.Assign (sym, mexp)) Lexing.dummy_pos Lexing.dummy_pos
    in
    Ast.Declare (Ast.New_var sym, tau, expand_ast_list (assign_expr :: tail))

(* De-sugars for loop into a block that declares a scope and has a while-loop, followed by a step statement if any *)
and expand_for s1 s2 e s3 =
  let dummy_marked_s2 = validate s2 in
  let dummy_marked_seq =
    mark_with_pos
      (Ast.Seq (process s3, dummy_marked_s2))
      Lexing.dummy_pos
      Lexing.dummy_pos
  in
  let dummy_marked_while =
    mark_with_pos (Ast.While (e, dummy_marked_seq)) Lexing.dummy_pos Lexing.dummy_pos
  in
  match Mark.data s1 with
  | Ast.Declare_intermediate (decl, tau) -> process_decl decl tau [ dummy_marked_while ]
  | _ -> Ast.Seq (process s1, dummy_marked_while)

(* Ensures assignment expressions have only variables (needed as lvalues are parsed as expressions) *)
and validate_assign_exp mexp1 mexp2 =
  match Mark.data mexp1 with
  | Ast.Var s -> Ast.Assign (s, mexp2)
  | _ -> failwith "Assign_exp, lhs is not a symbol"

(* Validates for loops to ensure step statements do not have declarations *)
and validate h =
  let stm_data = Mark.data h in
  match stm_data with
  | Ast.Declare _ -> failwith "For loop: Declaration cannot be step statement"
  | Ast.Declare_intermediate _ ->
    failwith "For loop: Declaration_intermediate cannot be step statement"
  | _ -> process h
;;

(* Driver function for all the elaboration *)
let elaborate (initial_ast_raw : Ast.program_raw) : Ast.mstm =
  let main_ident, initial_ast = initial_ast_raw in
  match Symbol.name main_ident with
  | "main" -> expand_ast_list initial_ast
  | s -> failwith (sprintf "expected main, got %s" s)
;;

let%expect_test "Test simple elaboration" =
  let lexbuf = Lexing.from_string "int main() {int a = 0; return 0; }" in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
  |}]
;;

let%expect_test "Test simple if elaboration" =
  let lexbuf =
    Lexing.from_string "int main() {int x; if (true) {x = 5;} else {x = 2;} return x; }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of a simple while loop" =
  let lexbuf =
    Lexing.from_string "int main() {int x = 3; while (x < 5) {x++;} return x; }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of a simple for loop" =
  let lexbuf =
    Lexing.from_string
      "int main() {int x = 3; for (int i = 0; i < 5; i++) {x++;} return x; }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test parsing of blocks" =
  let lexbuf = Lexing.from_string "int main() {int x = 3; {{{}}} return x; }" in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test elaboration invalid while" =
  let lexbuf =
    Lexing.from_string
      "int main()\n\
      \  {\n\
      \   int i;\n\
      \   int x = 0;\n\
      \  \n\
      \   for (i = 0; i < 10; x += j) {\n\
      \       int j = 2;\n\
      \       i++;\n\
      \   }\n\
      \  \n\
      \   return 20;\n\
      \  }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test elaboration ternary" =
  let lexbuf =
    Lexing.from_string
      "int main () {\n\
      \        int x = 150;\n\
      \        int y = x < 150 ? 1 / 0 : 1;\n\
      \        return y;\n\
      \      }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test dangling else" =
  let lexbuf =
    Lexing.from_string
      "int main () {\n\
      \  int a = 5;\n\
      \  int b = 10;\n\
      \  if (a) if (b) true; else false;\n\
      \      }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test parsing of ops in random test -ve" =
  let lexbuf =
    Lexing.from_string
      "int main ()\n\
      \    {\n\
      \      int n;\n\
      \      int m;\n\
      \      int b;\n\
      \      bool d0;\n\
      \    \n\
      \      n = 254;\n\
      \      m = 1;\n\
      \      for (b = 0 ; n > 0 ; n /= 2) {\n\
      \        if (n % 2 == 0)\n\
      \          d0 = false;\n\
      \        else\n\
      \          d0 = true;\n\
      \        if (m < 0) return 1/0;\t/* raise exception on overflow */\n\
      \        if (!d0) { m *= 10; }\n\
      \        else { b = m + b;  m *= 10; }\n\
      \      }\n\
      \      return b;\n\
      \    }\n\
      \    "
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    }
  |}]
;;

let%expect_test "Test parsing of for loop" =
  let lexbuf =
    Lexing.from_string "int main () { int x = 0; for (i = 0; i < 5; i++) x++; return x; }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of for loop with int initialised" =
  let lexbuf =
    Lexing.from_string
      "int main () { int x = 0; for (int i = 0; i < 5; i++) x++; return x; }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of if with initialization" =
  let lexbuf = Lexing.from_string "int main () { if (true) int x = 0;}" in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    }
  |}]
;;
