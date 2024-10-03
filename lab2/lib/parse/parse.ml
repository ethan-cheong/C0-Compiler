(* L1 Compiler
 * Parsing
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Gluing together the pieces produced by ocamllex and ocamlyacc
 *)

(* parse filename = ast
 * will raise ErrorMsg.Error in case of lexing or parsing error
 *)

open Core

(* In order for the lexbuf to correctly track source locations
 * we have to initialize the filename in the positions tracked by
 * the lexbuf.
 *)
let initialize_lexbuf (filename : string) : Lexing.lexbuf -> unit =
  let open Lexing in
  let pos = { pos_fname = filename; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 } in
  fun lexbuf ->
    lexbuf.lex_start_p <- pos;
    lexbuf.lex_curr_p <- pos
;;

let parse (filename : string) : Ast.program_raw =
  try
    let ast =
      In_channel.with_file filename ~f:(fun chan ->
        let lexbuf = Lexing.from_channel chan in
        initialize_lexbuf filename lexbuf;
        try C0_parser.program_raw C0_lexer.initial lexbuf with
        | _ ->
          (* Parse error; attempt to print a helpful error message. *)
          let src_span =
            Mark.of_positions Lexing.(lexbuf.lex_start_p) Lexing.(lexbuf.lex_curr_p)
          in
          Error_msg.error C0_lexer.errors (Some src_span) ~msg:"Parse error.";
          raise Error_msg.Error)
    in
    if Error_msg.has_any_errors C0_lexer.errors
    then (
      Out_channel.prerr_endline "Lex error.";
      raise Error_msg.Error)
    else ast
  with
  | Sys_error s ->
    (* Probably file not found or permissions errors. *)
    Out_channel.prerr_endline ("System error: " ^ s);
    raise Error_msg.Error
;;
(* 
(* Example expect test -- see README *)
let%expect_test "Test parsing of an empty program" =
  let lexbuf =
    Lexing.from_string "int main() {int x = 3; int y = -x + 4; return x + y * x / 3; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect
    {|
    int main {
    int x = 3;
    int y = (-(x) + 4);
    return (x + ((y * x) / 3));
    }
  |}]
;;

let%expect_test "Test parsing of a simple while loop" =
  let lexbuf =
    Lexing.from_string "int main() {int x = 3; while (x < 5) {x++;} return x; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of a simple for loop" =
  let lexbuf =
    Lexing.from_string
      "int main() {int x = 3; for (int i = 0; i < 10; x += j) {x += 1;} return x; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of simple if" =
  let lexbuf =
    Lexing.from_string "int main() {int x; if (true) {x = 5;} else {x = 2;} return x; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    }
  |}]
;;

(* TODO compare against test cases for operator precedence *)
let%expect_test "Test parsing of a simple ternary operator" =
  let lexbuf = Lexing.from_string "int main() {int x = (1 > 2) ? 3 : 4; return x; }" in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    }
  |}]
;;

(* Be sure to compare against test cases for operator precedence *)
let%expect_test "Test parsing of a simple ternary operator, no brackets" =
  let lexbuf = Lexing.from_string "int main() {int x = 1 > 2 ? 3 : 4; return x; }" in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    }
  |}]
;;

let%expect_test "Test parsing of blocks" =
  let lexbuf =
    Lexing.from_string
      "int main() {int a; {int b; b = 5; a = b;} int b; b = a; return b; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    }
  |}]
;;

let%expect_test "Test parsing of blocks" =
  let lexbuf =
    Lexing.from_string "int main() {int a = 0; a++; a += 1; int b = 1; b--; return b; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    }
  |}]
;;

let%expect_test "Test parsing of blocks" =
  let lexbuf =
    Lexing.from_string
      "int main()\n\
      \    {\n\
      \      int ret = 0xffffffff;\n\
      \      {\n\
      \        int x = 0;\n\
      \        x++;\n\
      \        ret += x;\n\
      \      }\n\
      \      {\n\
      \        int x = 0X2;\n\
      \        ret += x;\n\
      \      }\n\
      \      return ret;\n\
      \    }\n\
      \    "
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    }
  |}]
;;

let%expect_test "Test parsing of postops" =
  let lexbuf = Lexing.from_string "int main() {int a = 0; a++; b = 1; b--; return b; }" in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
  |}]
;;

let%expect_test "Test parsing of postops with -ve" =
  let lexbuf =
    Lexing.from_string "int main() {int a = 0; -a++; b = 1; +b--; return b; }"
  in
  let _, program = C0_parser.program_raw C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
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
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test order of ops" =
  let lexbuf =
    Lexing.from_string
      "int main() {\n\
      \        int a = 8 * 1 - 4 + 7 / 4 * 9 - 3 + 0;\n\
      \        return a;\n\
      \    }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test elaboration of postops" =
  let lexbuf = Lexing.from_string "int main() {int a = 0; a++; b = 1; b--; return b; }" in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test invalid for loop step statement" =
  let lexbuf =
    Lexing.from_string "int main() {for (int i = 0; i < 5; int j) {j = 5; } return 0; }"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test main as ident" =
  let lexbuf =
    Lexing.from_string
      "int main(){\n\
      \      int a = 1;\n\
      \      if (true?false:true?true:true) return 1;\n\
      \      return 0;}"
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test order of ops" =
  let lexbuf =
    Lexing.from_string
      "int main() {\n\
      \        int a = 8 * 1 - 4 + 7 / 4 * 9 - 3 + 0;\n\
      \        return a;\n\
      \    }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test elaboration of postops" =
  let lexbuf = Lexing.from_string "int main() {int a = 0; a++; b = 1; b--; return b; }" in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test invalid for loop step statement" =
  let lexbuf =
    Lexing.from_string "int main() {for (int i = 0; i < 5; int j) {j = 5; } return 0; }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  print_endline (Ast.Print.pp_mstm expanded);
  [%expect {|
    |}]
;; *)
