(* L1 Compiler
 * Parsing
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Gluing together the pieces produced by ocamllex and ocamlyacc
 *)

(* parse filename = ast
 * will raise ErrorMsg.Error in case of lexing or parsing error
 *)

open Core
module SymbolMap = Symbol.Map
module SymbolSet = Type_modules.SymbolSet
module SymbolTable = Type_modules.SymbolTable

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

let parse (filename : string) : Ast.program =
  try
    let ast =
      In_channel.with_file filename ~f:(fun chan ->
        let lexbuf = Lexing.from_channel chan in
        initialize_lexbuf filename lexbuf;
        try C0_parser.program C0_lexer.initial lexbuf with
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

(* Example expect test -- see README *)
(* let%expect_test "Test sample function" =
  let lexbuf =
    Lexing.from_string
      "int f() {\n\
      \        return 5;\n\
      \      }\n\
      \      \n\
      \      int main() {\n\
      \        int f = f();\n\
      \        return f;\n\
      \      }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  let (_ : unit) = Typechecker.typecheck expanded in
  print_endline (Ast.Print.pp_program expanded);
  [%expect {|
    |}]
;; *)
(* 
let%expect_test "Test sample function" =
  let lexbuf =
    Lexing.from_string
      "int f() {\n\
      \        return 5;\n\
      \      }\n\
      \      \n\
      \      int main() {\n\
      \        int f;\n\
      \      f = f();\n\
      \        return f;\n\
      \      }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  let (_ : unit) = Typechecker.typecheck expanded in
  print_endline (Ast.Print.pp_program expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test sample function" =
  let lexbuf =
    Lexing.from_string
      "int f() {\n\
      \        return 5;\n\
      \      }\n\
      \      \n\
      \      int main() {\n\
      \        bool f = f();\n\
      \        return f;\n\
      \      }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  let (_ : unit) = Typechecker.typecheck expanded in
  print_endline (Ast.Print.pp_program expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test sample function" =
  let lexbuf =
    Lexing.from_string
      "int f() {\n\
      \        return 5;\n\
      \      }\n\
      \      \n\
      \      int main() {\n\
      \       f();\n\
      \       int f = 5;\n\
      \      return f;\n\
      \      }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  let (_ : unit) = Typechecker.typecheck expanded in
  print_endline (Ast.Print.pp_program expanded);
  [%expect {|
    |}]
;;

let%expect_test "Test sample function" =
  let lexbuf =
    Lexing.from_string
      "int f() {\n\
      \        return 5;\n\
      \      }\n\
      \      \n\
      \      int main() {\n\
      \       int f = 5;\n\
      \       f();\n\
      \      return f;\n\
      \      }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  let (_ : unit) = Typechecker.typecheck expanded in
  print_endline (Ast.Print.pp_program expanded);
  [%expect {|
    |}]
;; *)

(* let%expect_test "Test sample function" =
  let (_ : unit) = SymbolTable.clear Check_typedef.typedefs in
  let lexbuf =
    Lexing.from_string "\n    int main() {\n      int *x;\n      return 0;\n    }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    |}]
;;

let%expect_test "Test lexing" =
  let (_ : unit) = SymbolTable.clear Check_typedef.typedefs in
  let lexbuf =
    Lexing.from_string
      "\n  typedef int foo;\n  int main() {\n  foo *bar;\n  return 0;\n  }\n    "
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    |}]
;;

let%expect_test "Test lexing" =
  let (_ : unit) = SymbolTable.clear Check_typedef.typedefs in
  let lexbuf =
    Lexing.from_string "\n  int main() {\n  foo *bar;\n  return 0;\n  }\n    "
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    |}]
;;

let%expect_test "Test lexing" =
  let (_ : unit) = SymbolTable.clear Check_typedef.typedefs in
  let lexbuf = Lexing.from_string "\n    typedef int foo;\n    foo func();\n    " in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect {|
    |}]
;; *)

(* let header =
  "typedef int fpt;\n\n\
   fpt fadd(fpt x, fpt y);\n\
   fpt fsub(fpt x, fpt y);\n\
   fpt fmul(fpt x, fpt y);\n\
   fpt fdiv(fpt x, fpt y);\n\
   bool fless(fpt x, fpt y);\n\n\
   fpt itof(int n);\n\
   int ftoi(fpt x);\n\n\
   /* dub alias for double */\n\
   typedef struct dub* dub;\n\n\
   dub dadd(dub x, dub y);\n\
   dub dsub(dub x, dub y);\n\
   dub dmul(dub x, dub y);\n\
   dub ddiv(dub x, dub y);\n\
   bool dless(dub x, dub y);\n\n\
   dub itod(int n);\n\
   int dtoi(dub x);\n\n\
   /* print to stderr */\n\
   void print_fpt(fpt x);\n\
   void print_dub(dub x);\n\
   void print_int(int n);\n\
   void print_hex(int n);\n"
;;

let%expect_test "Test parenthesis" =
  let lexbuf =
    Lexing.from_string
      "\n\
      \      struct dub {\n\
      \        int c;\n\
      \        fpt e;\n\
      \        dub **f;\n\
      \      };\n\
      \      \n\
      \      fpt main() {\n\
      \          dub a = alloc(struct dub );\n\
      \        print_dub(a);\n\
      \        struct dub [] g= alloc_array(struct dub, 4);\n\
      \        return dtoi(**(g[4].f));\n\
      \      \n\
      \      }\n\
      \      "
  in
  let (_ : Ast.program) =
    C0_parser.program C0_lexer.initial (Lexing.from_string header)
  in
  (* let header_expand = Elaborate.elaborate header_parse in *)
  let program = C0_parser.program C0_lexer.initial lexbuf in
  let expanded = Elaborate.elaborate program in
  (* let header_ctx = Typechecker.header_typecheck header_expand in *)
  (* let typechecked = Typechecker.typecheck expanded header_ctx in
  print_endline (Ast.Print.pp_program typechecked); *)
  print_endline (Ast.Print.pp_program expanded);
  [%expect {|
    |}]
;; *)
