(* L1 Compiler
 * Parsing
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Gluing together the pieces produced by ocamllex and menhir.
 *)

(* parse filename = ast
 * will raise Error_msg.Error in case of lexing or parsing error
 *)
val parse : string -> Ast.program
