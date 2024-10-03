(* L1 Compiler
 * AST -> IR Translator
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Translates elaborated Abstract Syntax Tree into IR.
 *)

(* translate list of elaborated abstract syntax trees to IR. *)
val translate : Ast.program -> Tree.program
