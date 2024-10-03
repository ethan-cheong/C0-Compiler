(* L1 Compiler
 * AST -> IR Translator
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Translates elaborated Abstract Syntax Tree into IR.
 *)
module SymbolTable = Type_modules.SymbolTable

(* translate list of elaborated abstract syntax trees to IR. *)
val translate : Ast.program -> (Int64.t * Int64.t) SymbolTable.t -> Tree.program
