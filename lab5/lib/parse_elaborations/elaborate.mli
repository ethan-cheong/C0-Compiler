(* L1 Compiler
 * Converting from initial AST into elaborated form
 *)

(* parse filename = ast
 * will raise Error_msg.Error in case of lexing or parsing error
 *)
val elaborate : Ast.program -> Ast.program
