(* L1 Compiler
 * Converting from initial AST into elaborated form
 *)

(* parse filename = ast
 * will raise Error_msg.Error in case of lexing or parsing error
 *)

(* 
   Elaboration Rules 
   
*)

val elaborate : Ast.program_raw -> Ast.mstm
