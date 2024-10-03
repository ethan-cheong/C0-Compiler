(* L1 Compiler
 * TypeChecker
 * After Typechecking, there should be an additional phase
 * to remove declarations
 *)

type env =
  { gamma : Ast.tau Symbol.Map.t
  ; delta : Type_modules.SymbolSet.t
  ; epsilon : (Ast.param list * Ast.tau * bool) Type_modules.SymbolTable.t
      (* The delta as stated in lab 3*)
  ; omega : Ast.tau Type_modules.SymbolTable.t
  ; used : unit Type_modules.SymbolTable.t
  ; returns : bool
  }

(* prints error message and raises ErrorMsg.error if error found *)
val typecheck : Ast.program -> env -> unit
val header_typecheck : Ast.program -> env
