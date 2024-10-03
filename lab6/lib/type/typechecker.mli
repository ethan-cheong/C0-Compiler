(* L1 Compiler
 * TypeChecker
 * After Typechecking, there should be an additional phase
 * to remove declarations
 *)

module SymbolTable = Type_modules.SymbolTable

type anno_state =
  { in_ensures : bool
  ; in_stmt : bool
  ; in_loop : bool
  ; in_header : bool
  ; ret_type : Ast.tau
  ; arr_type : Ast.tau
  }

type env =
  { gamma : Ast.tau Symbol.Map.t
  ; delta : Type_modules.SymbolSet.t
      (* epsilon is the namespace for functions and their declarations *)
  ; epsilon : (Ast.param list * Ast.tau * bool) SymbolTable.t
      (* omega is namespace for typedefs/types *)
  ; omega : Ast.tau SymbolTable.t
      (* sigma is the namespace for structs and their definitions *)
  ; sigma : (Ast.tau SymbolTable.t * bool) SymbolTable.t
  ; used : unit Type_modules.SymbolTable.t (* For functions only *)
  ; returns : bool (* For functions only *)
  ; anno_state : anno_state
  }

(* prints error message and raises ErrorMsg.error if error found *)
(* Must return the program with type values after typechecking *)
val typecheck : Ast.program -> env -> Ast.program * env
val header_typecheck : Ast.program -> Ast.program * env
