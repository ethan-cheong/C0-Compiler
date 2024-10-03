(* L1 Compiler
 * Elaborate out the initialisation of a declaration after type checking
 *)

module SymbolTable = Type_modules.SymbolTable
module Int32Table = Type_modules.Int32Table

val elaborate_decl
  :  ?debug:bool
  -> Ast.program
  -> Int64.t Int32Table.t SymbolTable.t
     * Int32.t SymbolTable.t SymbolTable.t
     * (Int64.t * Int64.t) SymbolTable.t
  -> Ast.program * (Int64.t * Int64.t) SymbolTable.t

val elaborate_header
  :  ?debug:bool
  -> Ast.program
  -> Typechecker.env
  -> Int64.t Int32Table.t SymbolTable.t
     * Int32.t SymbolTable.t SymbolTable.t
     * (Int64.t * Int64.t) SymbolTable.t
