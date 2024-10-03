open Core
module AS = Assem
module SymbolTable = Hashtbl.Make (Symbol)
module SymbolSet = Set.Make (Symbol)
module Int32Set = Set.Make (Int32)
module Int32Table = Hashtbl.Make (Int32)
module IntSet = Set.Make (Int)
module StringSet = Set.Make (String)
module TempSet = Set.Make (Temp)
module FieldMap = Map.Make (String)
module FieldTable = Hashtbl.Make (String)
(* module NodeSet = Set.Make (Node)
module NodeTable = Hashtbl.Make (Node) *)

module OperandTable = Hashtbl.Make (struct
  type t = AS.operand [@@deriving compare, sexp, hash]
end)

module OperandSet = Set.Make (struct
  type t = AS.operand [@@deriving compare, sexp, hash]
end)

module SSAVarTable = Hashtbl.Make (struct
  type t = Ssa.operand [@@deriving compare, sexp, hash]
end)

module SSAVarSet = Set.Make (struct
  type t = Ssa.operand [@@deriving compare, sexp, hash]
end)
