open Core
module AS = Assem
module SymbolTable = Hashtbl.Make (Symbol)
module SymbolSet = Set.Make (Symbol)
module Int32Set = Set.Make (Int32)
module Int32Table = Hashtbl.Make (Int32)
module TempSet = Set.Make (Temp)
(* module NodeSet = Set.Make (Node)
module NodeTable = Hashtbl.Make (Node) *)

module OperandTable = Hashtbl.Make (struct
  type t = AS.operand [@@deriving compare, sexp, hash]
end)

module OperandSet = Set.Make (struct
  type t = AS.operand [@@deriving compare, sexp, hash]
end)
