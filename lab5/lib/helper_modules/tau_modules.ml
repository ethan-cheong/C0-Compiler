open Core

module TauTable = Hashtbl.Make (struct
  type t = Ast.tau [@@deriving compare, sexp, hash]
end)
