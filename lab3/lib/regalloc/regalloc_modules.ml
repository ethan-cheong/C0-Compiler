open Core
module NodeSet = Set.Make (Node)
module NodeTable = Hashtbl.Make (Node)
module Int32Set = Type_modules.Int32Set
module Int32Table = Type_modules.Int32Table

type liveness_tables =
  { uses_table : NodeSet.t Int32Table.t
  ; defs_table : NodeSet.t Int32Table.t
  ; movs_table : bool Int32Table.t
  ; jump_table : (String.t, Int32.t) Hashtbl.t
  ; pred_table : Int32Set.t Int32Table.t
  ; liveout_table : NodeSet.t Int32Table.t
  ; livein_table : NodeSet.t Int32Table.t
  }
