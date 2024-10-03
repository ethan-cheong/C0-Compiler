(* L3 Compiler
 * Runs all the functions required for regalloc
 *)

module AS = Assem

val regalloc
  :  ?intf_graph_file:string
  -> AS.func list
  -> _skip_regalloc_per_function:int
  -> _skip_mcs:int
  -> _coalesce:bool
  -> debug:bool
  -> do_opt:bool
  -> print_intf_graph:bool
  -> timestamps:Timestamp.t
  -> AS.func list
