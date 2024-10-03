(* L3 Compiler
 * Runs all the functions required for regalloc
 *)

module AS = Assem

val regalloc
  :  AS.func list
  -> _skip_regalloc_per_function:int
  -> _skip_mcs:int
  -> debug:bool
  -> timestamps:Timestamp.t
  -> AS.func list
