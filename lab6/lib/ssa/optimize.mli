(* L5 Compiler
 * Run all SSA-based optimizations. 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 *)
module ThreeAS = Threeaddrassem

(* Convert to SSA, run optimizations, convert back *)
(* val optimize : ThreeAS.func list -> print_cfg:bool -> unit *)
val optimize
  :  ThreeAS.func list
  -> print_cfg:bool
  -> _deadcode_elim:bool
  -> _constant_prop:bool
  -> _sccp:bool
  -> _strength:bool
  -> ThreeAS.func list
