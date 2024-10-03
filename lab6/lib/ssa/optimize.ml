(* L5 Compiler
 * Run all SSA-based optimizations. 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 *)
module ThreeAS = Threeaddrassem
open Core

(* Convert to SSA, run optimizations, convert back *)
let optimize
  (code : ThreeAS.func list)
  ~print_cfg
  ~_deadcode_elim
  ~_constant_prop
  ~_sccp
  ~_strength
  =
  if print_cfg then Ssa_utils.clear_folder ();
  let signatures = List.map ~f:fst code in
  (* let counter = ref 0 in *)
  let ssa = List.map ~f:(fun func -> Abstrtossa.abstr_to_ssa ~print_cfg func) code in
  List.map2_exn signatures ssa ~f:(fun signature body ->
    let body = if _deadcode_elim then Deadcode_elim.run_adce body else body in
    let body = if _sccp then Sccp.sccp body else body in
    let body = if _constant_prop then Constant_prop.scp body else body in
    let body = if _strength then Strength.strength body else body in
    let body = if _deadcode_elim then Deadcode_elim.run_adce body else body in
    let body' = (Ssatoabstr.ssa_to_abstr body ~print_cfg : ThreeAS.instr list) in
    signature, body')
;;

(* TODOs (ethan do once deadcode elim is done): Change ssatoabstr - if the last thing in a function is NOT If, Ret, Jump, 
   then we can add the phi functions directly (it was deadcode eliminated). Otherwise,
   we apply the current logic we are doing.  *)
