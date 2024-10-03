(* L5 Compiler
 * Remove Nops, replace jumps with fall-through in 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 *)

open Core
module ThreeAS = Threeaddrassem

let cleanup (func : ThreeAS.func) =
  let body = snd func in
  let no_nops =
    List.filter body ~f:(fun instr ->
      match instr with
      | Nop -> false
      | _ -> true)
  in
  let label_counter = Hashtbl.create ~growth_allowed:true ~size:10 (module String) in
  List.iter no_nops ~f:(fun instr ->
    match instr with
    (* Only labels that are referenced once can be pruned *)
    | Jump s ->
      Hashtbl.update label_counter s ~f:(fun opt ->
        match opt with
        | None -> 1
        | Some c -> c + 1)
    | If { lt; lf; _ } ->
      Hashtbl.update label_counter lt ~f:(fun opt ->
        match opt with
        | None -> 1
        | Some c -> c + 1);
      Hashtbl.update label_counter lf ~f:(fun opt ->
        match opt with
        | None -> 1
        | Some c -> c + 1)
    | _ -> ());
  let rec cleanup_helper acc lst =
    match lst with
    | [] -> List.rev acc
    | ThreeAS.Jump s :: Label t :: tl
      when String.(s = t) && Hashtbl.find_exn label_counter s = 1 -> cleanup_helper acc tl
    | ThreeAS.Jump s :: Label t :: tl when String.(s = t) ->
      ThreeAS.Label t :: cleanup_helper acc tl
    | hd :: tl -> hd :: cleanup_helper acc tl
  in
  fst func, cleanup_helper [] no_nops
;;
