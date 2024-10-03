(* L5 Compiler
 * High level module for SSA-based optimizations
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>
 *)
open Core

(** Cleans up the cfg_outputs directory. *)
let clear_folder () =
  let path = "./cfg_outputs" in
  Sys.readdir path |> Array.iter ~f:(fun name -> Sys.remove (Filename.concat path name))
;;

let print_label_to_body tbl =
  Hashtbl.iteri tbl ~f:(fun ~key:label ~data:body ->
    Printf.printf
      "\n%s:%s\n"
      label
      (List.fold ~init:"" ~f:(fun acc instr -> acc ^ "\n" ^ Ssa.format_instr instr) body))
;;
