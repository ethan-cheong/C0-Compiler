(* C0 Compiler
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *)

open Core

type t = (string, int) Hashtbl.t

let init_timestamps () = String.Table.create ()

(* Intended use: call before and after a phase with the phase name. *)
let mark_timestamp timestamp_table (tag : string) : unit =
  let timestamp =
    Int63.(to_int_exn (Time_now.nanoseconds_since_unix_epoch () / of_int_exn 1000000))
  in
  match Hashtbl.find timestamp_table tag with
  | Some prev_timestamp ->
    Hashtbl.set timestamp_table ~key:tag ~data:(timestamp - prev_timestamp)
  | None -> Hashtbl.set timestamp_table ~key:tag ~data:timestamp
;;

(* Output string of timestamps in descending order of time taken *)
let print_timestamps timestamp_table : string =
  let sorted_times =
    List.sort
      ~compare:(fun (_, v1) (_, v2) -> -Int.compare v1 v2)
      (Hashtbl.to_alist timestamp_table)
  in
  List.fold sorted_times ~init:"\n-----Phase times-----\n" ~f:(fun acc (phase, time) ->
    acc ^ Printf.sprintf "%s: %dms\n" phase time)
;;
