(* L1 Compiler
 * Temporaries
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core

type t = int [@@deriving sexp, compare, hash]

let counter = ref 1
let reset () = counter := 1

(* Get the current temp counter*)
let get_counter () = !counter

let create () =
  let t = !counter in
  incr counter;
  t
;;

let make x = x
let name t = "%t" ^ string_of_int t

include Comparable.Make (Int)
