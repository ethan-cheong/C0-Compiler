(* L1 Compiler
 * Temporaries
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core

type size =
  | DOUBLE
  | QUAD
[@@deriving sexp, compare, hash, equal]

type ident = int [@@deriving sexp, compare, hash, equal]
type t = ident * size [@@deriving sexp, compare, hash, equal]

module Temp : sig
  type t [@@deriving sexp, compare, hash, equal]

  include Comparable.S with type t := t
end = struct
  module T = struct
    type t [@@deriving sexp, compare, hash, equal]
  end

  include T
  include Comparable.Make (T)
end

let counter = ref 1
let reset () = counter := 1

(* Get the current temp counter*)
let get_counter () = !counter

let create_of_size s =
  let t = !counter in
  incr counter;
  match s with
  | DOUBLE -> t, DOUBLE
  | QUAD -> t, QUAD
;;

let size t = snd t

let name t =
  match size t with
  | DOUBLE -> "%t" ^ string_of_int (fst t) ^ "d"
  | QUAD -> "%t" ^ string_of_int (fst t) ^ "q"
;;

let size_to_int32 = function
  | DOUBLE -> Int32.of_int_exn 4
  | QUAD -> Int32.of_int_exn 8
;;

let size_to_int64 = function
  | DOUBLE -> Int64.of_int_exn 4
  | QUAD -> Int64.of_int_exn 8
;;

let make t = t, DOUBLE
