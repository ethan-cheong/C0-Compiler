(* L1 Compiler
 * Temporaries
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core

type size =
  | BYTE
  | DOUBLE
  | QUAD
[@@deriving sexp, compare, hash, equal]

type version = int [@@deriving sexp, compare, hash, equal]
type ident = int [@@deriving sexp, compare, hash, equal]
type t = ident * size * version [@@deriving sexp, compare, hash, equal]

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
  | BYTE -> t, BYTE, 0
  | DOUBLE -> t, DOUBLE, 0
  | QUAD -> t, QUAD, 0
;;

let size (_, size, _) = size
let get_id (id, _, _) = id

let name (id, size, version) =
  match size with
  | BYTE -> "%t" ^ string_of_int id ^ "b_" ^ string_of_int version
  | DOUBLE -> "%t" ^ string_of_int id ^ "d_" ^ string_of_int version
  | QUAD -> "%t" ^ string_of_int id ^ "q_" ^ string_of_int version
;;

let size_to_int32 = function
  | BYTE -> Int32.of_int_exn 1
  | DOUBLE -> Int32.of_int_exn 4
  | QUAD -> Int32.of_int_exn 8
;;

let size_to_int64 = function
  | BYTE -> Int64.of_int_exn 1
  | DOUBLE -> Int64.of_int_exn 4
  | QUAD -> Int64.of_int_exn 8
;;

let make_version (id, size, _) version = id, size, version
let get_version (_, _, version) = version
