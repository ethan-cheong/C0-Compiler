(* L1 Compiler
 * Temporaries
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core

type t [@@deriving sexp, compare, hash, equal]

(* All temps come with an associated size. *)
type size =
  | BYTE
  | DOUBLE
  | QUAD
[@@deriving sexp, compare, hash, equal]

module Temp : sig
  type t [@@deriving sexp, compare, hash, equal]

  include Comparable.S with type t := t
end

(* Get the current temp counter. *)
val get_counter : unit -> int

(* resets temp numbering *)
val reset : unit -> unit

(* create a temp with the specified size *)
val create_of_size : size -> t

(* returns the name of a temp *)
val name : t -> string

(* returns the size of a temp *)
val size : t -> size

(* converts temp size to an Int32.t *)
val size_to_int32 : size -> Int32.t

(* converts temp size to an Int64.t *)
val size_to_int64 : size -> Int64.t

(* Make a copy of the temp with a specified version *)
val make_version : t -> int -> t
val get_id : t -> int
val get_version : t -> int
