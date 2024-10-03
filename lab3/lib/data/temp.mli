(* L1 Compiler
 * Temporaries
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

open Core

type t [@@deriving sexp, compare, hash]

include Comparable.S with type t := t

(* Get the current temp counter. *)
val get_counter : unit -> int

(* resets temp numbering *)
val reset : unit -> unit

(* returns a unique 32-bit temp *)
val create : unit -> t

(* returns the name of a temp *)
val name : t -> string

(* used for convenience when testing. Should not be called in code.*)
val make : int -> t
