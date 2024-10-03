(* C0 Compiler
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *)
type t

val init_timestamps : unit -> t
val mark_timestamp : t -> string -> unit
val print_timestamps : t -> string
