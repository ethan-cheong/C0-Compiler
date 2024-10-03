(* L1 Compiler
 * Converts from assem into liveness list 
 * Parses the input in reverse
 * Follow the algorithm from recitation


 * Implementation: have 4 hashmaps

 1. Get the maximum number of lines as line_count
 2. Keep track of the successor lines using succ_table (line to list of lines/hashtbl of lines)
 NOTE: May iterate a few times in the future here.
 3. For each line:
 3a. Parse each line to find what it uses and defines
 3b. Store into liveout_table, defs_table, uses_table
 3c. Find the liveout by referencing the livein_table (map from line to list of values)
 3d. Store into liveout_table
 3e. Find livein by creating hashtable to union (liveout - defs), then union uses
 3f. Store into livein_table
 3g. Store the mov in the mov_table

 4. For each line (front to back)
 4a. Update a json format to store the required values
 *)
open Core
module AS = Assem

type line =
  { uses : AS.operand list
  ; defines : AS.operand list
  ; live_out : AS.operand list
  ; move : bool
  ; line_number : Int32.t
  }

val liveness : AS.instr list -> line list
val string_of_op_lst : line list -> string
