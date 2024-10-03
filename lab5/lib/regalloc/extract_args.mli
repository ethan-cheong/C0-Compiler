(* L3 Compiler
 * Converts from assem into liveness list 
 * Parses the input in reverse
 * Follow the algorithm from recitation


 * Now, multiple things can be defined on each line
 * Also, need to run liveness on each
 * 

 * Input: List of (list of assem instructions)
 * 1. Each list of assem instructions is a function
 * 2. Before processing each list, we need to know what each function call defines
 * 3. Assume that the first line is the function label
 * 4. Within that line, extract all the registers and store into a list
 * 5. Pass this list around when doing liveness


 *)
open Core
module AS = Assem

(* List of only the func labels *)
val extract_args : AS.func list -> (string, Regalloc_modules.NodeSet.t) Hashtbl.t
