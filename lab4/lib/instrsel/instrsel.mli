(* L1 Compiler
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Instruction selection for assembly, takes in codegen-ed assembly
 * Expands the instructions into their "final assem" counterparts
 * without register allocation (i.e. registers and spilling)
 *)

val instr_sel : Threeaddrassem.program -> only_main:bool -> Assem.func list
