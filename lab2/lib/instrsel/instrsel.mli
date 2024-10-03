(* L1 Compiler
 * Instruction selection for assembly, takes in codegen-ed assembly
 * Expands the instructions into their "final assem" counterparts
 * without register allocation (i.e. registers and spilling)
 *)

val instr_sel : Threeaddrassem.instr list -> Assem.instr list
