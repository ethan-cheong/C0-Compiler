(* L1 Compiler
 * Assembly Code Generator for final representation of assembly 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Converts assembly with registers and stack refs to x86 assembly.
 *)
open Core
module AS = Assem

(* Current rule: use an intermediate register if both are refs.
   We load from src into R10, then store from R10 into mem. *)
let expand_mov (dest : AS.operand) (src : AS.operand) : AS.instr list =
  match src, dest with
  | _, _ when AS.equal_operand src dest -> [] (* Delete replicated movs *)
  | Temp _, _ | _, Temp _ -> failwith "IR should have no more temps after stack spilling"
  | _, Imm _ -> failwith "Destination of mov cannot be an immediate"
  | ( Stack_ref { size = src_size; offset = src_offset }
    , Stack_ref { size = dest_size; offset = dest_offset } ) ->
    AS.
      [ Store
          { src = Reg { reg = R10; size = src_size }
          ; addr = Reg { reg = SP; size = dest_size }
          ; offset = dest_offset
          }
      ; Load
          { addr = Reg { reg = SP; size = src_size }
          ; dest = Reg { reg = R10; size = src_size }
          ; offset = src_offset
          }
      ]
  | _ -> AS.[ Mov { src; dest } ]
;;

let code_gen (lst : AS.func list) : AS.func list =
  let rec code_gen_rec (lst : AS.instr list) (acc : AS.instr list) : AS.instr list =
    match lst with
    | [] -> acc
    | Mov { dest; src } :: t -> code_gen_rec t (expand_mov dest src @ acc)
    | h :: t -> code_gen_rec t (h :: acc)
  in
  let code_gen_helper (func : AS.func) : AS.func =
    let signature, body = func in
    let translated_body = List.rev (code_gen_rec body []) in
    signature, translated_body
  in
  List.map lst ~f:(fun l -> code_gen_helper l)
;;
(* Apply code_gen_helper to all lists and flatten the result.*)

(* 
let%expect_test "Test what conditionals do in tree" =
  Temp.reset ();
  let lexbuf =
    Lexing.from_string
      "\n\
      \  int main() {\n\
      \    bool x = ((5< (10+6)) || (54 <= (6*(20+(99)))));\n\
      \  }\n\
      \      "
  in
  let program = C0_parser.program_raw C0_lexer.initial lexbuf in
  let ast = Elaborate.elaborate program in
  let ir, temp_counter = Trans.translate ast in
  let assem = Codegen.code_gen ir temp_counter in
  let assem_no_temps = Stackspill.stack_spill assem in
  let final = instr_sel assem_no_temps in
  Printf.printf
    "----------AST------------\n\
     %s\n\
     ------------IR--------------\n\
     %s\n\
     ------------Assem-----------\n\
     Temp Counter: %d\n"
    (Ast.Print.pp_mstm ast)
    (Tree.Print.pp_program ir)
    temp_counter;
  let output_assem line = Printf.printf "\t%s\n" (AS.format line) in
  let output_final line = Printf.printf "\t%s\n" (FinalAS.format line) in
  List.iter ~f:output_assem assem_no_temps;
  Printf.printf "\n---------Final----------\n";
  List.iter ~f:output_final final;
  [%expect {|
    Something ... something should print
  |}]
;; *)
