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
module FinalAS = Finalassem

(* Current rule: use an intermediate register if both are refs. *)
let translate_mov (dest : AS.operand) (src : AS.operand) : FinalAS.instr list =
  match src, dest with
  | _, Imm _ -> failwith "Destination of mov cannot be an immediate"
  | Ref s, Ref d ->
    FinalAS.
      [ Binop { op = Mov; word_size = L; src = Reg R10D; dest = final_of_operand (Ref d) }
      ; Binop { op = Mov; word_size = L; src = final_of_operand (Ref s); dest = Reg R10D }
      ]
    (* failwith "No two refs for movs in instr sel" *)
  | _ ->
    FinalAS.
      [ Binop
          { op = FinalAS.Mov
          ; word_size = L
          ; src = final_of_operand src
          ; dest = final_of_operand dest
          }
      ]
;;

(**  If we have a binop `d = r1 @ r2 ` that is translated using the following 
    template:

      movl r1, %r10
      instr r2, %r10
      movl %r10, d
    
      then we can use the function below.
*)

(** `d = r1 / r2` is converted to 
      movl r1, %eax
      cltd
      idivl   r2
      movl    %eax, d
*)

let translate_unop (op : AS.one_addr_op) (src : AS.operand) : FinalAS.instr list =
  let finalas_op, word_size =
    match op with
    | AS.IDiv -> FinalAS.IDiv, FinalAS.L
    | AS.Pop -> FinalAS.Pop, FinalAS.Q
    | AS.Push -> FinalAS.Push, FinalAS.Q
  in
  match src with
  | Imm _ -> failwith "Destination of div cannot be an immediate"
  | _ -> FinalAS.[ Unop { op = finalas_op; word_size; src = final_of_operand src } ]
;;

let translate_jumpc (cmp : AS.comparison) (label : AS.operand) : FinalAS.instr list =
  FinalAS.[ Jc { cmp = final_of_comparison cmp; label = final_of_operand label } ]
;;

let translate_jump (label : AS.operand) : FinalAS.instr list =
  FinalAS.[ Jmp { label = final_of_operand label } ]
;;

let translate_test (lhs : AS.operand) (rhs : AS.operand) : FinalAS.instr list =
  FinalAS.[ Test { lhs = final_of_operand lhs; rhs = final_of_operand rhs } ]
;;

let translate_cmp (lhs : AS.operand) (rhs : AS.operand) : FinalAS.instr list =
  FinalAS.[ Cmp { lhs = final_of_operand lhs; rhs = final_of_operand rhs } ]
;;

let translate_nullop (op : AS.zero_addr_op) =
  let final_op =
    match op with
    | AS.Cltd -> FinalAS.Cltd
  in
  FinalAS.[ Nullop { op = final_op } ]
;;

let translate_binop (op : AS.two_addr_op) (dest : AS.operand) (src : AS.operand)
  : FinalAS.instr list
  =
  let instr =
    match op with
    | Add ->
      FinalAS.Binop
        { op = FinalAS.Add
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | Sub ->
      FinalAS.Binop
        { op = FinalAS.Sub
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | IMul ->
      FinalAS.Binop
        { op = FinalAS.IMul
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | Xor ->
      FinalAS.Binop
        { op = FinalAS.Xor
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | And ->
      FinalAS.Binop
        { op = FinalAS.And
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | Or ->
      FinalAS.Binop
        { op = FinalAS.Or
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | Sal ->
      FinalAS.Binop
        { op = FinalAS.Sal
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
    | Sar ->
      FinalAS.Binop
        { op = FinalAS.Sar
        ; word_size = L
        ; src = FinalAS.final_of_operand src
        ; dest = FinalAS.final_of_operand dest
        }
  in
  [ instr ]
;;

let code_gen (lst : AS.instr list) : FinalAS.instr list =
  let rec code_gen_helper (lst : AS.instr list) (acc : FinalAS.instr list)
    : FinalAS.instr list
    =
    match lst with
    | [] -> acc
    (* Epilogue, including Ret *)
    | Mov { dest; src } :: t -> code_gen_helper t (translate_mov dest src @ acc)
    | Binop { op; dest; src } :: t -> code_gen_helper t (translate_binop op dest src @ acc)
    | Cmp { lhs; rhs } :: t -> code_gen_helper t (translate_cmp lhs rhs @ acc)
    | Unop { op; src; _ } :: t -> code_gen_helper t (translate_unop op src @ acc)
    | Nullop { op } :: t -> code_gen_helper t (translate_nullop op @ acc)
    | Directive d :: t -> code_gen_helper t ([ FinalAS.Directive d ] @ acc)
    | Comment c :: t -> code_gen_helper t ([ FinalAS.Comment c ] @ acc)
    | JumpC { cmp; label } :: t -> code_gen_helper t (translate_jumpc cmp label @ acc)
    | Jump { label } :: t -> code_gen_helper t (translate_jump label @ acc)
    | Test { lhs; rhs } :: t -> code_gen_helper t (translate_test lhs rhs @ acc)
    | AS.Label l :: t -> code_gen_helper t ([ FinalAS.Label l ] @ acc)
    | Ret :: t -> code_gen_helper t (FinalAS.Ret :: acc)
  in
  List.rev (code_gen_helper lst [])
;;
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
