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
  | _ ->
    FinalAS.
      [ Binop
          { op = Mov
          ; word_size = L
          ; src = final_of_operand src
          ; dest = final_of_operand dest
          }
      ]
;;

(** Recall that all instructions need to be translated in reverse. 
    `d = s1 + s2` is converted to

      movl s1, %r10
      addl s2, %r10
      movl %r10, d

    *)
let translate_add (dest : AS.operand) (lhs : AS.operand) (rhs : AS.operand)
  : FinalAS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of add cannot be an immediate"
  | _ ->
    FinalAS.
      [ Binop { op = Mov; word_size = L; src = Reg R10D; dest = final_of_operand dest }
      ; Binop { op = Add; word_size = L; src = final_of_operand rhs; dest = Reg R10D }
      ; Binop { op = Mov; word_size = L; src = final_of_operand lhs; dest = Reg R10D }
      ]
;;

(** `d = s1 - s2` is converted to

      movl s1, %r10
      subl s2, %r10
      movl %r10, d

    *)
let translate_sub (dest : AS.operand) (lhs : AS.operand) (rhs : AS.operand)
  : FinalAS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of sub cannot be an immediate"
  | _ ->
    FinalAS.
      [ Binop { op = Mov; word_size = L; src = Reg R10D; dest = final_of_operand dest }
      ; Binop { op = Sub; word_size = L; src = final_of_operand rhs; dest = Reg R10D }
      ; Binop { op = Mov; word_size = L; src = final_of_operand lhs; dest = Reg R10D }
      ]
;;

(** `d = r1 * r2` is converted to 

      movl r1, %r10
      imull r2, %r10
      movl %r10, d
    
*)
let translate_mul (dest : AS.operand) (lhs : AS.operand) (rhs : AS.operand)
  : FinalAS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of mul cannot be an immediate"
  | _ ->
    FinalAS.
      [ Binop { op = Mov; word_size = L; src = Reg R10D; dest = final_of_operand dest }
      ; Binop { op = IMul; word_size = L; src = final_of_operand rhs; dest = Reg R10D }
      ; Binop { op = Mov; word_size = L; src = final_of_operand lhs; dest = Reg R10D }
      ]
;;

(** `d = r1 / r2` is converted to 

      movl r1, %eax
      cltd
      idivl   r2
      movl    %eax, d
    
*)
let translate_div (dest : AS.operand) (lhs : AS.operand) (rhs : AS.operand)
  : FinalAS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of div cannot be an immediate"
  | _ ->
    FinalAS.
      [ Binop { op = Mov; word_size = L; src = Reg EAX; dest = final_of_operand dest }
      ; Unop { op = IDiv; word_size = L; src = final_of_operand rhs }
      ; Nullop { op = Cltd }
      ; Binop { op = Mov; word_size = L; src = final_of_operand lhs; dest = Reg EAX }
      ]
;;

(** `d = r1 % r2` is converted to 

      movl r1, %eax
      cltd
      idivl   r2
      movl    %edx, d
    
*)
let translate_mod (dest : AS.operand) (lhs : AS.operand) (rhs : AS.operand)
  : FinalAS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of mod cannot be an immediate"
  | _ ->
    FinalAS.
      [ Binop { op = Mov; word_size = L; src = Reg EDX; dest = final_of_operand dest }
      ; Unop { op = IDiv; word_size = L; src = final_of_operand rhs }
      ; Nullop { op = Cltd }
      ; Binop { op = Mov; word_size = L; src = final_of_operand lhs; dest = Reg EAX }
      ]
;;

let translate_binop
  (op : AS.operation)
  (dest : AS.operand)
  (lhs : AS.operand)
  (rhs : AS.operand)
  : FinalAS.instr list
  =
  match op with
  | Add -> translate_add dest lhs rhs
  | Sub -> translate_sub dest lhs rhs
  | Mul -> translate_mul dest lhs rhs
  | Div -> translate_div dest lhs rhs
  | Mod -> translate_mod dest lhs rhs
;;

let rec instr_trans_helper (lst : AS.instr list) (acc : FinalAS.instr list)
  : FinalAS.instr list
  =
  match lst with
  | [] -> FinalAS.[ Ret; Unop { op = Pop; word_size = Q; src = Reg RBP } ] @ acc
  (* Epilogue, including Ret *)
  | Mov { dest; src } :: t -> instr_trans_helper t (translate_mov dest src @ acc)
  | Binop { op; dest; lhs; rhs } :: t ->
    instr_trans_helper t (translate_binop op dest lhs rhs @ acc)
  | Directive d :: t -> instr_trans_helper t ([ FinalAS.Directive d ] @ acc)
  | Comment c :: t -> instr_trans_helper t ([ FinalAS.Comment c ] @ acc)
;;

let instr_trans (lst : AS.instr list) : FinalAS.instr list =
  List.rev
    (instr_trans_helper
       lst
       FinalAS.(
         (* Prologue *)
         [ Binop { op = Mov; word_size = Q; src = Reg RSP; dest = Reg RBP }
         ; Unop { op = Push; word_size = Q; src = Reg RBP }
         ]))
;;

(* let%expect_test "identity: return 1;" =
  Temp.reset ();
  let assem_in = AS.[ Mov { dest = Reg EAX; src = Imm (Int32.of_int_trunc 1) } ] in
  let assem_out = instr_trans assem_in in
  let output_instr assem = Printf.printf "\t%s\n" (FinalAS.format assem) in
  output_instr (FinalAS.Directive ".function\tmain:");
  List.iter ~f:output_instr assem_out;
  output_instr (FinalAS.Directive ".ident\t\"15-411 L1 compiler\"");
  [%expect
    {|
       .function	main:
       pushq  %rbp
       movq %rsp, %rbp
       movl $1, %eax
       popq %rbp
       ret
       .ident	"15-411 L1 compiler"
     |}]
;; *)
