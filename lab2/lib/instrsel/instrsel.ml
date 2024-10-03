(* L1 Compiler
 * Instruction selection. 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Converts 3-address assembly to 2-address assembly.
 *)
open Core
module AS = Assem
module ThreeAS = Threeaddrassem

let convert_op = AS.operand_of_three_addr_operand
let convert_cmp = AS.cmp_of_three_addr_cmp

(* Current rule: use an intermediate register if both are refs. *)
let translate_mov (dest : ThreeAS.operand) (src : ThreeAS.operand) : AS.instr list =
  match src, dest with
  | _, ThreeAS.Imm _ -> failwith "Destination of mov cannot be an immediate"
  | _ -> AS.[ Mov { src = convert_op src; dest = convert_op dest } ]
;;

(** Recall that all instructions need to be translated in reverse. 
    `d = s1 + s2` is converted to
      movl s1, %r10
      addl s2, %r10
      movl %r10, d
    *)

(** `d = s1 - s2` is converted to
      movl s1, %r10
      subl s2, %r10
      movl %r10, d
    *)

(** `d = r1 * r2` is converted to 
      movl r1, %r10
      imull r2, %r10
      movl %r10, d
*)

(**  If we have a binop `d = r1 @ r2 ` that is translated using the following 
    template:
      movl r1, %r10
      instr r2, %r10
      movl %r10, d
      then we can use the function below.
*)
let translate_simple_binop
  (dest : ThreeAS.operand)
  (lhs : ThreeAS.operand)
  (rhs : ThreeAS.operand)
  (op : AS.two_addr_op)
  : AS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of simple binop cannot be an immediate"
  | _ ->
    AS.
      [ Mov { src = Reg R10D; dest = convert_op dest }
      ; Binop { op; src = convert_op rhs; dest = Reg R10D }
      ; Mov { src = convert_op lhs; dest = Reg R10D }
      ]
;;

(** `d = r1 / r2` is converted to 

      movl r1, %eax
      cltd
      idivl   r2
      movl    %eax, d
    
*)
let translate_div (dest : ThreeAS.operand) (lhs : ThreeAS.operand) (rhs : ThreeAS.operand)
  : AS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of div cannot be an immediate"
  | _ ->
    AS.
      [ Mov { src = Reg EAX; dest = convert_op dest }
      ; Unop { op = IDiv; src = convert_op rhs; div_type = AS.Div }
      ; Nullop { op = Cltd }
      ; Mov { src = convert_op lhs; dest = Reg EAX }
      ]
;;

(** `d = r1 % r2` is converted to 

      movl r1, %eax
      cltd
      idivl   r2
      movl    %edx, d
    
*)
let translate_mod (dest : ThreeAS.operand) (lhs : ThreeAS.operand) (rhs : ThreeAS.operand)
  : AS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of mod cannot be an immediate"
  | _ ->
    AS.
      [ Mov { src = Reg EDX; dest = convert_op dest }
      ; Unop { op = IDiv; src = convert_op rhs; div_type = AS.Mod }
      ; Nullop { op = Cltd }
      ; Mov { src = convert_op lhs; dest = Reg EAX }
      ]
;;

(** `d = lhs << rhs` is converted to 

      movl rhs ecx % some test register
      test ecx ecx
      jl exn
      cmp 31 ecx
      jg exn
      movl lhs, %r10
      sal ecx, %r10
      movl %r10, d
      jmp end
      exn: 
      movl $0, r10d
      idivl r10d
      end:

      `d = lhs >> rhs` follows a similar conversion. Because they use the ECX
      register, this must be explicitly accounted for during register allocation
*)

let translate_shift
  (dest : ThreeAS.operand)
  (lhs : ThreeAS.operand)
  (rhs : ThreeAS.operand)
  (op : AS.two_addr_op)
  (label_number : int)
  : AS.instr list
  =
  match dest with
  | Imm _ -> failwith "Destination of simple binop cannot be an immediate"
  | _ ->
    let op_name =
      match op with
      | Sal -> "sal"
      | Sar -> "sar"
      | _ -> failwith "cannot call translate_shift on a non-shift op."
    in
    let label_end = Printf.sprintf "%s_end_%d" op_name label_number in
    let label_exn = Printf.sprintf "%s_exn_%d" op_name label_number in
    AS.
      [ Label label_end
      ; Unop { op = IDiv; src = Reg R10D; div_type = AS.Div }
      ; Mov { src = Imm Int32.zero; dest = Reg R10D }
      ; Label label_exn
      ; Jump { label = Label label_end }
      ; Mov { src = Reg R10D; dest = convert_op dest }
      ; Binop { op; src = Reg ECX; dest = Reg R10D }
      ; Mov { src = convert_op lhs; dest = Reg R10D }
      ; JumpC { cmp = Gt; label = Label label_exn }
      ; Cmp { lhs = Imm (Int32.of_int_exn 31); rhs = Reg ECX }
        (* immediate has to be the rhs operand.  *)
      ; JumpC { cmp = Lt; label = Label label_exn }
      ; Test { lhs = Reg ECX; rhs = Reg ECX }
      ; Mov { src = convert_op rhs; dest = Reg ECX }
      ]
;;

(**
    `lhs cmp rhs` should be translated to
    mov lhs r10d
    cmp r10d rhs
    *)
let translate_cmp (lhs : ThreeAS.operand) (rhs : ThreeAS.operand) : AS.instr list =
  AS.
    [ Cmp { lhs = Reg R10D; rhs = convert_op rhs }
    ; Mov { src = convert_op lhs; dest = Reg R10D }
    ]
;;

let translate_dir str = AS.Directive str
let translate_comment str = AS.Comment str
let translate_label str = AS.Label str
let translate_jump label = AS.Jump { label = convert_op label }

let translate_jumpc cmp label =
  AS.JumpC { cmp = convert_cmp cmp; label = convert_op label }
;;

let translate_binop
  (op : ThreeAS.operation)
  (dest : ThreeAS.operand)
  (lhs : ThreeAS.operand)
  (rhs : ThreeAS.operand)
  (label_number : int)
  : AS.instr list
  =
  match op with
  | ThreeAS.Add -> translate_simple_binop dest lhs rhs AS.Add
  | ThreeAS.Sub -> translate_simple_binop dest lhs rhs AS.Sub
  | ThreeAS.Mul -> translate_simple_binop dest lhs rhs AS.IMul
  | ThreeAS.Xor -> translate_simple_binop dest lhs rhs AS.Xor
  | ThreeAS.And -> translate_simple_binop dest lhs rhs AS.And
  | ThreeAS.Or -> translate_simple_binop dest lhs rhs AS.Or
  | ThreeAS.Div -> translate_div dest lhs rhs
  | ThreeAS.Mod -> translate_mod dest lhs rhs
  | ThreeAS.Sal -> translate_shift dest lhs rhs AS.Sal label_number
  | ThreeAS.Sar -> translate_shift dest lhs rhs AS.Sar label_number
;;

let instr_sel (lst : ThreeAS.instr list) : AS.instr list =
  let label_counter = ref 0 in
  let next () =
    incr label_counter;
    !label_counter
  in
  let rec instr_sel_helper (lst : ThreeAS.instr list) (acc : AS.instr list)
    : AS.instr list
    =
    let label_number = next () in
    match lst with
    | [] -> acc
    | ThreeAS.Mov { dest; src } :: t -> instr_sel_helper t (translate_mov dest src @ acc)
    | ThreeAS.Binop { op; dest; lhs; rhs } :: t ->
      instr_sel_helper t (translate_binop op dest lhs rhs label_number @ acc)
    | ThreeAS.Cmp { lhs; rhs } :: t -> instr_sel_helper t (translate_cmp lhs rhs @ acc)
    (* Epilogue, including Ret *)
    | ThreeAS.Ret { src } :: t ->
      instr_sel_helper
        t
        ([ AS.Ret; AS.Mov { src = convert_op src; dest = Reg EAX } ] @ acc)
    (* Directive, Comment, JumpC, Jump, Label are all the same *)
    | ThreeAS.Jump { label } :: t -> instr_sel_helper t (translate_jump label :: acc)
    | ThreeAS.JumpC { cmp; label } :: t ->
      instr_sel_helper t (translate_jumpc cmp label :: acc)
    | ThreeAS.Label str :: t -> instr_sel_helper t (translate_label str :: acc)
    | ThreeAS.Directive str :: t -> instr_sel_helper t (translate_dir str :: acc)
    | ThreeAS.Comment str :: t -> instr_sel_helper t (translate_comment str :: acc)
  in
  List.rev (instr_sel_helper lst [])
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
