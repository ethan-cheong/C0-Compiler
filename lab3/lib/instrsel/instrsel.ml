(* L1 Compiler
 * Instruction selection. 
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Converts 3-address assembly to 2-address assembly.
 *)
open Core
module AS = Assem
module ThreeAS = Threeaddrassem

let convert_op = function
  | ThreeAS.Imm i -> AS.Imm i (* Immediates are always 32 bits *)
  | ThreeAS.MAX_INT -> AS.MAX_INT
  | ThreeAS.Temp t -> AS.Temp t
;;

let convert_cmp = AS.cmp_of_three_addr_cmp

(* All functions are translated in reverse *)

(* Naively convert all movs for now. In codegen, we will deal with unique cases
   e.g. mov temp temp. *)
let translate_mov (dest : ThreeAS.operand) (src : ThreeAS.operand) : AS.instr list =
  match src, dest with
  | _, ThreeAS.Imm _ -> failwith "Destination of mov cannot be an immediate"
  | _ -> AS.[ Mov { src = convert_op src; dest = convert_op dest } ]
;;

(**  If we have a binop `d = r1 @ r2 ` that is translated using the following 
    template:
      movl r1, %r10
      instr r2, %r10
      movl %r10, d
      then we can use the function below.

    As of now, these are all double words.
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
    (* Destination is always a temp; for now, temps are always doubles *)
    let dest_size = AS.DOUBLE in
    let r10d = AS.Reg { reg = R10; size = dest_size } in
    AS.
      [ Mov { src = r10d; dest = convert_op dest }
      ; Binop { op; src = convert_op rhs; dest = r10d }
      ; Mov { src = convert_op lhs; dest = r10d }
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
    let eax = AS.Reg { reg = AX; size = DOUBLE } in
    AS.
      [ Mov { src = eax; dest = convert_op dest }
      ; Unop { op = IDiv; src = convert_op rhs; div_type = AS.Div }
      ; Nullop { op = Cltd }
      ; Mov { src = convert_op lhs; dest = eax }
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
    let eax = AS.Reg { reg = AX; size = DOUBLE } in
    let edx = AS.Reg { reg = DX; size = DOUBLE } in
    AS.
      [ Mov { src = edx; dest = convert_op dest }
      ; Unop { op = IDiv; src = convert_op rhs; div_type = AS.Mod }
      ; Nullop { op = Cltd }
      ; Mov { src = convert_op lhs; dest = eax }
      ]
;;

(** `d = lhs << rhs` is converted to 

      movl rhs ecx % some test register
      test ecx ecx
      jl exn
      cmp 31 ecx
      jg exn
      movl lhs, %e10d
      sal ecx, %e10d
      movl %e10d, d
      jmp end
      exn: 
      movl $0, e10d
      idivl r10d
      end:

      `d = lhs >> rhs` follows a similar conversion. Because they use the ECX
      register, this must be explicitly accounted for during register allocation.

      Since we are adding a label, we also need to pass in the caller name.
*)
let translate_shift
  (dest : ThreeAS.operand)
  (lhs : ThreeAS.operand)
  (rhs : ThreeAS.operand)
  (op : AS.two_addr_op)
  (label_number : int)
  (caller_name : string)
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
    let label_end = Printf.sprintf "%s_end_%d_%s" op_name label_number caller_name in
    let label_exn = Printf.sprintf "%s_exn_%d_%s" op_name label_number caller_name in
    let r10d = AS.Reg { reg = R10; size = DOUBLE } in
    let ecx = AS.Reg { reg = CX; size = DOUBLE } in
    AS.
      [ Label label_end
      ; Unop { op = IDiv; src = r10d; div_type = AS.Div }
      ; Mov { src = Imm Int32.zero; dest = r10d }
      ; Label label_exn
      ; Jmp label_end
      ; Mov { src = r10d; dest = convert_op dest }
      ; Binop { op; src = ecx; dest = r10d }
      ; Mov { src = convert_op lhs; dest = r10d }
      ; Jc { cmp = G; label = label_exn }
      ; Cmp { lhs = Imm (Int32.of_int_exn 31); rhs = ecx }
        (* immediate has to be the rhs operand.  *)
      ; Jc { cmp = L; label = label_exn }
      ; Test { lhs = ecx; rhs = ecx }
      ; Mov { src = convert_op rhs; dest = ecx }
        (* these should always be doubles anyway*)
      ]
;;

(**
    `lhs cmp rhs` should be translated to
    movl lhs r10d
    cmp r10d rhs
    *)
let translate_cmp (lhs : ThreeAS.operand) (rhs : ThreeAS.operand) : AS.instr list =
  (* We only compare doubles (no register to register compares) *)
  let r10d = AS.Reg { reg = R10; size = DOUBLE } in
  AS.
    [ Cmp { lhs = r10d; rhs = convert_op rhs }
    ; Mov { src = convert_op lhs; dest = r10d }
    ]
;;

(* Translations of directions, comments, labels, jumps, and conditional jumps 
   involve translating from the 3 address assembly to the 2 address assembly equivalent *)
let translate_dir str = AS.Directive str
let translate_comment str = AS.Comment str
let translate_label str = AS.Label str
let translate_jump label = AS.Jmp label
let translate_jumpc cmp label = AS.Jc { cmp = convert_cmp cmp; label }

let translate_return src =
  let dest_size = AS.DOUBLE in
  (* TODO: In future labs, get the correct dest size from the temp *)
  let ax = AS.Reg { reg = AX; size = dest_size } in
  AS.[ Ret; Mov { src = convert_op src; dest = ax } ]
;;

(* We do the full translation of call in stackspill, after regalloc. *)
let translate_call dest ident args assign_res =
  (* TODO: Change the destination size depending on what is returned *)
  if assign_res
  then (
    let dest_size = AS.DOUBLE in
    AS.
      [ Mov { dest = convert_op dest; src = Reg { reg = AX; size = dest_size } }
      ; Call { ident; args = List.map ~f:convert_op args }
      ])
  else AS.[ Call { ident; args = List.map ~f:convert_op args } ]
;;

(* We propagate caller_name as translate_shift needs it. *)
let translate_binop
  (op : ThreeAS.operation)
  (dest : ThreeAS.operand)
  (lhs : ThreeAS.operand)
  (rhs : ThreeAS.operand)
  (label_number : int)
  caller_name
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
  | ThreeAS.Sal -> translate_shift dest lhs rhs AS.Sal label_number caller_name
  | ThreeAS.Sar -> translate_shift dest lhs rhs AS.Sar label_number caller_name
;;

let translate_func ~only_main (func : ThreeAS.func) : AS.func =
  let signature, body = func in
  let args = List.map signature.args ~f:(fun arg -> convert_op arg) in
  let caller_name = signature.ident in
  let label_counter = ref 0 in
  let next () =
    incr label_counter;
    !label_counter
  in
  let rec translate_func_helper (lst : ThreeAS.instr list) (acc : AS.instr list)
    : AS.instr list
    =
    let label_number = next () in
    match lst with
    | [] -> List.rev acc
    | ThreeAS.Mov { dest; src } :: t ->
      translate_func_helper t (translate_mov dest src @ acc)
    | ThreeAS.Binop { op; dest; lhs; rhs } :: t ->
      translate_func_helper
        t
        (translate_binop op dest lhs rhs label_number caller_name @ acc)
    | ThreeAS.Cmp { lhs; rhs } :: t ->
      translate_func_helper t (translate_cmp lhs rhs @ acc)
    | ThreeAS.CallF { dest; ident; args; assign_res } :: t ->
      translate_func_helper t (translate_call dest ident args assign_res @ acc)
    (* Epilogue, including Ret *)
    | ThreeAS.Ret { src } :: t -> translate_func_helper t (translate_return src @ acc)
    (* Directive, Comment, JumpC, Jump, Label are all the same *)
    | ThreeAS.Jump label :: t -> translate_func_helper t (translate_jump label :: acc)
    | ThreeAS.JumpC { cmp; label } :: t ->
      translate_func_helper t (translate_jumpc cmp label :: acc)
    | ThreeAS.Label str :: t -> translate_func_helper t (translate_label str :: acc)
    | ThreeAS.Directive str :: t -> translate_func_helper t (translate_dir str :: acc)
    | ThreeAS.Comment str :: t -> translate_func_helper t (translate_comment str :: acc)
  in
  (* Short-circuit if only_main is true (l1 or l2 test file) *)
  match only_main with
  | true ->
    let translated_body = translate_func_helper body [] in
    ( AS.
        { label = signature.ident
        ; args
        ; tail_rec = signature.tail_rec
        ; regalloc = false
        ; num_temps = signature.num_temps
        }
    , translated_body )
  | false ->
    let args_to_not_spill = Callclobber.non_call_clobbered_args signature.args body in
    let map_index_to_operand i : AS.operand =
      if i = 0
      then Reg { reg = DI; size = DOUBLE }
      else if i = 1
      then Reg { reg = SI; size = DOUBLE }
      else if i = 2
      then Reg { reg = DX; size = DOUBLE }
      else if i = 3
      then Reg { reg = CX; size = DOUBLE }
      else if i = 4
      then Reg { reg = R8; size = DOUBLE }
      else if i = 5
      then Reg { reg = R9; size = DOUBLE }
      else (
        let offset = (i - 5) * 8 in
        (* Any temps will be located at stack_offset above where they should be, 
         since we decrement the stack by stack offset immediately upon 
         entering the function. 
         When we enter stackspill, we have to add stack_offset to all 
         stack refs. *)
        Stack_ref { offset = Int32.(of_int_exn offset); size = QUAD })
    in
    (* Move registers into the appropriate argument spots. 
     Only call clobbered registers require this.
     For non-call clobbered registers, replace all their occurences with map_index_to_operand.
  *)
    let prologue =
      List.rev_filter_mapi args ~f:(fun i arg ->
        let temp =
          match arg with
          | Temp t -> t
          | _ -> failwith "ThreeAS.args cannot contain temps"
        in
        match Hashtbl.mem args_to_not_spill temp with
        (* Do not spill this arg. *)
        | true -> None
        (* Spill this arg *)
        | false -> Some (AS.Mov { dest = Temp temp; src = map_index_to_operand i }))
    in
    let translated_body = translate_func_helper body prologue in
    let replace_non_call_clobbered_arg (operand : AS.operand) =
      match operand with
      | Assem.Temp t ->
        (match Hashtbl.find args_to_not_spill t with
         | Some arg_index -> map_index_to_operand arg_index
         | None -> operand)
      | _ -> operand
    in
    (* Replace all non-call-clobbered-args in the function body.*)
    let replaced_body =
      List.map translated_body ~f:(fun instr ->
        match instr with
        | Unop u -> AS.Unop { u with src = replace_non_call_clobbered_arg u.src }
        | Binop b ->
          Binop
            { b with
              src = replace_non_call_clobbered_arg b.src
            ; dest = replace_non_call_clobbered_arg b.dest
            }
        | Mov { dest; src } ->
          Mov
            { src = replace_non_call_clobbered_arg src
            ; dest = replace_non_call_clobbered_arg dest
            }
        | Test { lhs; rhs } ->
          Test
            { lhs = replace_non_call_clobbered_arg lhs
            ; rhs = replace_non_call_clobbered_arg rhs
            }
        | Cmp { lhs; rhs } ->
          Cmp
            { lhs = replace_non_call_clobbered_arg lhs
            ; rhs = replace_non_call_clobbered_arg rhs
            }
        | Call { ident; args } ->
          Call { ident; args = List.map ~f:replace_non_call_clobbered_arg args }
        | _ -> instr)
    in
    (* Replace all non-call-clobbered args in the arglist to indicate to regalloc
       not to allocate them *)
    let replaced_args =
      List.mapi args ~f:(fun i arg ->
        let temp =
          match arg with
          | Temp t -> t
          | _ -> failwith "ThreeAS.args cannot contain temps"
        in
        match Hashtbl.mem args_to_not_spill temp with
        (* Arg has to be replaced with its reg / temp *)
        | true -> map_index_to_operand i
        (* Spill this arg *)
        | false -> arg)
    in
    ( AS.
        { label = signature.ident
        ; args = replaced_args
        ; tail_rec = signature.tail_rec
        ; regalloc = false
        ; num_temps = signature.num_temps
        }
    , replaced_body )
;;

let instr_sel (program : ThreeAS.program) ~only_main =
  (* We apply this function below to each func in the program *)
  List.map program ~f:(fun func -> translate_func func ~only_main)
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
