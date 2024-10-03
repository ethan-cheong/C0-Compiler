(* L1 Compiler
 * Converts temps to refs on the stack 
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Temps are assigned locations on the stack in order that they are seen.
 * Uses a hashmap to keep track of stack locations. 
 *)
open Core
module AS = Assem

(** [add_callee_saved_reg reg_counter operand] will add operand to the reg_counter 
    hash table if it is a callee-saved register. We use this to determine how 
    much stack space we need for the function. *)
let add_callee_saved_reg ~reg_counter operand =
  match operand with
  (* Count the number of callee-saved registers used *)
  | AS.Reg { reg; _ } ->
    let r =
      match reg with
      | BX -> 0
      | BP -> 1
      | R12 -> 2
      | R13 -> 3
      | R14 -> 4
      | R15 -> 5
      | _ -> -1
    in
    if r >= 0 then Hashtbl.set reg_counter ~key:r ~data:reg
  | _ -> ()
;;

(** [add_temp temp_counter operand] will add a temp to the temp_counter hash 
    table. *)
let add_temp ~temp_counter operand =
  match operand with
  | AS.Temp t -> Hashtbl.set temp_counter ~key:t ~data:()
  | _ -> ()
;;

(** [calculate_offsets body] returns a tuple [(stack_offset, reg_counter)].

    [stack_offset] is the required stack offset for our function.
    [reg_counter] is a hashtbl containing the callee-saved registers.
    *)
let calculate_offsets (body : AS.instr list) =
  let temp_counter = Hashtbl.create ~growth_allowed:true ~size:500 (module Temp) in
  let reg_counter = Hashtbl.create ~growth_allowed:false ~size:10 (module Int) in
  let extract_temps_and_regs (instr : AS.instr) =
    match instr with
    | Unop { src; _ } ->
      add_temp ~temp_counter src;
      add_callee_saved_reg ~reg_counter src
    | Binop { src; dest; _ } | Mov { dest; src } ->
      add_temp ~temp_counter src;
      add_callee_saved_reg ~reg_counter src;
      add_temp ~temp_counter dest;
      add_callee_saved_reg ~reg_counter dest
    | Test { lhs; rhs } | Cmp { lhs; rhs } ->
      add_temp ~temp_counter lhs;
      add_callee_saved_reg ~reg_counter lhs;
      add_temp ~temp_counter rhs;
      add_callee_saved_reg ~reg_counter rhs
    | _ -> ()
  in
  List.iter body ~f:extract_temps_and_regs;
  let stack_offset =
    Int32.of_int_exn
      (* Save all args in registers, callee-saved registers and temps to stack. *)
      ((Hashtbl.length temp_counter + Hashtbl.length reg_counter) * 8)
  in
  stack_offset, reg_counter
;;

(** Runs stack spilling for a given function body.
   Params: [body] is the function body
           [temp_table] is a global temp table to hold temps and stack offsets. 
           [stack_offset] is the required stack offset to store arguments, 
           callee-saved registers and temps
           [reg_counter] is the set of callee-saved registers (as a hashtbl)
           [can_use_red_zone] is true iff the function can use the red zone *)
let stack_spill_func
  (body : AS.instr list)
  temp_table
  stack_offset
  reg_counter
  can_use_red_zone
  : AS.instr list
  =
  (* Helper functions for managing hashtable containing temps *)
  (* Adds a temp to the hashmap and returns the corresponding stack offset. 
        Temps should not be assigned more than once. *)
  let add_temp_to_table (temp : Temp.t) =
    (* If tail recursive, use the "red zone". *)
    let dest_offset =
      if can_use_red_zone
      then
        (Hashtbl.length temp_table + Hashtbl.length reg_counter + 1) * -8
        |> Int32.of_int_trunc
      else
        (* 0(rsp), ..., 5(rsp) are used to store any callee saved registers. *)
        (* Temps in function calls start from the offset AFTER callee-saved registers. *)
        (Hashtbl.length temp_table + Hashtbl.length reg_counter) * 8 |> Int32.of_int_trunc
    in
    Hashtbl.find_or_add temp_table temp ~default:(fun () -> dest_offset)
  in
  (* Gets the corresponding stack offset of a temp in the hashmap. 
      Temps should not be referenced before they have been assigned to.
      However, this can still happen in code where temps are never accessed 
      because of a branch that can't be reached.
      In that case, we give these temps an offset of Int32.max_value since they 
      will never be accessed, so they are easily visible in assembly. *)
  let ref_temp_from_table (temp : Temp.t) =
    Hashtbl.find_or_add temp_table temp ~default:(fun () -> Int32.max_value)
  in
  (* Replaces a mov instruction with a list of instructions in reverse order.
      mov x t:
        push x 
      
      mov t x:
        mov offset(rsp) x 
      
      mov t1 t2:
        mov offset(rsp) r10d
        push r10d
      *)
  let spill_temps_mov (dest : AS.operand) (src : AS.operand) : AS.instr =
    AS.(
      let dest_part =
        match dest with
        | Temp t ->
          let dest_offset = add_temp_to_table t in
          Stack_ref { offset = dest_offset; size = QUAD }
        | _ -> dest
      in
      let src_part =
        match src with
        | Temp t ->
          let src_offset = ref_temp_from_table t in
          Stack_ref { offset = src_offset; size = QUAD }
        | _ -> src
      in
      AS.Mov { dest = dest_part; src = src_part })
  in
  (* Replaces a binop with the same instruction, but any temps are replaced with
    stack offsets.
    Because of instruction selection, we know that temps can only be in the src
    argument.
    We need to move the temp into a scratch register
    addl t1 -> eax 

    movq offset(rsp), r10
    addl r10d eax
    *)
  let spill_temps_binop binop : AS.instr =
    match binop with
    | AS.Binop { op; src; dest } ->
      (match src with
       | Temp t ->
         (* In a binop, the size is always a DOUBLE word. *)
         AS.Binop
           { src = Stack_ref { offset = ref_temp_from_table t; size = DOUBLE }; dest; op }
       | _ -> binop)
    | _ -> failwith "spill_temps_binop called on a non-binop"
  in
  (* Replaces a Cmp instruction with a cmp, but with the temp replaced.

    cmp lhs t1 becomes
      cmp offset(t1) r10d

    Because of instruction selection, we know that Temps can only be generated
    on the rhs.
    *)
  let spill_temps_unop unop : AS.instr =
    match unop with
    | AS.Unop { op; src; div_type } ->
      (match op with
       | IDiv ->
         (match src with
          | Temp t ->
            (* Size has to be a quad (we can't access offset(%esp)! ). *)
            AS.Unop
              { op
              ; src = Stack_ref { offset = ref_temp_from_table t; size = QUAD }
              ; div_type
              }
          | _ -> unop)
       | _ -> failwith "pop and push shouldn't be in code yet")
    | _ -> failwith "non-unop provided to spill temps unop"
  in
  let spill_temps_cmp (lhs : AS.operand) (rhs : AS.operand) =
    let open AS in
    match lhs, rhs with
    | Temp _, _ ->
      failwith "A temp was on the RHS of cmp in stackspilling; something went wrong"
    (* Use the size stored in t otherwise. *)
    | _, Temp t ->
      Cmp { lhs; rhs = Stack_ref { offset = ref_temp_from_table t; size = DOUBLE } }
    | _ -> Cmp { lhs; rhs }
  in
  let spill_temps_ret () =
    let epilogue =
      if can_use_red_zone || Int32.(stack_offset = zero)
      then AS.[ Ret ]
      else
        AS.
          [ Ret
          ; Binop
              { op = Add; src = Imm stack_offset; dest = Reg { reg = SP; size = QUAD } }
          ]
    in
    (* Restore all callee saved registers *)
    let restore_registers =
      Hashtbl.fold reg_counter ~init:[] ~f:(fun ~key:_ ~data:r acc ->
        AS.Mov
          { src =
              Stack_ref { size = QUAD; offset = Int32.of_int_exn (List.length acc * 8) }
          ; dest = Reg { reg = r; size = QUAD }
          }
        :: acc)
    in
    epilogue @ restore_registers
  in
  (* Translate a Call instruction. *)
  let translate_call (call : AS.instr) =
    match call with
    | Call { ident; args } ->
      let map_index_to_operand i : AS.operand =
        let arg_size i = List.nth_exn args i |> AS.size_of_operand in
        if i = 0
        then Reg { reg = DI; size = arg_size i }
        else if i = 1
        then Reg { reg = SI; size = arg_size i }
        else if i = 2
        then Reg { reg = DX; size = arg_size i }
        else if i = 3
        then Reg { reg = CX; size = arg_size i }
        else if i = 4
        then Reg { reg = R8; size = arg_size i }
        else if i = 5
        then Reg { reg = R9; size = arg_size i }
        else (
          let offset = (i - 6) * 8 in
          Stack_ref { offset = Int32.of_int_exn offset; size = QUAD })
      in
      let number_of_args = List.length args in
      let stack_decr =
        (* The amount we decrement the stack by *)
        if number_of_args <= 6
        then Int32.zero
        else Int32.of_int_exn ((number_of_args - 6) * 8)
      in
      (* Adjust the decrement to be 0 mod 16 if necessary. The stack is aligned
       8 mod 16 at function entry; hence, if the stack offset + stack decr is 
        0 mod 16, it has to be increased by 8. *)
      let stack_decr =
        if Int32.((stack_offset + stack_decr) % of_int_exn 16 = zero)
        then Int32.(stack_decr + of_int_exn 8)
        else stack_decr
      in
      let rsp = AS.Reg { reg = SP; size = QUAD } in
      AS.
        [ Binop { src = Imm stack_decr; op = Add; dest = rsp }
        ; Call { ident; args = [] }
        ]
      (* Produces a list with the ordering [max_arg, ..., 0]. Should be reversed
         since we are doing the usual reverse accumulator trick. *)
      (* TODO: don't use @, do some recursive appending *)
      @ List.rev_mapi args ~f:(fun i arg ->
          (* Notice that args are all temps now. We need to convert these to regs. *)
          match arg with
          | Temp t ->
            AS.Mov
              { dest = map_index_to_operand i
              ; src =
                  Stack_ref
                    { offset = Int32.(ref_temp_from_table t + stack_decr); size = QUAD }
              }
          | _ -> AS.Mov { dest = map_index_to_operand i; src = arg })
      @ [ Binop { src = Imm stack_decr; op = Sub; dest = rsp } ]
    | _ -> failwith "translate call called on a non-call..."
  in
  let rec stack_spill_func_helper (lst : AS.instr list) (acc : AS.instr list)
    : AS.instr list
    =
    match lst with
    | [] -> acc
    | Mov { dest; src } :: t -> stack_spill_func_helper t (spill_temps_mov dest src :: acc)
    | Cmp { lhs; rhs } :: t -> stack_spill_func_helper t (spill_temps_cmp lhs rhs :: acc)
    | Binop h :: t -> stack_spill_func_helper t (spill_temps_binop (Binop h) :: acc)
    | Unop h :: t -> stack_spill_func_helper t (spill_temps_unop (Unop h) :: acc)
    (* Any instructions that don't involve temps * are preserved *)
    | Call h :: t -> stack_spill_func_helper t (translate_call (Call h) @ acc)
    | Ret :: t -> stack_spill_func_helper t (spill_temps_ret () @ acc) (* epilogue *)
    | instr :: t -> stack_spill_func_helper t (instr :: acc)
  in
  (* Decrement stack pointer at function entry, unless using the red zone, 
     or if the stack offset is zero *)
  let move_stack_section =
    if can_use_red_zone || Int32.(stack_offset = zero)
    then []
    else
      [ AS.Binop
          { op = Sub; src = Imm stack_offset; dest = Reg { reg = SP; size = QUAD } }
      ]
  in
  let prologue =
    (* Save all callee-saved registers*)
    Hashtbl.fold reg_counter ~init:[] ~f:(fun ~key:_ ~data:r acc ->
      AS.Mov
        { src = Reg { reg = r; size = QUAD }
        ; dest =
            Stack_ref
              { size = QUAD
              ; offset =
                  (if can_use_red_zone
                   then Int32.of_int_exn ((List.length acc + 1) * -8)
                   else Int32.of_int_exn (List.length acc * 8))
              }
        }
      :: acc)
    @ move_stack_section
  in
  List.rev (stack_spill_func_helper body prologue)
;;

(** [adjust_stack_offsets lst adj] increments the stack offsets of instructions 
    of the form 
      mov i($rsp) dest 
    to
      mov (i+adj)($rsp) dest
    
    In instruction selection, we explicitly got the position of args 7+ on the 
    stack.
    Now that we decrement the stack pointer on function entry, these positions
    have to be incremented.
    *)
let adjust_stack_offsets (lst : AS.instr list) (adj : Int32.t) : AS.instr list =
  (* Helper function for adjust_stack_offsets*)
  let adjust_ref = function
    | AS.Stack_ref { offset; size } ->
      AS.Stack_ref { offset = Int32.(offset + adj); size }
    | op -> op
  in
  List.map lst ~f:(fun instr ->
    match instr with
    | Mov { src; dest } -> AS.Mov { src = adjust_ref src; dest = adjust_ref dest }
    | Unop u -> Unop { u with src = adjust_ref u.src }
    | Binop b -> Binop { b with src = adjust_ref b.src; dest = adjust_ref b.dest }
    | Test t -> Test { lhs = adjust_ref t.lhs; rhs = adjust_ref t.rhs }
    | Cmp c -> Cmp { lhs = adjust_ref c.lhs; rhs = adjust_ref c.rhs }
    | Call c -> Call { c with args = List.map c.args ~f:adjust_ref }
    | _ -> instr)
;;

let stack_spill (lst : AS.func list) ~only_main : AS.func list =
  (* Global Hashtbl for temps*)
  let temp_table = Hashtbl.create ~growth_allowed:true ~size:500 (module Temp) in
  let stack_spill_helper (func : AS.func) temp_table =
    match only_main with
    | true ->
      let signature, body = func in
      let (stack_offset : Int32.t), reg_counter = calculate_offsets body in
      let translated_body =
        stack_spill_func body temp_table stack_offset reg_counter false
      in
      signature, translated_body
    | false ->
      let signature, body = func in
      let (stack_offset : Int32.t), reg_counter = calculate_offsets body in
      let adjusted_body = adjust_stack_offsets body stack_offset in
      (* If a function was regalloced, it cannot use the red zone. Otherwise, 
         it can use the red zone if it was previously marked as tail-recursive
         in translation, and also uses less than 128 args. *)
      let can_use_red_zone =
        (not signature.regalloc)
        && Int32.(stack_offset <= Int32.of_int_exn 128)
        && signature.tail_rec
      in
      let translated_body =
        stack_spill_func
          adjusted_body
          temp_table
          stack_offset
          reg_counter
          can_use_red_zone
      in
      Hashtbl.clear temp_table;
      signature, translated_body
  in
  List.map lst ~f:(fun func -> stack_spill_helper func temp_table)
;;
