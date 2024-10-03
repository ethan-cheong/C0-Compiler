(* L1 Compiler
 * Converts temps to refs on the stack 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Temps are assigned locations on the stack in order that they are seen.
 * Uses a hashmap to keep track of stack locations. 
 *)
open Core
module AS = Assem

(* Helper functions for managing hashtable containing temps*)

(** Adds a temp to the hashmap and returns the corresponding stack offset. 
    Temps should not be assigned more than once. *)
let add_temp_to_table
  (temp : Temp.t)
  (temp_table : (Temp.t, int32) Hashtbl_intf.Hashtbl.t)
  =
  let dest_offset = (Hashtbl.length temp_table + 1) * -4 |> Int32.of_int_trunc in
  Hashtbl.find_or_add temp_table temp ~default:(fun () -> dest_offset)
;;

(** Gets the corresponding stack offset of a temp in the hashmap. 
    Temps should not be referenced before they have been assigned to.
    However, this can still happen in code where temps are never accessed 
    because of a branch that can't be reached.
    In that case, we give these temps an offset of Int32.max_value since they 
    will never be accessed, so they are easily visible in assembly. *)
let ref_temp_from_table
  (temp : Temp.t)
  (temp_table : (Temp.t, int32) Hashtbl_intf.Hashtbl.t)
  =
  Hashtbl.find_or_add temp_table temp ~default:(fun () -> Int32.max_value)
;;

(** Replaces a mov instruction with the same instruction, but with any temps
    replaced by references to a location on the stack. 
    Requires: [dest] is not an immediate
              Neither [dest] nor [src] is a reference *)
let spill_temps_mov (dest : AS.operand) (src : AS.operand) temp_table : AS.instr =
  AS.(
    let dest_part =
      match dest with
      | Temp t ->
        let dest_offset = add_temp_to_table t temp_table in
        Ref { offset = dest_offset; reg = RSP }
      | Imm i ->
        failwith
          ((i |> Int32.to_string)
           ^ " is the destination, but dest should never be an immediate")
      | MAX_INT -> failwith "destination cannot be immediate (max int)"
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label _ -> failwith "None of the arguments in mov operands should be labels!"
    in
    let src_part =
      match src with
      | Temp t ->
        let src_offset = ref_temp_from_table t temp_table in
        Ref { offset = src_offset; reg = RSP }
      | Imm i -> Imm i
      | MAX_INT -> MAX_INT
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label _ -> failwith "None of the arguments in mov operands should be labels!"
    in
    Mov { dest = dest_part; src = src_part })
;;

(** Replaces a binop instruction with the same instruction, but with any temps 
    replaced by references to a location on the stack.
    Requires: [dest] is not an immediate
              None of [dest] or [src] are references or labels *)
let spill_temps_binop
  (op : AS.two_addr_op)
  (dest : AS.operand)
  (src : AS.operand)
  temp_table
  : AS.instr
  =
  AS.(
    let dest_part =
      match dest with
      | Temp t ->
        let dest_offset = add_temp_to_table t temp_table in
        Ref { offset = dest_offset; reg = RSP }
      | Imm i ->
        failwith
          ((i |> Int32.to_string)
           ^ " is the destination, but dest should never be an immediate")
      | MAX_INT -> failwith "destination cannot be immediate (max int)"
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The destination can never be a label " ^ l)
    in
    let src_part =
      match src with
      | Temp t ->
        let src_offset = ref_temp_from_table t temp_table in
        Ref { offset = src_offset; reg = RSP }
      | Imm i -> Imm i
      | MAX_INT -> MAX_INT
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The rhs cannot be a label " ^ l)
    in
    Binop { op; dest = dest_part; src = src_part })
;;

(** Replaces a unop instruction with the same instruction, but with any temps 
    replaced by references to a location on the stack.
    Requires: [src] is not an immediate or labels *)
let spill_temps_unop (op : AS.one_addr_op) (src : AS.operand) temp_table : AS.instr =
  AS.(
    let src_part =
      match src with
      | Temp t ->
        let src_offset = add_temp_to_table t temp_table in
        Ref { offset = src_offset; reg = RSP }
      | Imm i ->
        failwith
          ((i |> Int32.to_string)
           ^ " is the destination, but src should never be an immediate")
      | MAX_INT -> failwith "destination cannot be immediate (max int)"
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The destination can never be a label " ^ l)
    in
    Unop { op; src = src_part; div_type = NotDiv })
;;

(** Replaces a binop instruction with the same instruction, but with any temps 
    replaced by references to a location on the stack.
    Requires: [dest] is not an immediate
              None of [dest] or [src] are references or labels *)
let spill_temps_test (lhs : AS.operand) (rhs : AS.operand) temp_table : AS.instr =
  AS.(
    let lhs_part =
      match lhs with
      | Temp t ->
        let lhs_offset = add_temp_to_table t temp_table in
        Ref { offset = lhs_offset; reg = RSP }
      | Imm i -> Imm i
      | MAX_INT -> MAX_INT
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The destination can never be a label " ^ l)
    in
    let rhs_part =
      match rhs with
      | Temp t ->
        let rhs_offset = ref_temp_from_table t temp_table in
        Ref { offset = rhs_offset; reg = RSP }
      | Imm i -> Imm i
      | MAX_INT -> MAX_INT
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The rhs cannot be a label " ^ l)
    in
    Test { lhs = lhs_part; rhs = rhs_part })
;;

(** Replaces a Cmp instruction with the same instruction, but with any temps 
    replaced by references to a location on the stack.
    Requires: 
              None of [lhs] or [rhs] are references or labels *)
let spill_temps_cmp (lhs : AS.operand) (rhs : AS.operand) temp_table : AS.instr =
  AS.(
    let lhs_part =
      match lhs with
      | Temp t ->
        let lhs_offset = ref_temp_from_table t temp_table in
        Ref { offset = lhs_offset; reg = RSP }
      | Imm i -> Imm i
      | MAX_INT -> MAX_INT
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The lhs cannot be a label " ^ l)
    in
    let rhs_part =
      match rhs with
      | Temp t ->
        let rhs_offset = ref_temp_from_table t temp_table in
        Ref { offset = rhs_offset; reg = RSP }
      | Imm i -> Imm i
      | MAX_INT -> MAX_INT
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
      | Label l -> failwith ("The rhs cannot be a label " ^ l)
    in
    Cmp { lhs = lhs_part; rhs = rhs_part })
;;

let rec stack_spill_helper (lst : AS.instr list) (acc : AS.instr list) temp_table
  : AS.instr list
  =
  match lst with
  | [] -> acc
  | Mov { dest; src } :: t ->
    stack_spill_helper t (spill_temps_mov dest src temp_table :: acc) temp_table
  | Binop { op; dest; src } :: t ->
    stack_spill_helper t (spill_temps_binop op dest src temp_table :: acc) temp_table
  | Unop { op; src; _ } :: t ->
    stack_spill_helper t (spill_temps_unop op src temp_table :: acc) temp_table
  | Nullop { op } :: t -> stack_spill_helper t (Nullop { op } :: acc) temp_table
  | Test { lhs; rhs } :: t ->
    stack_spill_helper t (spill_temps_test lhs rhs temp_table :: acc) temp_table
  | Ret :: t -> stack_spill_helper t (Ret :: acc) temp_table
  | Cmp { lhs; rhs } :: t ->
    stack_spill_helper t (spill_temps_cmp lhs rhs temp_table :: acc) temp_table
  | JumpC { cmp; label } :: t ->
    stack_spill_helper t (JumpC { cmp; label } :: acc) temp_table
  | Jump { label } :: t -> stack_spill_helper t (Jump { label } :: acc) temp_table
  | Label l :: t -> stack_spill_helper t (Label l :: acc) temp_table
  | Directive d :: t -> stack_spill_helper t (Directive d :: acc) temp_table
  | Comment c :: t -> stack_spill_helper t (Comment c :: acc) temp_table
;;

let stack_spill (lst : AS.instr list) : AS.instr list =
  let temp_table = Hashtbl.create ~growth_allowed:true ~size:500 (module Temp) in
  List.rev (stack_spill_helper lst [] temp_table)
;;

(* let%expect_test "Simple main conversion" =
  Temp.reset ();
  let temp_arr = Array.init 6 ~f:(fun _ -> Temp.create ()) in
  let temp_arr = Array.concat [ Array.init 1 ~f:(fun _ -> Temp.create ()); temp_arr ] in
  let assem_in =
    AS.
      [ Mov { dest = Temp temp_arr.(1); src = Imm (Int32.of_int_trunc 3) }
      ; Mov { dest = Temp temp_arr.(3); src = Imm (Int32.of_int_trunc 0) }
      ; Mov { dest = Temp temp_arr.(4); src = Temp temp_arr.(1) }
      ; Binop
          { op = Sub
          ; dest = Temp temp_arr.(2)
          ; lhs = Temp temp_arr.(3)
          ; rhs = Temp temp_arr.(4)
          }
      ; Mov { dest = Temp temp_arr.(5); src = Temp temp_arr.(1) }
      ; Mov { dest = Temp temp_arr.(6); src = Imm (Int32.of_int_trunc 3) }
      ; Binop
          { op = Add; dest = Reg EAX; lhs = Temp temp_arr.(5); rhs = Temp temp_arr.(6) }
      ]
  in
  let assem_out = stack_spill assem_in in
  let output_instr instr = Printf.printf "\t%s\n" (AS.format instr) in
  output_instr (AS.Directive ".function\tmain()");
  List.iter ~f:output_instr assem_out;
  output_instr (AS.Directive ".ident\t\"15-411 L1 Twoassem compiler\"");
  [%expect
    {|
    .function	main()
    %t1 <-- $3
    %t3 <-- $0
    %t4 <-- %t1
    %t2 <-- %t3
    %t2 -= %t4
    %t5 <-- %t1
    %t6 <-- $3
    %eax <-- %t5
    %eax += %t6
    .ident	"15-411 L1 Twoassem compiler"
  |}]
;; *)
