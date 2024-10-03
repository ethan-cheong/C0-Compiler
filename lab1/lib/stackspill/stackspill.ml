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
  match Hashtbl.add temp_table ~key:temp ~data:dest_offset with
  | `Ok -> dest_offset
  | `Duplicate -> failwith "Attempted to write to temp twice"
;;

let get_option = function
  | Some x -> x
  | _ -> failwith "Referenced temp from table before it had been added"
;;

(** Gets the corresponding stack offset of a temp in the hashmap. 
    Temps should not be referenced before they have been assigned to. *)
let ref_temp_from_table
  (temp : Temp.t)
  (temp_table : (Temp.t, int32) Hashtbl_intf.Hashtbl.t)
  =
  Hashtbl.find temp_table temp |> get_option
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
        Ref { offset = dest_offset; reg = RBP }
      | Imm i ->
        failwith
          ((i |> Int32.to_string)
           ^ " is the destination, but dest should never be an immediate")
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
    in
    let src_part =
      match src with
      | Temp t ->
        let src_offset = ref_temp_from_table t temp_table in
        Ref { offset = src_offset; reg = RBP }
      | Imm i -> Imm i
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
    in
    Mov { dest = dest_part; src = src_part })
;;

(** Replaces a binop instruction with the same instruction, but with any temps 
    replaced by references to a location on the stack.
    Requires: [dest] is not an immediate
              None of [dest], [lhs] or [rhs] are references *)
let spill_temps_binop
  (op : AS.operation)
  (dest : AS.operand)
  (lhs : AS.operand)
  (rhs : AS.operand)
  temp_table
  : AS.instr
  =
  AS.(
    let dest_part =
      match dest with
      | Temp t ->
        let dest_offset = add_temp_to_table t temp_table in
        Ref { offset = dest_offset; reg = RBP }
      | Imm i ->
        failwith
          ((i |> Int32.to_string)
           ^ " is the destination, but dest should never be an immediate")
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
    in
    let lhs_part =
      match lhs with
      | Temp t ->
        let lhs_offset = ref_temp_from_table t temp_table in
        Ref { offset = lhs_offset; reg = RBP }
      | Imm i -> Imm i
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
    in
    let rhs_part =
      match rhs with
      | Temp t ->
        let rhs_offset = ref_temp_from_table t temp_table in
        Ref { offset = rhs_offset; reg = RBP }
      | Imm i -> Imm i
      | Reg r -> Reg r
      | Ref _ ->
        failwith "Abstract assembly should not contain references before stack spilling"
    in
    Binop { op; dest = dest_part; lhs = lhs_part; rhs = rhs_part })
;;

let rec stack_spill_helper (lst : AS.instr list) (acc : AS.instr list) temp_table
  : AS.instr list
  =
  match lst with
  | [] -> acc
  | Mov { dest; src } :: t ->
    stack_spill_helper t (spill_temps_mov dest src temp_table :: acc) temp_table
  | Binop { op; dest; lhs; rhs } :: t ->
    stack_spill_helper t (spill_temps_binop op dest lhs rhs temp_table :: acc) temp_table
  | _ :: t -> stack_spill_helper t acc temp_table
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
