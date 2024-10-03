(* L1 Compiler
 * Converts from finalassem into liveness json
 * Parses the input in reverse
 * Follow the algorithm from recitation


 * Implementation: have 4 hashmaps

 NOTE: might need to create a succ_table graph as well.
 1. Get the maximum number of lines as line_count
 2. Keep track of the successor lines using succ_table (line to list of lines/hashtbl of lines)
 NOTE: May iterate a few times in the future here.
 3. For each line:
 3a. Parse each line to find what it uses and defines
 3b. Store into defs_table, uses_table OK
 3c. Find the liveout by referencing the livein_table (map from line to list of values)
 3d. Store into liveout_table
 3e. Find livein by creating hashtable to union (liveout - defs), then union uses
 3f. Store into livein_table
 3g. Store the mov in the mov_table

 4. For each line (front to back)
 4a. Update a json format to store the required values
 *)

open Core
module AS = Assem

(* Created modules to simplify functions *)
module Int32Set = Set.Make (Int32)
module Int32Table = Hashtbl.Make (Int32)

module OperandTable = Hashtbl.Make (struct
  type t = AS.operand [@@deriving compare, sexp, hash]
end)

module OperandSet = Set.Make (struct
  type t = AS.operand [@@deriving compare, sexp, hash]
end)

type line =
  { uses : AS.operand list
  ; defines : AS.operand list
  ; live_out : AS.operand list
  ; move : bool
  ; line_number : Int32.t
  }

(* Adds key/data pair to table and returns true if it is the first insertion
 TODO: update this function when considering loops/gotos/jumps
 - Add will not modify the table if there is an existing entry, but we may need to update it regularly *)
let add_to_table table ~key ~data =
  match Hashtbl.add table ~key ~data with
  | `Duplicate -> false
  | `Ok -> true
;;

(* Looks at succ_table for all successors of a line_number. 
    Unions the operandsets in all successors for all liveouts of a line number*)
let union_succ
  (succ_table : (Int32.t, Int32Set.t) Hashtbl.t)
  (livein_table : (Int32.t, OperandSet.t) Hashtbl.t)
  (line_number : Int32.t)
  =
  let all_succs_line =
    match Hashtbl.find succ_table line_number with
    | None -> Int32Set.empty
    | Some x -> x
  in
  let all_succs_set_list =
    Int32Set.to_list all_succs_line
    |> List.map ~f:(fun x ->
         match Hashtbl.find livein_table x with
         | None -> OperandSet.empty
         | Some y -> y)
  in
  OperandSet.union_list all_succs_set_list
;;

(* Adds an operand to a set, fails with Ref and ignores Immediate values *)
let add_to_set curr_set op =
  match op with
  | AS.Imm _ -> curr_set
  | AS.Ref _ -> failwith "not supposed to have ref in temp"
  | AS.Reg r -> OperandSet.add curr_set (AS.Reg r)
  | AS.Temp t -> OperandSet.add curr_set (AS.Temp t)
;;

(* Takes in line of instruction and line number. 
    Searches for successors, livein, liveout, uses, and defs given instruction. 
    Specifies mov given instruction *)
let process_line
  (line_in : AS.instr)
  (line_number : Int32.t)
  ((succ_table, livein_table, liveout_table, uses_table, defs_table, movs_table, ops_table) :
    (Int32.t, Int32Set.t) Hashtbl.t
    * (Int32.t, OperandSet.t) Hashtbl.t
    * (Int32.t, OperandSet.t) Hashtbl.t
    * (Int32.t, OperandSet.t) Hashtbl.t
    * (Int32.t, AS.operand) Hashtbl.t
    * (Int32.t, bool) Hashtbl.t
    * (AS.operand, unit) Hashtbl.t)
  =
  let used_values =
    match Hashtbl.find uses_table line_number with
    | None -> OperandSet.empty
    | Some x -> x
  in
  let live_outs = union_succ succ_table livein_table line_number in
  let curr_live_outs =
    match Hashtbl.find liveout_table line_number with
    | None -> OperandSet.empty
    | Some x -> x
  in
  let all_live_out = Set.union live_outs curr_live_outs in
  assert (add_to_table liveout_table ~key:line_number ~data:all_live_out);
  match line_in with
  | Binop { op; dest; lhs; rhs } ->
    assert (add_to_table ops_table ~key:dest ~data:() || true);
    assert (add_to_table ops_table ~key:lhs ~data:() || true);
    assert (add_to_table ops_table ~key:rhs ~data:() || true);
    let used_values_checked =
      match op with
      | AS.Div | AS.Mod ->
        let used_values_1 = add_to_set used_values (AS.Reg AS.EDX) in
        add_to_set used_values_1 (AS.Reg AS.EAX)
      | _ -> used_values
    in
    let add_lhs = add_to_set used_values_checked lhs in
    let add_rhs = add_to_set add_lhs rhs in
    assert (add_to_table uses_table ~key:line_number ~data:add_rhs);
    assert (add_to_table defs_table ~key:line_number ~data:dest);
    let live_in = OperandSet.diff all_live_out (OperandSet.of_list [ dest ]) in
    Hashtbl.set movs_table ~key:line_number ~data:false;
    add_to_table livein_table ~key:line_number ~data:(OperandSet.union live_in add_rhs)
  | Mov { dest; src } ->
    assert (add_to_table ops_table ~key:dest ~data:() || true);
    assert (add_to_table ops_table ~key:src ~data:() || true);
    let add_src = add_to_set used_values src in
    assert (add_to_table uses_table ~key:line_number ~data:add_src);
    assert (add_to_table defs_table ~key:line_number ~data:dest);
    let live_in = OperandSet.diff all_live_out (OperandSet.of_list [ dest ]) in
    Hashtbl.set movs_table ~key:line_number ~data:true;
    add_to_table livein_table ~key:line_number ~data:(OperandSet.union live_in add_src)
  | _ ->
    (* { uses = []; live_out = []; live_out = []; move = true; line_number } *)
    true
;;

(* Traverses from back to front, maps from source to successor.live_out
    Placeholder function until required to build successor table given jumps and conditionals *)
let build_succ_table
  (assem_list : AS.instr list)
  (succ_table : (Int32.t, Int32Set.t) Hashtbl.t)
  =
  let rec build_helper assem_list succ_table counter =
    match assem_list with
    | [] -> succ_table
    | _ :: t ->
      if Int32.is_positive counter
      then (
        let () =
          match Hashtbl.find succ_table counter with
          | Some curr_set ->
            assert (
              add_to_table
                succ_table
                ~key:counter
                ~data:(Int32Set.union curr_set (Int32Set.of_list [ Int32.succ counter ])))
          | None ->
            assert (
              add_to_table
                succ_table
                ~key:counter
                ~data:(Int32Set.of_list [ Int32.succ counter ]))
        in
        build_helper t succ_table (Int32.succ counter))
      else succ_table
  in
  build_helper assem_list succ_table (Int32.of_int_trunc 1)
;;

(* Given all the tables and lines, constructs the list in the form specified in line *)
let build_line_list
  list_len
  ((liveout_table, uses_table, defs_table, movs_table) :
    (Int32.t, OperandSet.t) Hashtbl.t
    * (Int32.t, OperandSet.t) Hashtbl.t
    * (Int32.t, AS.operand) Hashtbl.t
    * (Int32.t, bool) Hashtbl.t)
  =
  let rec build_helper list_len acc =
    match list_len with
    | n when Int32.( < ) n Int32.zero -> failwith "list_len not supposed to be negative"
    | n when Int32.( = ) n Int32.zero -> acc
    | n ->
      build_helper
        (Int32.pred list_len)
        ({ uses =
             OperandSet.to_list
               (match Hashtbl.find uses_table n with
                | None -> failwith "uses must have value"
                | Some x -> x)
         ; defines =
             [ (match Hashtbl.find defs_table n with
                | None -> failwith "defs must have value"
                | Some x -> x)
             ]
         ; live_out =
             OperandSet.to_list
               (match Hashtbl.find liveout_table n with
                | None -> failwith "liveout must have value"
                | Some x -> x)
         ; move =
             (match Hashtbl.find movs_table n with
              | None -> failwith "move must have value"
              | Some x -> x)
         ; line_number = n
         }
         :: acc)
  in
  build_helper list_len []
;;

(* Creates list of lines required for liveness analysis *)
let liveness (assem_list : AS.instr list) : line list * int =
  let succ_table =
    build_succ_table assem_list (Int32Table.create ~growth_allowed:true ~size:500 ())
  in
  let livein_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let liveout_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let uses_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let defs_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let movs_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let ops_table = OperandTable.create ~growth_allowed:true ~size:500 () in
  let rec process_helper list_len rev_list =
    match rev_list with
    | [] -> ()
    | h :: t ->
      assert (
        process_line
          h
          list_len
          ( succ_table
          , livein_table
          , liveout_table
          , uses_table
          , defs_table
          , movs_table
          , ops_table ));
      process_helper (Int32.pred list_len) t
  in
  process_helper (Int32.of_int_trunc (List.length assem_list)) (List.rev assem_list);
  ( build_line_list
      (Int32.of_int_trunc (List.length assem_list))
      (liveout_table, uses_table, defs_table, movs_table)
  , List.length (OperandTable.keys ops_table) )
;;

(* Helper functions to format output for testing *)
let format_op x = "\"" ^ AS.format_operand x ^ "\""
let format_op_list lst = "[" ^ String.concat ~sep:", " (List.map ~f:format_op lst) ^ "]"

let string_of_line { uses; defines; live_out; move; line_number } =
  "{\n\"Uses\": "
  ^ format_op_list uses
  ^ ",\n"
  ^ "\"Defines\": "
  ^ format_op_list defines
  ^ ",\n"
  ^ "\"Live_out\": "
  ^ format_op_list live_out
  ^ ",\n"
  ^ "\"Move\": "
  ^ (if move then "true" else "false")
  ^ ",\n"
  ^ "\"Line\": "
  ^ Int32.to_string line_number
  ^ ",\n},\n"
;;

let string_of_op_lst lst =
  "[" ^ String.concat ~sep:" " (List.map lst ~f:string_of_line) ^ "]"
;;

(* let%expect_test "test" =
   Temp.reset ();
   let lexbuf = Lexing.from_string "int main() {return 1;}" in
   let ast = C0_parser.program C0_lexer.initial lexbuf in
   let ir = Trans.translate ast in
   let assem_three = Intcodegen.int_code_gen ir in
   let live_lst = liveness assem_three in
   let output_instr_list instr_list =
     Printf.printf "\t%s\n" (string_of_op_lst instr_list)
   in
   output_instr_list live_lst;
   [%expect
     {|
       .function	main()
       %eax <-- $1
       .ident	"15-411 L1 reference compiler"
     |}]
 ;; *)

let%expect_test "Test parsing of commutative and associative into 3 assem" =
  Temp.reset ();
  let lexbuf = Lexing.from_string "int main() {return (5 + 3 - 6 * 3); }" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = Intcodegen.int_code_gen ir in
  let live_lst, len = liveness assem_three in
  let output_instr_list instr_list =
    Printf.printf "\t%s\n" (string_of_op_lst instr_list)
  in
  Printf.printf "hello %s" (string_of_int len);
  output_instr_list live_lst;
  [%expect
    {|
         [{
       "Uses": [],
       "Defines": ["%t3"],
       "Live_out": ["%t3"],
       "Move": true,
       "Line": 1,
       },
        {
       "Uses": [],
       "Defines": ["%t4"],
       "Live_out": ["%t3", "%t4"],
       "Move": true,
       "Line": 2,
       },
        {
       "Uses": ["%t3", "%t4"],
       "Defines": ["%t1"],
       "Live_out": ["%t1"],
       "Move": false,
       "Line": 3,
       },
        {
       "Uses": [],
       "Defines": ["%t5"],
       "Live_out": ["%t1", "%t5"],
       "Move": true,
       "Line": 4,
       },
        {
       "Uses": [],
       "Defines": ["%t6"],
       "Live_out": ["%t1", "%t5", "%t6"],
       "Move": true,
       "Line": 5,
       },
        {
       "Uses": ["%t5", "%t6"],
       "Defines": ["%t2"],
       "Live_out": ["%t1", "%t2"],
       "Move": false,
       "Line": 6,
       },
        {
       "Uses": ["%t1", "%t2"],
       "Defines": ["%eax"],
       "Live_out": [],
       "Move": false,
       "Line": 7,
       },
       ]
     |}]
;;
