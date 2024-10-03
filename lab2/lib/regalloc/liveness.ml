(* L1 Compiler
 * Converts from finalassem into liveness json
 * Parses the input in reverse
 * Follow the algorithm from recitation
 * Implementation: Read the readme.md for documentation
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

(* Adds a value to an operand set *)
let add_to_set curr_set op =
  match op with
  | AS.Imm _ | AS.Label _ | AS.MAX_INT -> curr_set
  | AS.Ref _ -> failwith "not supposed to have ref in temp"
  | AS.Reg r -> OperandSet.add curr_set (AS.Reg r)
  | AS.Temp t -> OperandSet.add curr_set (AS.Temp t)
;;

(* Adds a value to the table *)
let add_to_table table ~key ~data =
  match Hashtbl.add table ~key ~data with
  | `Duplicate -> false
  | `Ok -> true
;;

(* A function that constructs a function for pre-processing
   Takes in the required tables
   Returns a function that can take in a line number and line for pre-processing *)
let create_preproc_fn
  ~(uses_table : OperandSet.t Int32Table.t)
  ~(defs_table : AS.operand Int32Table.t)
  ~(movs_table : bool Int32Table.t)
  ~(jump_table : (String.t, Int32.t) Hashtbl.t)
  line_no
  instr
  =
  let int32_line = Int32.of_int_trunc line_no in
  let used_values =
    match Hashtbl.find uses_table int32_line with
    | None -> OperandSet.empty
    | Some x -> x
  in
  match instr with
  | AS.Binop { src; dest; _ } ->
    let add_src = add_to_set used_values src in
    assert (add_to_table uses_table ~key:int32_line ~data:add_src);
    assert (add_to_table defs_table ~key:int32_line ~data:dest);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Unop { op; src; div_type } ->
    (match op with
     | AS.Pop | AS.Push -> Hashtbl.set movs_table ~key:int32_line ~data:false
     | AS.IDiv ->
       let dest =
         match div_type with
         | AS.Div -> AS.Reg AS.EAX
         | AS.Mod -> AS.Reg AS.EDX
         | _ -> failwith "div type for unop must only be div or mod"
       in
       let add_edx = add_to_set used_values (AS.Reg AS.EDX) in
       let add_eax = add_to_set add_edx (AS.Reg AS.EAX) in
       let add_src = add_to_set add_eax src in
       assert (add_to_table uses_table ~key:int32_line ~data:add_src);
       assert (add_to_table defs_table ~key:int32_line ~data:dest);
       Hashtbl.set movs_table ~key:int32_line ~data:false)
  | AS.Nullop { op } ->
    (* Treat nullop as using eax to define edx *)
    (match op with
     | AS.Cltd ->
       let used_eax = AS.Reg AS.EAX in
       let def_edx = AS.Reg AS.EDX in
       let add_eax = add_to_set used_values used_eax in
       assert (add_to_table uses_table ~key:int32_line ~data:add_eax);
       assert (add_to_table defs_table ~key:int32_line ~data:def_edx);
       Hashtbl.set movs_table ~key:int32_line ~data:false)
  | AS.Cmp { lhs; rhs } ->
    let add_lhs = add_to_set used_values lhs in
    let add_rhs = add_to_set add_lhs rhs in
    assert (add_to_table uses_table ~key:int32_line ~data:add_rhs);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Mov { dest; src } ->
    let add_src = add_to_set used_values src in
    assert (add_to_table uses_table ~key:int32_line ~data:add_src);
    assert (add_to_table defs_table ~key:int32_line ~data:dest);
    Hashtbl.set movs_table ~key:int32_line ~data:true
  | AS.Directive _ | AS.Comment _ -> Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Label label ->
    assert (add_to_table jump_table ~key:label ~data:int32_line);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Jump { label } ->
    (* Jumps to the label *)
    (match label with
     | AS.Label _ -> Hashtbl.set movs_table ~key:int32_line ~data:false
     | _ -> failwith "AS Jump should only contain a label")
  | AS.JumpC { label; _ } ->
    (match label with
     | AS.Label _ -> Hashtbl.set movs_table ~key:int32_line ~data:false
     | _ -> failwith "AS JumpC should only contain a label")
    (* Will not add to operands here, since any return should already have been pre-defined
    Hashtbl.set movs_table ~key:int32_line ~data:false;
    let add_src = add_to_set used_values src in
    assert (add_to_table uses_table ~key:int32_line ~data:add_src) *)
  | AS.Ret -> Hashtbl.set movs_table ~key:int32_line ~data:false
  (* Ret not supposed to use or define anything *)
  | AS.Test { lhs; rhs } ->
    let add_lhs = add_to_set used_values lhs in
    let add_rhs = add_to_set add_lhs rhs in
    assert (add_to_table uses_table ~key:int32_line ~data:add_rhs);
    Hashtbl.set movs_table ~key:int32_line ~data:false
;;

(* Iterates through each line
   At each line:
   1. Update mov table
   2. Insert definition into defs table
   3. Insert uses into uses table
   4. Inserts the line number into the jumps table if it is a string *)
let pre_processing
  ~(uses_table : OperandSet.t Int32Table.t)
  ~(defs_table : AS.operand Int32Table.t)
  ~(movs_table : bool Int32Table.t)
  ~(jump_table : (String.t, Int32.t) Hashtbl.t)
  ~(assem_list : AS.instr list)
  : AS.instr Array.t
  =
  let assem_arr = Array.of_list assem_list in
  let preproc_fn = create_preproc_fn ~uses_table ~defs_table ~movs_table ~jump_table in
  let (_ : unit) = Array.iteri assem_arr ~f:preproc_fn in
  assem_arr
;;

(* Searches jump table for the label to get line number for jump *)
let find_jump_line ~(jump_table : (String.t, Int32.t) Hashtbl.t) (label : String.t) =
  match Hashtbl.find jump_table label with
  | Some line_no -> line_no
  | None -> failwith "Line number for label unfound"
;;

(* Given a line number, find all predecessor lines *)
let get_pred_set ~(pred_table : Int32Set.t Int32Table.t) (line_no : Int32.t) =
  match Int32Table.find pred_table line_no with
  | None -> Int32Set.empty
  | Some x -> x
;;

(* Given a table of operandset as values, get the operandset *)
let get_op_set ~(set_table : OperandSet.t Int32Table.t) (line_no : Int32.t) =
  match Hashtbl.find set_table line_no with
  | None -> OperandSet.empty
  | Some x -> x
;;

(* Check that an operand is in the operandset at a line, given the table *)
let check_in_set variable line_number ~set_table =
  match Int32Table.find set_table line_number with
  | Some x -> Set.exists x ~f:(fun var -> AS.compare_operand var variable = 0)
  | None -> false
;;

(* Check if value is defined on a given line *)
let check_if_defined variable line_number ~defs_table =
  match Int32Table.find defs_table line_number with
  | Some x -> AS.compare_operand variable x = 0
  | None -> false
;;

(* Build table of predecessors by looking at the jump table and successors *)
let build_pred_table
  ~(pred_table : Int32Set.t Int32Table.t)
  ~(jump_table : (String.t, Int32.t) Hashtbl.t)
  ~(instr_array : AS.instr Array.t)
  =
  let pred_table_fn line_no instr =
    let int32_line = Int32.of_int_trunc line_no in
    match instr with
    | AS.Mov _
    | AS.Directive _
    | AS.Comment _
    | AS.Cmp _
    | AS.Label _
    | AS.Nullop _
    | AS.Unop _
    | AS.Binop _
    | AS.Test _
    | AS.Ret ->
      let lcurr = int32_line in
      let lnext = Int32.succ lcurr in
      Int32Table.update pred_table lnext ~f:(fun pred_set ->
        match pred_set with
        | None -> Int32Set.of_list [ lcurr ]
        | Some x -> Int32Set.add x lcurr)
      (* assert (add_to_table pred_table ~key:lnext ~data:pred_set) *)
    | JumpC { label; _ } ->
      let lcurr = int32_line in
      let lnext = Int32.succ lcurr in
      let label_str =
        match label with
        | AS.Label s -> s
        | _ -> failwith "AS Jump should only contain a label"
      in
      let ljump = find_jump_line ~jump_table label_str in
      let (_ : unit) =
        Int32Table.update pred_table ljump ~f:(fun pred_set ->
          match pred_set with
          | None -> Int32Set.of_list [ int32_line ]
          | Some x -> Int32Set.add x int32_line)
      in
      Int32Table.update pred_table lnext ~f:(fun pred_set ->
        match pred_set with
        | None -> Int32Set.of_list [ int32_line ]
        | Some x -> Int32Set.add x int32_line)
    (* let pred_set_jump_init = get_pred_set ~pred_table ljump in
      let pred_set_next = Int32Set.add pred_set_next_init lcurr in
      let pred_set_jump = Int32Set.add pred_set_jump_init lcurr in
      assert (add_to_table pred_table ~key:lnext ~data:pred_set_next);
      assert (add_to_table pred_table ~key:ljump ~data:pred_set_jump) *)
    | Jump { label } ->
      let label_str =
        match label with
        | AS.Label s -> s
        | _ -> failwith "AS Jump should only contain a label"
      in
      let ljump = find_jump_line ~jump_table label_str in
      Int32Table.update pred_table ljump ~f:(fun pred_set ->
        match pred_set with
        | None -> Int32Set.of_list [ int32_line ]
        | Some x -> Int32Set.add x int32_line)
  in
  Array.iteri instr_array ~f:pred_table_fn
;;

(* Check if variable is in liveout and ensure it is either live-in or defined *)
let is_variable_in_liveout ~variable ~line_number ~liveout_table ~livein_table ~defs_table
  =
  match check_in_set variable line_number ~set_table:liveout_table with
  | true ->
    assert (
      check_in_set variable line_number ~set_table:livein_table
      || check_if_defined variable line_number ~defs_table);
    true
  | false -> false
;;

(* After encountering a variable that is used, retrace the predecessor lines
   Recursively update the live-out set for the predecessor line P
   If the variable is defined, then stop
   If the variable is not defined,
      update the live-in set for the predecessor P
      then call itself on the predecessors of P
   *)
let rec retrace_control_flow
  ~variable
  ~liveout_table
  ~livein_table
  ~defs_table
  ~pred_table
  ~preds
  =
  let retrace_helper pred_line =
    if not
         (is_variable_in_liveout
            ~variable
            ~line_number:pred_line
            ~liveout_table
            ~livein_table
            ~defs_table)
    then (
      let (_ : unit) =
        Int32Table.update liveout_table pred_line ~f:(fun liveout_set ->
          match liveout_set with
          | None -> OperandSet.of_list [ variable ]
          | Some x -> OperandSet.add x variable)
      in
      if not (check_if_defined variable pred_line ~defs_table)
      then (
        let (_ : unit) =
          Int32Table.update livein_table pred_line ~f:(fun livein_set ->
            match livein_set with
            | None -> OperandSet.of_list [ variable ]
            | Some x -> OperandSet.add x variable)
        in
        let predset_of_pred_line = get_pred_set ~pred_table pred_line in
        retrace_control_flow
          ~variable
          ~liveout_table
          ~livein_table
          ~defs_table
          ~pred_table
          ~preds:predset_of_pred_line))
    else ()
  in
  Int32Set.iter preds ~f:retrace_helper
;;

(* Starts from the last line and works backwards to the first line *)
let work_backwards
  ~pred_table
  ~uses_table
  ~defs_table
  ~livein_table
  ~liveout_table
  no_lines
  =
  let rec helper_fn curr_line =
    if not (Int32.is_negative curr_line)
    then (
      let uses_set = get_op_set ~set_table:uses_table curr_line in
      ignore
        (OperandSet.iter uses_set ~f:(fun used_var ->
           match used_var with
           | AS.Imm _ | AS.Ref _ | AS.Label _ | AS.MAX_INT ->
             failwith "not supported operands for sets"
           | AS.Reg _ | AS.Temp _ ->
             (match check_in_set used_var curr_line ~set_table:livein_table with
              | true -> ()
              | false ->
                let (_ : unit) =
                  Int32Table.update livein_table curr_line ~f:(fun livein_set ->
                    match livein_set with
                    | None -> OperandSet.of_list [ used_var ]
                    | Some x -> OperandSet.add x used_var)
                in
                let pred_set = get_pred_set ~pred_table curr_line in
                retrace_control_flow
                  ~variable:used_var
                  ~liveout_table
                  ~livein_table
                  ~defs_table
                  ~pred_table
                  ~preds:pred_set))
          : unit);
      helper_fn (Int32.pred curr_line))
    else ()
  in
  helper_fn no_lines
;;

(* Build the line list for Max Card Search *)
let build_line_list
  list_len
  ~(liveout_table : OperandSet.t Int32Table.t)
  ~(uses_table : OperandSet.t Int32Table.t)
  ~(defs_table : AS.operand Int32Table.t)
  ~(movs_table : bool Int32Table.t)
  =
  let rec build_helper list_len acc =
    match list_len with
    | n when Int32.( < ) n Int32.zero -> acc
    | n ->
      build_helper
        (Int32.pred list_len)
        ({ uses =
             OperandSet.to_list
               (match Hashtbl.find uses_table n with
                | None -> OperandSet.empty
                | Some x -> x)
         ; defines =
             (match Hashtbl.find defs_table n with
              | None -> []
              | Some x -> [ x ])
         ; live_out =
             OperandSet.to_list
               (match Hashtbl.find liveout_table n with
                | None -> OperandSet.empty
                | Some x -> x)
         ; move =
             (match Hashtbl.find movs_table n with
              | None ->
                failwith
                  (sprintf "move must have value, no value for %s" (Int32.to_string n))
              | Some x -> x)
         ; line_number = n
         }
         :: acc)
  in
  build_helper (Int32.pred list_len) []
;;

(* Creates list of lines required for liveness analysis *)
let liveness (assem_list : AS.instr list) : line list =
  let pred_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let jump_table = Hashtbl.create ~growth_allowed:true ~size:500 (module String) in
  let livein_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let liveout_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let uses_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let defs_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let movs_table = Int32Table.create ~growth_allowed:true ~size:500 () in
  let assem_arr =
    pre_processing ~uses_table ~defs_table ~movs_table ~jump_table ~assem_list
  in
  let arr_size = Int32.of_int_trunc (Array.length assem_arr) in
  let (_ : unit) = build_pred_table ~pred_table ~jump_table ~instr_array:assem_arr in
  let (_ : unit) =
    work_backwards
      ~pred_table
      ~uses_table
      ~defs_table
      ~livein_table
      ~liveout_table
      (Int32.pred arr_size)
  in
  build_line_list arr_size ~liveout_table ~uses_table ~defs_table ~movs_table
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
