(* L1 Compiler
 * Converts from finalassem into liveness json
 * Parses the input in reverse
 * Follow the algorithm from recitation
 * Implementation: Read the readme.md for documentation
 *)

open Core
module AS = Assem

(* Created modules to simplify functions *)
module Int32Set = Type_modules.Int32Set
module Int32Table = Type_modules.Int32Table
module NodeTable = Regalloc_modules.NodeTable
module NodeSet = Regalloc_modules.NodeSet

type line =
  { uses : NodeSet.t
  ; defines : NodeSet.t
  ; live_out : NodeSet.t
  ; move : bool
  ; line_number : Int32.t
  }

let call_def_set : NodeSet.t =
  NodeSet.of_list
    [ Node.Reg AS.AX
    ; Node.Reg AS.DI
    ; Node.Reg AS.SI
    ; Node.Reg AS.DX
    ; Node.Reg AS.CX
    ; Node.Reg AS.R8
    ; Node.Reg AS.R9
    ; Node.Reg AS.R10
    ; Node.Reg AS.R11
    ]
;;

let arg_regs_list : Node.t list =
  [ Node.Reg AS.DI
  ; Node.Reg AS.SI
  ; Node.Reg AS.DX
  ; Node.Reg AS.CX
  ; Node.Reg AS.R8
  ; Node.Reg AS.R9
  ]
;;

(* Functions only define min(6, args_len) registers. *)
let select_regs ~(args_len : int) =
  let rec helper acc lst rem =
    match lst, rem with
    | _, 0 -> acc
    | [], _ -> acc
    | h :: t, _ -> helper (h :: acc) t (rem - 1)
  in
  helper [] arg_regs_list args_len
;;

(* Temps that represent arguments are used, along with their corresponding
   argument registers. *)
let used_nodes_call ~(args : AS.operand list) : NodeSet.t =
  let args_len = List.length args in
  let used_vals =
    List.fold_left args ~init:[] ~f:(fun acc arg ->
      match arg with
      | AS.Temp _ | AS.Reg _ -> Node.node_of_operand arg :: acc
      | AS.MAX_INT | AS.Imm _ | AS.Addr_imm _ -> acc
      | AS.Stack_ref _ -> failwith "no refs allowed when extracting args")
  in
  let regs_used = select_regs ~args_len in
  let vals_nodeset = NodeSet.of_list used_vals in
  let regs_nodeset = NodeSet.of_list regs_used in
  NodeSet.union vals_nodeset regs_nodeset
;;

let node_of_operand_opt (op : AS.operand) : Node.t option =
  match op with
  | MAX_INT | Imm _ | Addr_imm _ -> None
  | Reg _ | Temp _ -> Some (Node.node_of_operand op)
  | Stack_ref _ -> None
;;

let call_use_set ~(args_table : (string, NodeSet.t) Hashtbl.t) ~(label : string)
  : NodeSet.t
  =
  match Hashtbl.find args_table label with
  | Some x -> x
  | None -> failwith "function call must have set, even if empty"
;;

(* Adds a value to a node set *)
let add_to_set ~curr_set ~op_opt =
  match op_opt with
  | None -> curr_set
  | Some x -> NodeSet.add curr_set x
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
  ~(uses_table : NodeSet.t Int32Table.t)
  ~(defs_table : NodeSet.t Int32Table.t)
  ~(movs_table : bool Int32Table.t)
  ~(jump_table : (String.t, Int32.t) Hashtbl.t)
  (line_no : int)
  (instr : AS.instr)
  =
  let int32_line = line_no |> Int32.of_int_trunc |> Int32.succ in
  let used_values =
    match Hashtbl.find uses_table int32_line with
    | None -> NodeSet.empty
    | Some x -> x
  in
  let def_values =
    match Hashtbl.find defs_table int32_line with
    | None -> NodeSet.empty
    | Some x -> x
  in
  match instr with
  | AS.Binop { src; dest; _ } ->
    let add_src = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt src) in
    let add_dest = add_to_set ~curr_set:def_values ~op_opt:(node_of_operand_opt dest) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_src);
    assert (add_to_table defs_table ~key:int32_line ~data:add_dest);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Unop { op; src; div_type; _ } ->
    (* Word size not used in liveness analysis*)
    (match op with
     | AS.IDiv ->
       let dest =
         match div_type with
         | AS.Div -> Some (Node.Reg AS.AX)
         | AS.Mod -> Some (Node.Reg AS.DX)
         | _ -> failwith "div type for unop must only be div or mod"
       in
       let add_edx = add_to_set ~curr_set:used_values ~op_opt:(Some (Node.Reg AS.DX)) in
       let add_eax = add_to_set ~curr_set:add_edx ~op_opt:(Some (Node.Reg AS.AX)) in
       let add_src = add_to_set ~curr_set:add_eax ~op_opt:(node_of_operand_opt src) in
       let add_dest = add_to_set ~curr_set:def_values ~op_opt:dest in
       assert (add_to_table uses_table ~key:int32_line ~data:add_src);
       assert (add_to_table defs_table ~key:int32_line ~data:add_dest);
       Hashtbl.set movs_table ~key:int32_line ~data:false)
  | AS.Nullop { op } ->
    (* Treat nullop as using eax to define edx *)
    (match op with
     | AS.Cltd ->
       let add_eax = add_to_set ~curr_set:used_values ~op_opt:(Some (Node.Reg AS.AX)) in
       let add_edx = add_to_set ~curr_set:def_values ~op_opt:(Some (Node.Reg AS.DX)) in
       assert (add_to_table uses_table ~key:int32_line ~data:add_eax);
       assert (add_to_table defs_table ~key:int32_line ~data:add_edx);
       Hashtbl.set movs_table ~key:int32_line ~data:false)
  | AS.Cmp { lhs; rhs } ->
    let add_lhs = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt lhs) in
    let add_rhs = add_to_set ~curr_set:add_lhs ~op_opt:(node_of_operand_opt rhs) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_rhs);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Mov { dest; src }
  | AS.Movsx { dest; src }
  | AS.Movzx { dest; src }
  | AS.Mov_trunc { dest; src } ->
    (* Word size not used in liveness analysis *)
    let add_src = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt src) in
    let add_dest = add_to_set ~curr_set:def_values ~op_opt:(node_of_operand_opt dest) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_src);
    assert (add_to_table defs_table ~key:int32_line ~data:add_dest);
    Hashtbl.set movs_table ~key:int32_line ~data:true
  | AS.Load { dest; base; index; _ } ->
    (* Defines dest, uses base + index *)
    let add_base = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt base) in
    let add_index = add_to_set ~curr_set:add_base ~op_opt:(node_of_operand_opt index) in
    let add_dest = add_to_set ~curr_set:def_values ~op_opt:(node_of_operand_opt dest) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_index);
    assert (add_to_table defs_table ~key:int32_line ~data:add_dest);
    Hashtbl.set movs_table ~key:int32_line ~data:true
  | AS.Lea { dest; base; index; _ } ->
    (* Defines dest, uses base + index *)
    let add_base = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt base) in
    let add_index = add_to_set ~curr_set:add_base ~op_opt:(node_of_operand_opt index) in
    let add_dest = add_to_set ~curr_set:def_values ~op_opt:(node_of_operand_opt dest) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_index);
    assert (add_to_table defs_table ~key:int32_line ~data:add_dest);
    Hashtbl.set movs_table ~key:int32_line ~data:true
  | AS.Store { src; base; index; _ } ->
    (* Defines a memory location, requires base + index + src *)
    let add_src = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt src) in
    let add_base = add_to_set ~curr_set:add_src ~op_opt:(node_of_operand_opt base) in
    let add_index = add_to_set ~curr_set:add_base ~op_opt:(node_of_operand_opt index) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_index);
    (* Should be empty *)
    assert (add_to_table defs_table ~key:int32_line ~data:def_values);
    Hashtbl.set movs_table ~key:int32_line ~data:true
  | AS.Directive _ | AS.Comment _ -> Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Label label ->
    (* Don't need to think about defs or uses here, neither are used *)
    assert (add_to_table jump_table ~key:label ~data:int32_line);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Jmp _ ->
    (* Jumps to the label *)
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Jc _ -> Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Ret ->
    (* Ret are supposed to use eax *)
    let used_eax = Some (Node.Reg AS.AX) in
    let add_eax = add_to_set ~curr_set:used_values ~op_opt:used_eax in
    assert (add_to_table uses_table ~key:int32_line ~data:add_eax);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Test { lhs; rhs } ->
    let add_lhs = add_to_set ~curr_set:used_values ~op_opt:(node_of_operand_opt lhs) in
    let add_rhs = add_to_set ~curr_set:add_lhs ~op_opt:(node_of_operand_opt rhs) in
    assert (add_to_table uses_table ~key:int32_line ~data:add_rhs);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Call { args; _ } ->
    (* Now, it is not the uses set.
       Need a new function. 
       All the args into the call will be added into uses
       The same number of args will also be added from the regs.
    *)
    let add_uses = used_nodes_call ~args in
    assert (NodeSet.is_empty def_values);
    assert (NodeSet.is_empty used_values);
    assert (add_to_table defs_table ~key:int32_line ~data:call_def_set);
    assert (add_to_table uses_table ~key:int32_line ~data:add_uses);
    Hashtbl.set movs_table ~key:int32_line ~data:false
  | AS.Pop _ | AS.Push _ -> failwith "pop and push dont exist in liveness"
;;

let initialise_defs_table
  ~(defs_table : NodeSet.t Int32Table.t)
  ~(args_table : (string, NodeSet.t) Hashtbl.t)
  ~(label : string)
  : unit
  =
  let line_zero = Int32.zero in
  let add_defs = call_use_set ~args_table ~label in
  assert (add_to_table defs_table ~key:line_zero ~data:add_defs)
;;

let initialise_pred_table ~(pred_table : Int32Set.t Int32Table.t) : unit =
  let line_zero = Int32.zero in
  let lnext = Int32.succ line_zero in
  Int32Table.update pred_table lnext ~f:(fun pred_set ->
    match pred_set with
    | None -> Int32Set.of_list [ line_zero ]
    | Some _ -> failwith "wtf is gg here lol")
;;

(* DESIGN DECISION: All lines now start from 1, 
       first line has pred of 0, 
       line 0 will be the func_label line (effectively means defs taken from somewhere else)
    *)
(* | AS.Func_label { label; _ } ->
    (* Might want to assert that this line is line 0, 
       only have first line as function definition *)
    assert (Int32.equal int32_line Int32.zero);
    (* For function labels, the "used" are being defined *)
    let add_defs = call_use_set ~args_table ~label in
    assert (NodeSet.is_empty def_values);
    assert (NodeSet.is_empty used_values);
    assert (add_to_table defs_table ~key:int32_line ~data:add_defs);
    Hashtbl.set movs_table ~key:int32_line ~data:false *)

(* Iterates through each line
    At each line:
    1. Update mov table
    2. Insert definition into defs table
    3. Insert uses into uses table
    4. Inserts the line number into the jumps table if it is a string *)
let pre_processing
  ~(uses_table : NodeSet.t Int32Table.t)
  ~(defs_table : NodeSet.t Int32Table.t)
  ~(movs_table : bool Int32Table.t)
  ~(jump_table : (String.t, Int32.t) Hashtbl.t)
  ~(assem_list : AS.instr list)
  : unit
  =
  let preproc_fn = create_preproc_fn ~uses_table ~defs_table ~movs_table ~jump_table in
  List.iteri assem_list ~f:preproc_fn
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

(* Given a table of nodeset as values, get the nodeset *)
let get_node_set ~(set_table : NodeSet.t Int32Table.t) (line_no : Int32.t) =
  match Hashtbl.find set_table line_no with
  | None -> NodeSet.empty
  | Some x -> x
;;

(* Check that a node is in the nodeset at a line, given the table *)
let check_in_set (variable : Node.t) line_number ~set_table =
  match Int32Table.find set_table line_number with
  | Some x -> NodeSet.mem x variable
  | None -> false
;;

(* Check if value is defined on a given line *)
let check_if_defined (variable : Node.t) line_number ~defs_table =
  match Int32Table.find defs_table line_number with
  | Some x -> NodeSet.mem x variable
  | None -> false
;;

(* Build table of predecessors by looking at the jump table and successors *)
let build_pred_table
  ~(pred_table : Int32Set.t Int32Table.t)
  ~(jump_table : (String.t, Int32.t) Hashtbl.t)
  ~(instr_list : AS.instr list)
  =
  let pred_table_fn line_no instr =
    let int32_line = Int32.of_int_trunc line_no in
    match instr with
    | AS.Pop _ | AS.Push _ -> failwith "no pop or push in liveness"
    | AS.Mov _
    | AS.Movsx _
    | AS.Movzx _
    | AS.Mov_trunc _
    | AS.Load _
    | AS.Lea _
    | AS.Store _
    | AS.Directive _
    | AS.Comment _
    | AS.Cmp _
    | AS.Label _
    | AS.Nullop _
    | AS.Unop _
    | AS.Binop _
    | AS.Call _ (* Calls should only have pred as the jump i think*)
    | AS.Test _ ->
      let lcurr = int32_line in
      let lnext = Int32.succ lcurr in
      Int32Table.update pred_table lnext ~f:(fun pred_set ->
        match pred_set with
        | None -> Int32Set.of_list [ lcurr ]
        | Some x -> Int32Set.add x lcurr)
      (* assert (add_to_table pred_table ~key:lnext ~data:pred_set) *)
    | Jc { label; _ } ->
      let lcurr = int32_line in
      let lnext = Int32.succ lcurr in
      let ljump = find_jump_line ~jump_table label in
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
    | Jmp label ->
      let ljump = find_jump_line ~jump_table label in
      Int32Table.update pred_table ljump ~f:(fun pred_set ->
        match pred_set with
        | None -> Int32Set.of_list [ int32_line ]
        | Some x -> Int32Set.add x int32_line)
    | Ret -> () (* Returns should not have a successor *)
  in
  List.iteri instr_list ~f:pred_table_fn
;;

(* Check if variable is in liveout and ensure it is either live-in or defined *)
let is_variable_in_liveout
  ~(variable : Node.t)
  ~line_number
  ~liveout_table
  ~livein_table
  ~defs_table
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
  ~(variable : Node.t)
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
          | None -> NodeSet.of_list [ variable ]
          | Some x -> NodeSet.add x variable)
      in
      if not (check_if_defined variable pred_line ~defs_table)
      then (
        let (_ : unit) =
          Int32Table.update livein_table pred_line ~f:(fun livein_set ->
            match livein_set with
            | None -> NodeSet.of_list [ variable ]
            | Some x -> NodeSet.add x variable)
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
    if Int32.is_positive curr_line
    then (
      let uses_set = get_node_set ~set_table:uses_table curr_line in
      ignore
        (NodeSet.iter uses_set ~f:(fun (used_var : Node.t) ->
           match check_in_set used_var curr_line ~set_table:livein_table with
           | true -> ()
           | false ->
             let (_ : unit) =
               Int32Table.update livein_table curr_line ~f:(fun livein_set ->
                 match livein_set with
                 | None -> NodeSet.of_list [ used_var ]
                 | Some x -> NodeSet.add x used_var)
             in
             let pred_set = get_pred_set ~pred_table curr_line in
             retrace_control_flow
               ~variable:used_var
               ~liveout_table
               ~livein_table
               ~defs_table
               ~pred_table
               ~preds:pred_set)
          : unit);
      helper_fn (Int32.pred curr_line))
    else ()
  in
  helper_fn no_lines
;;

(* Build the line list for Max Card Search *)
let build_line_list
  list_len
  ~(liveout_table : NodeSet.t Int32Table.t)
  ~(uses_table : NodeSet.t Int32Table.t)
  ~(defs_table : NodeSet.t Int32Table.t)
  ~(movs_table : bool Int32Table.t)
  =
  let rec build_helper list_len acc =
    match list_len with
    | n when Int32.( = ) n Int32.zero -> acc
    | n ->
      build_helper
        (Int32.pred list_len)
        ({ uses =
             (match Hashtbl.find uses_table n with
              | None -> NodeSet.empty
              | Some x -> x)
         ; defines =
             (match Hashtbl.find defs_table n with
              | None -> NodeSet.empty
              | Some x -> x)
         ; live_out =
             (match Hashtbl.find liveout_table n with
              | None -> NodeSet.empty
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

(** Creates list of lines required for liveness analysis. [fn_args]  *)
let liveness
  (func : AS.func)
  (fn_args : (string, NodeSet.t) Hashtbl.t)
  (liveness_tables : Regalloc_modules.liveness_tables)
  ~(timestamps : Timestamp.t)
  : line list
  =
  let uses_table = liveness_tables.uses_table in
  let defs_table = liveness_tables.defs_table in
  let movs_table = liveness_tables.movs_table in
  let jump_table = liveness_tables.jump_table in
  let pred_table = liveness_tables.pred_table in
  let liveout_table = liveness_tables.liveout_table in
  let livein_table = liveness_tables.livein_table in
  let assem_list = snd func in
  let label = (fst func).label in
  let (_ : unit) = initialise_pred_table ~pred_table in
  let (_ : unit) = initialise_defs_table ~defs_table ~args_table:fn_args ~label in
  Timestamp.mark_timestamp timestamps ((fst func).label ^ " pre-proc");
  let (_ : unit) =
    pre_processing ~uses_table ~defs_table ~movs_table ~jump_table ~assem_list
  in
  Timestamp.mark_timestamp timestamps ((fst func).label ^ " pre-proc");
  let arr_size = Int32.of_int_trunc (List.length assem_list) in
  Timestamp.mark_timestamp timestamps ((fst func).label ^ " work_backwards");
  let (_ : unit) = build_pred_table ~pred_table ~jump_table ~instr_list:assem_list in
  let (_ : unit) =
    work_backwards
      ~pred_table
      ~uses_table
      ~defs_table
      ~livein_table
      ~liveout_table
      arr_size
  in
  Timestamp.mark_timestamp timestamps ((fst func).label ^ " work_backwards");
  Timestamp.mark_timestamp timestamps ((fst func).label ^ " build_line_list");
  let res = build_line_list arr_size ~liveout_table ~uses_table ~defs_table ~movs_table in
  Timestamp.mark_timestamp timestamps ((fst func).label ^ " build_line_list");
  res
;;

(* Helper functions to format output for testing *)
let format_node x = "\"" ^ Node.format_node x ^ "\""

let format_node_set node_set =
  "[" ^ String.concat ~sep:", " (List.map ~f:format_node (NodeSet.to_list node_set)) ^ "]"
;;

let string_of_line { uses; defines; live_out; move; line_number } =
  "{\n\"Uses\": "
  ^ format_node_set uses
  ^ ",\n"
  ^ "\"Defines\": "
  ^ format_node_set defines
  ^ ",\n"
  ^ "\"Live_out\": "
  ^ format_node_set live_out
  ^ ",\n"
  ^ "\"Move\": "
  ^ (if move then "true" else "false")
  ^ ",\n"
  ^ "\"Line\": "
  ^ Int32.to_string line_number
  ^ ",\n},\n"
;;

let string_of_node_lst lst =
  "[" ^ String.concat ~sep:" " (List.map lst ~f:string_of_line) ^ "]"
;;
