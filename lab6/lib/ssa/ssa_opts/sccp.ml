open Core
module CFG = Cfg.CFG
module Dot = Cfg.Dot
module Bfs = Cfg.Bfs
module Node = CFG.Node
module VarTable = Type_modules.SSAVarTable
module VarSet = Type_modules.SSAVarSet
module IdSet = Set.Make (Int)
module BlockSet = Set.Make (String)

type valTau =
  | Undefined
  | Constant of Ssa.operand
  | Overdefined

let formatTau = function
  | Undefined -> "undef"
  | Overdefined -> "overdefined"
  | Constant x -> sprintf "const(%s)" (Ssa.format_operand x)
;;

let neg_condition condition =
  Ssa.(
    match condition with
    | Lt -> Gt
    | Leq -> Geq
    | Gt -> Lt
    | Geq -> Leq
    | Eq -> Eq
    | Neq -> Neq)
;;

let update_if lhs rhs condition lt lf =
  Ssa.(
    match lhs, rhs with
    | Temp _, Imm _ | Temp _, Addr_imm _ | Temp _, MAX_INT ->
      If { lhs = rhs; rhs = lhs; condition = neg_condition condition; lt; lf }
    | _ -> If { lhs; rhs; condition; lt; lf })
;;

module SSAOperand = struct
  type t = Ssa.operand [@@deriving compare, sexp, hash]
end

let id_to_instr : (Int.t, Ssa.instr) Hashtbl.t = Hashtbl.create (module Int)
let label_to_ids : (Node.t, Int.t list) Hashtbl.t = Hashtbl.create (module Node)
let id_to_label : (Int.t, String.t) Hashtbl.t = Hashtbl.create (module Int)

let operand_uses_tbl : (SSAOperand.t, IdSet.t) Hashtbl.t =
  Hashtbl.create (module SSAOperand)
;;

(* let operand_def_tbl : (SSAOperand.t, Int.t) Hashtbl.t = Hashtbl.create (module SSAOperand) *)

let operand_lattice_tbl : (SSAOperand.t, valTau) Hashtbl.t =
  Hashtbl.create (module SSAOperand)
;;

let operand_in_memoperation : (SSAOperand.t, bool) Hashtbl.t =
  Hashtbl.create (module SSAOperand)
;;

let args_to_label : (SSAOperand.t, String.t) Hashtbl.t =
  Hashtbl.create (module SSAOperand)
;;

let block_executed_tbl : (String.t, bool) Hashtbl.t = Hashtbl.create (module String)
let block_worklist = ref BlockSet.empty
let variable_worklist = ref VarSet.empty
let get_lattice_val operand = Hashtbl.find_exn operand_lattice_tbl operand

let get_processed_lattice_val operand =
  match get_lattice_val operand with
  | Overdefined -> operand
  | Constant x -> x
  | Undefined ->
    Printf.printf "%s\n" (Ssa.format_operand operand);
    failwith "why operand undefined?"
;;

let set_lattice_val operand tau = Hashtbl.set operand_lattice_tbl ~key:operand ~data:tau
let sign_extend (x : Int32.t) : Int64.t = Int64.of_int32 x

let zero_extend (x : Int32.t) : Int64.t =
  let only_lower_32 = Int64.(shift_left one 32 - one) in
  Int64.(of_int32 x land only_lower_32)
;;

(* 
  Compare x and y
  Returns true if x is higher up than y (implies y needs to be promoted)
*)
let ( >> ) x y =
  match x, y with
  | Overdefined, Overdefined -> false
  | Overdefined, _ -> true
  | Constant _, Overdefined -> false
  | Constant _, Constant _ -> false
  | Constant _, _ -> true
  | Undefined, _ -> false
;;

let promote_operand operand tau =
  (* Printf.printf
    "%s promoted from %s to %s\n"
    (Ssa.format_operand operand)
    (formatTau (get_lattice_val operand))
    (formatTau tau); *)
  set_lattice_val operand tau;
  variable_worklist := VarSet.add !variable_worklist operand
;;

let get_label cfg curr_label ind = List.nth_exn (CFG.pred cfg curr_label) ind

let is_block_executable label =
  match Hashtbl.find block_executed_tbl label with
  | Some _ -> true
  | None -> false
;;

let set_block_executable label = Hashtbl.set block_executed_tbl ~key:label ~data:true

let set_operand_memoperation operand =
  Hashtbl.set operand_in_memoperation ~key:operand ~data:true
;;

let is_operand_in_memoperation operand =
  match Hashtbl.find operand_in_memoperation operand with
  | Some _ -> true
  | None -> false
;;

let get_executed cfg curr_label ind =
  let label = get_label cfg curr_label ind in
  is_block_executable label
;;

let promote_block block =
  if is_block_executable block
  then ()
  else (
    set_block_executable block;
    block_worklist := BlockSet.add !block_worklist block)
;;

let evaluate_binop_64 lhs rhs op =
  Ssa.(
    match op with
    | Add -> Int64.(lhs + rhs), true
    | Sub -> Int64.(lhs - rhs), true
    | Mul -> Int64.(lhs * rhs), true
    | Div -> if Int64.(rhs = Int64.zero) then lhs, false else Int64.(lhs / rhs), true
    | Mod -> if Int64.(rhs = Int64.zero) then lhs, false else Int64.(rem lhs rhs), true
    | Or -> Int64.(lhs lor rhs), true
    | Xor -> Int64.(lhs lxor rhs), true
    | And -> Int64.(lhs land rhs), true
    | Sal -> Int64.(lhs lsl to_int_trunc rhs), true
    | Sar -> Int64.(shift_right lhs (to_int_trunc rhs)), true
    | Shr -> Int64.(shift_right_logical lhs (to_int_trunc rhs)), true)
;;

let evaluate_binop_32 lhs rhs op =
  Ssa.(
    match op with
    | Add -> Int32.(lhs + rhs), true
    | Sub -> Int32.(lhs - rhs), true
    | Mul -> Int32.(lhs * rhs), true
    | Div ->
      if Int32.(
           rhs = Int32.zero
           || Int64.(of_int32 Int32.(lhs / rhs) <> of_int32 lhs / of_int32 rhs))
      then lhs, false
      else Int32.(lhs / rhs), true
    | Mod ->
      if Int32.(
           rhs = Int32.zero
           || Int64.(of_int32 Int32.(lhs / rhs) <> of_int32 lhs / of_int32 rhs))
      then lhs, false
      else Int32.(rem lhs rhs), true
    | Or -> Int32.(lhs lor rhs), true
    | Xor -> Int32.(lhs lxor rhs), true
    | And -> Int32.(lhs land rhs), true
    | Sal ->
      if Int32.(rhs >= of_int_trunc 32 || is_negative rhs)
      then lhs, false
      else Int32.(lhs lsl to_int_trunc rhs), true
    | Sar ->
      if Int32.(rhs >= of_int_trunc 32 || is_negative rhs)
      then lhs, false
      else Int32.(shift_right lhs (to_int_trunc rhs)), true
    | Shr ->
      if Int32.(rhs >= of_int_trunc 32 || is_negative rhs)
      then lhs, false
      else Int32.(shift_right_logical lhs (to_int_trunc rhs)), true)
;;

let process_binop_consts lhs rhs op =
  Ssa.(
    match lhs, rhs with
    | Imm x, Imm y ->
      let res, can = evaluate_binop_32 x y op in
      if can then Some (Imm res) else None
    | Addr_imm _, Addr_imm _ ->
      None
      (*
          None because address operations cant be done 
          https://stackoverflow.com/questions/23762332/addq-with-64bit-immediates
          *)
      (* let res, can = evaluate_binop_64 x y op in
        if can then Some (Addr_imm res) else None *)
    | MAX_INT, MAX_INT ->
      let res, can = evaluate_binop_32 Int32.(~-one) Int32.(~-one) op in
      if can then Some (Imm res) else None
    | Imm x, MAX_INT ->
      let res, can = evaluate_binop_32 x Int32.(~-one) op in
      if can then Some (Imm res) else None
    | MAX_INT, Imm y ->
      let res, can = evaluate_binop_32 Int32.(~-one) y op in
      if can then Some (Imm res) else None
    | _ -> failwith "how did we end up here?")
;;

let process_binop lhs rhs op =
  let lhs = get_lattice_val lhs in
  let rhs = get_lattice_val rhs in
  (* Printf.printf "%s (%s) %s\n" (formatTau lhs) (Ssa.format_binop op) (formatTau rhs); *)
  match lhs, rhs with
  | Overdefined, _ -> Overdefined
  | _, Overdefined -> Overdefined
  | Constant lhs', Constant rhs' ->
    (match process_binop_consts lhs' rhs' op with
     | Some x -> Constant x
     | None -> Overdefined)
  | Undefined, Constant _ -> Undefined
  | Constant _, Undefined -> Undefined
  | Undefined, Undefined -> Undefined
;;

let process_mov src = get_lattice_val src

let process_movsx src =
  let src_val = get_lattice_val src in
  match src_val with
  | Undefined -> Undefined
  | Overdefined -> Overdefined
  | Constant lattice_val ->
    Constant
      (match lattice_val with
       | Ssa.Imm x -> Ssa.Addr_imm (sign_extend x)
       | Ssa.MAX_INT -> Ssa.Addr_imm (sign_extend Int32.(~-one))
       | _ -> failwith "only imm or maxint (maxint is -1)")
;;

let process_movzx src =
  let src_val = get_lattice_val src in
  match src_val with
  | Undefined -> Undefined
  | Overdefined -> Overdefined
  | Constant lattice_val ->
    Constant
      (match lattice_val with
       | Ssa.Imm x -> Ssa.Addr_imm (zero_extend x)
       | Ssa.MAX_INT -> Ssa.Addr_imm (zero_extend Int32.(~-one))
       | _ -> failwith "only imm or maxint (maxint is -1)")
;;

let process_mov_trunc src =
  let src_lattice = get_lattice_val src in
  match src_lattice with
  | Undefined -> Undefined
  | Overdefined -> Overdefined
  | Constant lattice_val ->
    (match lattice_val with
     | Ssa.Addr_imm x -> Constant (Ssa.Imm (Int32.of_int64_trunc x))
     | _ -> failwith "only addr imm allowed for truncation")
;;

let process_lea_consts disp base index scale =
  match base, index with
  | Ssa.Addr_imm addr, Ssa.Imm imm ->
    Ssa.Addr_imm Int64.(addr + (of_int32 imm * of_int scale) + of_int32 disp)
  | _ ->
    Printf.printf "%s %s\n" (Ssa.format_operand base) (Ssa.format_operand index);
    failwith "why base and index not addr imm and imm?"
;;

let process_lea disp base index scale =
  let base_lattice = get_lattice_val base in
  let index_lattice = get_lattice_val index in
  match base_lattice, index_lattice with
  | Overdefined, _ -> Overdefined
  | _, Overdefined -> Overdefined
  | Constant base', Constant index' ->
    Constant (process_lea_consts disp base' index' scale)
  | Undefined, Constant _ -> Undefined
  | Constant _, Undefined -> Undefined
  | Undefined, Undefined -> Undefined
;;

let process_phi_args args _ _ =
  let args_lattice = List.map args ~f:(fun arg -> get_lattice_val arg, arg) in
  let res =
    List.fold args_lattice ~init:Undefined ~f:(fun acc (arg_lattice, arg) ->
      let arg_is_executed =
        match arg with
        | Temp x when Temp.get_version x = 0 -> true
        | Temp _ -> is_block_executable (Hashtbl.find_exn args_to_label arg)
        | _ -> failwith "why phi has non temp?"
      in
      match acc with
      | Overdefined -> Overdefined
      | Undefined -> if arg_is_executed then arg_lattice else Undefined
      | Constant x ->
        if not arg_is_executed
        then acc
        else (
          match arg_lattice with
          | Overdefined -> Overdefined
          | Undefined -> acc
          | Constant y -> if Ssa.compare_operand y x <> 0 then Overdefined else acc))
  in
  res
;;

let process_if lhs rhs comparison =
  let lhs = get_lattice_val lhs in
  let rhs = get_lattice_val rhs in
  match lhs, rhs with
  | Overdefined, _ -> Overdefined
  | _, Overdefined -> Overdefined
  | Undefined, Constant _ -> Undefined
  | Constant _, Undefined -> Undefined
  | Undefined, Undefined -> Undefined
  | Constant lhs, Constant rhs ->
    let res =
      Ssa.(
        Imm
          (match rhs, lhs with
           | Imm x', Imm y' ->
             (match comparison with
              | Lt -> if Int32.(x' < y') then Int32.one else Int32.zero
              | Leq -> if Int32.(x' <= y') then Int32.one else Int32.zero
              | Gt -> if Int32.(x' > y') then Int32.one else Int32.zero
              | Geq -> if Int32.(x' >= y') then Int32.one else Int32.zero
              | Eq -> if Int32.(x' = y') then Int32.one else Int32.zero
              | Neq -> if Int32.(x' <> y') then Int32.one else Int32.zero)
           | MAX_INT, Imm y' ->
             (match comparison with
              | Lt -> if Int32.(~-one < y') then Int32.one else Int32.zero
              | Leq -> if Int32.(~-one <= y') then Int32.one else Int32.zero
              | Gt -> if Int32.(~-one > y') then Int32.one else Int32.zero
              | Geq -> if Int32.(~-one >= y') then Int32.one else Int32.zero
              | Eq -> if Int32.(~-one = y') then Int32.one else Int32.zero
              | Neq -> if Int32.(~-one <> y') then Int32.one else Int32.zero)
           | Imm x', MAX_INT ->
             (match comparison with
              | Lt -> if Int32.(x' < ~-one) then Int32.one else Int32.zero
              | Leq -> if Int32.(x' <= ~-one) then Int32.one else Int32.zero
              | Gt -> if Int32.(x' > ~-one) then Int32.one else Int32.zero
              | Geq -> if Int32.(x' >= ~-one) then Int32.one else Int32.zero
              | Eq -> if Int32.(x' = ~-one) then Int32.one else Int32.zero
              | Neq -> if Int32.(x' <> ~-one) then Int32.one else Int32.zero)
           | MAX_INT, MAX_INT ->
             (match comparison with
              | Lt -> if Int32.(~-one < ~-one) then Int32.one else Int32.zero
              | Leq -> if Int32.(~-one <= ~-one) then Int32.one else Int32.zero
              | Gt -> if Int32.(~-one > ~-one) then Int32.one else Int32.zero
              | Geq -> if Int32.(~-one >= ~-one) then Int32.one else Int32.zero
              | Eq -> if Int32.(~-one = ~-one) then Int32.one else Int32.zero
              | Neq -> if Int32.(~-one <> ~-one) then Int32.one else Int32.zero)
           | Addr_imm x', Addr_imm y' ->
             (match comparison with
              | Lt -> if Int64.(x' < y') then Int32.one else Int32.zero
              | Leq -> if Int64.(x' <= y') then Int32.one else Int32.zero
              | Gt -> if Int64.(x' > y') then Int32.one else Int32.zero
              | Geq -> if Int64.(x' >= y') then Int32.one else Int32.zero
              | Eq -> if Int64.(x' = y') then Int32.one else Int32.zero
              | Neq -> if Int64.(x' <> y') then Int32.one else Int32.zero)
           | _ -> failwith "why did comparisons happen?"))
    in
    Constant res
;;

let process_instr instr cfg curr_label =
  Ssa.(
    match instr with
    | Binop { op; lhs; rhs; dest } ->
      (* Printf.printf "%s:" (Ssa.format_operand dest); *)
      let processed_res = process_binop lhs rhs op in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Mov { src; dest } ->
      let processed_res = process_mov src in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Movsx { src; dest } ->
      let processed_res = process_movsx src in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Movzx { src; dest } ->
      let processed_res = process_movzx src in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Mov_trunc { src; dest } ->
      let processed_res = process_mov_trunc src in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Lea { disp; base; index; scale; dest } ->
      (* Process Lea similar to Movsx/Movzx. I.e., do the calculations *)
      let processed_res = process_lea disp base index scale in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Load { dest; _ } ->
      let orig_res = get_lattice_val dest in
      if Overdefined >> orig_res then promote_operand dest Overdefined
    | CallF { dest; _ } ->
      let orig_res = get_lattice_val dest in
      if Overdefined >> orig_res then promote_operand dest Overdefined
    | Phi { dest; args } ->
      let processed_res = process_phi_args args cfg curr_label in
      let orig_res = get_lattice_val dest in
      if processed_res >> orig_res then promote_operand dest processed_res
    | Jump successor -> if is_block_executable curr_label then promote_block successor
    | If { lhs; rhs; condition; lt; lf } ->
      let processed_res = process_if lhs rhs condition in
      (match processed_res with
       | Undefined -> ()
       | Overdefined ->
         promote_block lt;
         promote_block lf
       | Constant x ->
         (match x with
          | Imm x' when Int32.(x' = one) -> promote_block lt
          | Imm x' when Int32.(x' = zero) -> promote_block lf
          | _ -> failwith "result of if evaluation only 1 or 0"))
    | Store _ | Ret _ | Ret_void | Nop | Directive _ | Comment _ | Label _ | Cmp _ -> ())
;;

let process_var_worklist cfg =
  let operand = VarSet.min_elt_exn !variable_worklist in
  variable_worklist := VarSet.remove !variable_worklist operand;
  let operand_uses =
    match Hashtbl.find operand_uses_tbl operand with
    | None -> IdSet.empty
    | Some x -> x
  in
  IdSet.iter operand_uses ~f:(fun instr_id ->
    let instr = Hashtbl.find_exn id_to_instr instr_id in
    let curr_label = Hashtbl.find_exn id_to_label instr_id in
    if is_block_executable curr_label then process_instr instr cfg curr_label)
;;

let process_block_worklist cfg =
  let label = BlockSet.min_elt_exn !block_worklist in
  block_worklist := BlockSet.remove !block_worklist label;
  let instr_ids = Hashtbl.find_exn label_to_ids label in
  List.iter instr_ids ~f:(fun instr_id ->
    let instr = Hashtbl.find_exn id_to_instr instr_id in
    let curr_label = Hashtbl.find_exn id_to_label instr_id in
    if is_block_executable curr_label then process_instr instr cfg curr_label)
;;

let initialise_lattice operand =
  Ssa.(
    match operand with
    | Temp _ -> set_lattice_val operand Undefined
    | _ -> set_lattice_val operand (Constant operand))
;;

let initialise_uses operand instr_id =
  Hashtbl.update operand_uses_tbl operand ~f:(fun uses_opt ->
    match uses_opt with
    | None -> IdSet.of_list [ instr_id ]
    | Some x -> IdSet.add x instr_id)
;;

let initialise_arg_label operand instr_id =
  let label = Hashtbl.find_exn id_to_label instr_id in
  Hashtbl.set args_to_label ~key:operand ~data:label
;;

let initialise_arg_zero operand =
  Ssa.(
    match operand with
    | Temp x when Temp.get_version x = 0 -> promote_operand operand Overdefined
    | _ -> ())
;;

(* Warning: for any constants encountered, insert into lattice vals as constants *)
let initialise_instr instr instr_id =
  Ssa.(
    match instr with
    | Binop { lhs; rhs; dest; _ } ->
      initialise_lattice lhs;
      initialise_lattice rhs;
      initialise_lattice dest;
      initialise_arg_zero lhs;
      initialise_arg_zero rhs;
      initialise_arg_zero dest;
      initialise_uses lhs instr_id;
      initialise_uses rhs instr_id;
      initialise_arg_label dest instr_id
    | Mov { src; dest }
    | Movsx { src; dest }
    | Movzx { src; dest }
    | Mov_trunc { src; dest } ->
      initialise_lattice src;
      initialise_lattice dest;
      initialise_arg_zero src;
      initialise_arg_zero dest;
      initialise_uses src instr_id;
      initialise_arg_label dest instr_id
    | If { lhs; rhs; _ } ->
      initialise_lattice lhs;
      initialise_lattice rhs;
      initialise_arg_zero lhs;
      initialise_arg_zero rhs;
      initialise_uses lhs instr_id;
      initialise_uses rhs instr_id
    | Ret { src } ->
      initialise_lattice src;
      initialise_arg_zero src;
      initialise_uses src instr_id
    | CallF { dest; args; _ } ->
      List.iter args ~f:(fun arg ->
        initialise_lattice arg;
        initialise_arg_zero arg;
        initialise_uses arg instr_id);
      initialise_lattice dest;
      initialise_arg_zero dest;
      initialise_arg_label dest instr_id
    | Store { base; index; src; _ } ->
      initialise_lattice base;
      initialise_lattice index;
      initialise_lattice src;
      initialise_arg_zero base;
      initialise_arg_zero index;
      initialise_arg_zero src;
      initialise_uses base instr_id;
      initialise_uses index instr_id;
      initialise_uses src instr_id;
      set_operand_memoperation base;
      set_operand_memoperation index;
      set_operand_memoperation src
    | Load { base; index; dest; _ } ->
      initialise_lattice base;
      initialise_lattice index;
      initialise_lattice dest;
      initialise_arg_zero base;
      initialise_arg_zero index;
      initialise_arg_zero dest;
      initialise_uses base instr_id;
      initialise_uses index instr_id;
      set_operand_memoperation base;
      set_operand_memoperation index
    | Lea { base; index; dest; _ } ->
      initialise_lattice base;
      initialise_lattice index;
      initialise_lattice dest;
      initialise_arg_zero base;
      initialise_arg_zero index;
      initialise_arg_zero dest;
      set_operand_memoperation base;
      set_operand_memoperation index;
      initialise_uses base instr_id;
      initialise_uses index instr_id
    | Phi { args; dest } ->
      List.iter args ~f:(fun arg ->
        initialise_lattice arg;
        initialise_arg_zero arg;
        initialise_uses arg instr_id);
      initialise_lattice dest;
      initialise_arg_zero dest;
      initialise_arg_label dest instr_id
    | _ -> ())
;;

let initialise_tables root label_to_body =
  Hashtbl.clear id_to_instr;
  Hashtbl.clear label_to_ids;
  Hashtbl.clear id_to_label;
  Hashtbl.clear operand_uses_tbl;
  Hashtbl.clear operand_lattice_tbl;
  Hashtbl.clear block_executed_tbl;
  Hashtbl.clear operand_in_memoperation;
  Hashtbl.clear args_to_label;
  block_worklist := BlockSet.empty;
  variable_worklist := VarSet.empty;
  let counter = ref 0 in
  Hashtbl.iteri label_to_body ~f:(fun ~key:label ~data:instrs ->
    let instr_ids =
      List.fold_left instrs ~init:[] ~f:(fun acc instr ->
        counter := !counter + 1;
        Hashtbl.set id_to_instr ~key:!counter ~data:instr;
        Hashtbl.set id_to_label ~key:!counter ~data:label;
        initialise_instr instr !counter;
        !counter :: acc)
    in
    Hashtbl.set label_to_ids ~key:label ~data:(List.rev instr_ids));
  set_block_executable root;
  block_worklist := BlockSet.of_list [ root ]
;;

let get_filtered_args new_cfg old_cfg label args =
  let old_preds = CFG.pred old_cfg label in
  let old_pred_args = List.map2_exn old_preds args ~f:(fun x y -> x, y) in
  let new_preds = BlockSet.of_list (CFG.pred new_cfg label) in
  (* TODO: 
     Get the indexes of the args which are in new_preds but not in old preds?
     (ind, arg) --> ()
     new preds will not have some args because some edges no longer exist
  *)
  List.filter_map old_pred_args ~f:(fun (pred, arg) ->
    if BlockSet.mem new_preds pred then Some arg else None)
;;

let update_phi_instr instr label new_cfg old_cfg =
  Ssa.(
    match instr with
    | Phi { args; dest } ->
      Phi { args = get_filtered_args new_cfg old_cfg label args; dest }
    | _ -> instr)
;;

let replace_instr instr =
  Ssa.(
    match instr with
    | Binop { dest; lhs; rhs; op } ->
      (match get_lattice_val dest with
       | Overdefined ->
         Some
           (Binop
              { dest
              ; lhs = get_processed_lattice_val lhs
              ; rhs = get_processed_lattice_val rhs
              ; op
              })
       | Undefined -> failwith "why dest undefined here?"
       | Constant x ->
         if is_operand_in_memoperation dest then Some (Mov { dest; src = x }) else None)
    | Mov { dest; src } ->
      (match get_lattice_val dest with
       | Overdefined -> Some (Mov { dest; src = get_processed_lattice_val src })
       | Undefined -> failwith "why dest undefined binop?"
       | Constant x ->
         if is_operand_in_memoperation dest then Some (Mov { dest; src = x }) else None)
    | Movsx { dest; src } ->
      (match get_lattice_val dest with
       | Overdefined -> Some (Movsx { dest; src = get_processed_lattice_val src })
       | Undefined -> failwith "why dest undefined movsx?"
       | Constant x ->
         if is_operand_in_memoperation dest then Some (Mov { dest; src = x }) else None)
    | Movzx { dest; src } ->
      (match get_lattice_val dest with
       | Overdefined -> Some (Movzx { dest; src = get_processed_lattice_val src })
       | Undefined -> failwith "why dest undefined movzx?"
       | Constant x ->
         if is_operand_in_memoperation dest then Some (Mov { dest; src = x }) else None)
    | Mov_trunc { dest; src } ->
      (match get_lattice_val dest with
       | Overdefined -> Some (Mov_trunc { dest; src = get_processed_lattice_val src })
       | Undefined -> failwith "why dest undefined mov_trunc?"
       | Constant x ->
         if is_operand_in_memoperation dest then Some (Mov { dest; src = x }) else None)
    | Directive _ | Comment _ | Jump _ | Label _ | Ret_void | Nop -> Some instr
    | If _ -> Some instr
    | Ret { src } -> Some (Ret { src = get_processed_lattice_val src })
    | CallF { dest; ident; args; assign_res } ->
      Some
        (CallF
           { dest
           ; ident
           ; assign_res
           ; args = List.map args ~f:(fun arg -> get_processed_lattice_val arg)
           })
    | Store _ ->
      (* Probably keep store as itself, 
       since it needs the stuff to be in registers *)
      Some instr
    | Load _ ->
      (* Probably keep load as itself, 
         since it needs the stuff to be in registers *)
      Some instr
    | Phi { args; dest } ->
      (match get_lattice_val dest with
       | Overdefined ->
         Some
           (Phi
              { dest; args = List.map args ~f:(fun arg -> get_processed_lattice_val arg) })
       | Undefined -> failwith "why is dest undefined phi?"
       | Constant x ->
         if is_operand_in_memoperation dest
         then Some (Phi { dest; args = List.map args ~f:(fun _ -> x) })
         else None)
    | Cmp _ -> failwith "no cmp!!!"
    | Lea { disp; base; index; scale; dest } ->
      (match get_lattice_val dest with
       | Overdefined -> Some (Lea { disp; base; index; scale; dest })
       | Undefined -> failwith "why is dest undefined lea?"
       | Constant x ->
         if is_operand_in_memoperation x
         then
           Some
             (Lea
                { disp
                ; base = get_processed_lattice_val base
                ; index = get_processed_lattice_val index
                ; scale
                ; dest
                })
         else None))
;;

let update_blocks cfg label_to_body =
  let labels = Hashtbl.keys label_to_body in
  let filtered_labels =
    List.filter_map labels ~f:(fun label ->
      if not (is_block_executable label)
      then (
        CFG.remove_vertex cfg label;
        None)
      else Some label)
  in
  BlockSet.of_list filtered_labels
;;

let rebuild_cfg_instr instr label new_cfg =
  CFG.add_vertex new_cfg label;
  Ssa.(
    match instr with
    | Jump succ_label -> CFG.add_edge new_cfg label succ_label
    | If { lt; lf; _ } ->
      CFG.add_edge new_cfg label lt;
      CFG.add_edge new_cfg label lf
    | _ -> ())
;;

(* Call on all the instruction ids *)
let update_cfg_ifs instr =
  Ssa.(
    match instr with
    | If { lhs; rhs; condition; lt; lf } ->
      let processed_res = process_if lhs rhs condition in
      (match processed_res with
       | Undefined -> failwith "why processed_res undefined if?"
       | Overdefined ->
         let lhs = get_processed_lattice_val lhs in
         let rhs = get_processed_lattice_val rhs in
         update_if lhs rhs condition lt lf
       | Constant x ->
         (match x with
          | Imm x' when Int32.(x' = one) -> Jump lt
          | Imm x' when Int32.(x' = zero) -> Jump lf
          | _ -> failwith "result of if evaluation only 1 or 0"))
    | _ -> instr)
;;

(* Can only call after the instructions for jumps have been replaced *)
let rebuild_control_flow new_cfg =
  let executable_blocks = Hashtbl.keys block_executed_tbl in
  let executable_blocks_set = BlockSet.of_list executable_blocks in
  Hashtbl.iteri label_to_ids ~f:(fun ~key:label ~data:instr_ids ->
    if not (BlockSet.mem executable_blocks_set label)
    then ()
    else
      List.iter instr_ids ~f:(fun instr_id ->
        let instr = Hashtbl.find_exn id_to_instr instr_id in
        rebuild_cfg_instr instr label new_cfg))
;;

let update_instructions new_cfg old_cfg label_to_body =
  let rem_labels = update_blocks new_cfg label_to_body in
  Hashtbl.mapi_inplace id_to_instr ~f:(fun ~key:id ~data:instr ->
    let id_label = Hashtbl.find_exn id_to_label id in
    if not (BlockSet.mem rem_labels id_label) then instr else update_cfg_ifs instr);
  rebuild_control_flow new_cfg;
  Hashtbl.filter_mapi label_to_ids ~f:(fun ~key:label ~data:instr_ids ->
    if not (BlockSet.mem rem_labels label)
    then None
    else (
      let mapped_instrs =
        List.filter_map instr_ids ~f:(fun instr_id ->
          let instr = Hashtbl.find_exn id_to_instr instr_id in
          let instr' = update_phi_instr instr label new_cfg old_cfg in
          replace_instr instr')
      in
      Some mapped_instrs))
;;

let sccp (cfg_orig, root_orig, label_to_body, labels_in_order) =
  (* Printf.printf "\ngraph before sccp\n";
  Abstrtossa.print_label_to_body label_to_body; *)
  (* Dot.output_graph
    (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_old_cfg.txt" root_orig))
    cfg_orig; *)
  initialise_tables root_orig label_to_body;
  while
    (not (BlockSet.is_empty !block_worklist)) || not (VarSet.is_empty !variable_worklist)
  do
    if not (BlockSet.is_empty !block_worklist) then process_block_worklist cfg_orig;
    if not (VarSet.is_empty !variable_worklist) then process_var_worklist cfg_orig
  done;
  let new_cfg = CFG.create () in
  (* Printf.printf "\n\n\n operand to definition:";
  Hashtbl.iteri operand_lattice_tbl ~f:(fun ~key ~data ->
    Printf.printf "%s %s\n" (Ssa.format_operand key) (formatTau data));
  Printf.printf "\n\n\n"; *)
  let new_label_to_bodies = update_instructions new_cfg cfg_orig label_to_body in
  let filtered_labels =
    List.filter labels_in_order ~f:(fun label -> CFG.mem_vertex new_cfg label)
  in
  (* Printf.printf "\ngraph after sccp\n";
  Abstrtossa.print_label_to_body new_label_to_bodies;
  Printf.printf "\ngraph after sccp end\n"; *)
  (* Dot.output_graph
    (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_new_cfg.txt" root_orig))
    new_cfg; *)
  new_cfg, root_orig, new_label_to_bodies, filtered_labels
;;
