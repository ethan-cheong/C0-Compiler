open Core
module ThreeAS = Threeaddrassem
module Dominator = Cfg.Dominator
module CFG = Cfg.CFG
module Dot = Cfg.Dot
module Node = CFG.Node
module Bfs = Cfg.Bfs
module VarTable = Type_modules.SSAVarTable
module IdSet = Set.Make (Int)
module EdgeSet = Set.Make (CFG.EdgePair)

let sign_extend (x : Int32.t) : Int64.t =
  let mask = Int64.of_int32 Int32.min_value in
  let extended = Int64.shift_left (Int64.of_int32 x) 32 in
  if Int64.(extended land mask <> Int64.zero)
  then Int64.(extended lor (Int64.of_int (-1) lsl 32))
  else extended
;;

let zero_extend (x : Int32.t) : Int64.t = Int64.(of_int32 x lor shift_left one 32)

module SSAEdge = struct
  type t = int * int [@@deriving sexp, hash, equal, compare]
end

module SSAEdgeSet = Set.Make (SSAEdge)

type valTau =
  | Undefined
  | Constant of Ssa.operand
  | Overdefined

type blockTau =
  | Executable
  | Unexecuted

type edgeTau =
  | EdgeUnexecuted
  | EdgeExecuted

let is_temp =
  Ssa.(
    function
    | Temp _ -> true
    | _ -> false)
;;

(* Assume everything is int64 then the value is casted back? *)
let evaluate_binop lhs rhs op =
  Ssa.(
    match op with
    | Add -> Int64.(lhs + rhs), true
    | Sub -> Int64.(lhs - rhs), true
    | Mul -> Int64.(lhs * rhs), true
    | Div -> if Int64.(rhs = Int64.zero) then lhs, false else Int64.(lhs / rhs), true
    | Mod -> if Int64.(rhs = Int64.zero) then lhs, false else Int64.(lhs % rhs), true
    | Or -> Int64.(lhs lor rhs), true
    | Xor -> Int64.(lhs lxor rhs), true
    | And -> Int64.(lhs land rhs), true
    | Sal -> Int64.(lhs lsl to_int_trunc rhs), true
    | Sar -> Int64.(shift_right lhs (to_int_trunc rhs)), true
    | Shr -> Int64.(shift_right_logical lhs (to_int_trunc rhs)), true)
;;

let taus_are_equal lhs rhs =
  match lhs, rhs with
  | Undefined, Undefined -> true
  | Overdefined, Overdefined -> true
  | Constant x, Constant y when Ssa.compare_operand x y = 0 -> true
  | _ -> false
;;

let can_evaluate_operation lhs rhs op =
  match lhs, rhs with
  (* Not sure if there will be a case of undefined for both *)
  | Undefined, _ -> Undefined, false
  | _, Undefined -> Undefined, false
  | Overdefined, _ -> Overdefined, false
  | _, Overdefined -> Overdefined, false
  | Constant x, Constant y ->
    (match x, y with
     (* For binops, only if they are the same type? *)
     | Imm x', Imm y' ->
       let res, can_evaluate =
         evaluate_binop (Int64.of_int32 x') (Int64.of_int32 y') op
       in
       if can_evaluate
       then Constant (Imm (Int32.of_int64_trunc res)), true
       else Overdefined, false
     | Addr_imm x', Addr_imm y' ->
       let res, can_evaluate = evaluate_binop x' y' op in
       if can_evaluate then Constant (Addr_imm res), true else Overdefined, false
     | MAX_INT, MAX_INT ->
       let res, can_evaluate =
         evaluate_binop
           (Int64.of_int32 Int32.max_value)
           (Int64.of_int32 Int32.max_value)
           op
       in
       if can_evaluate
       then Constant (Imm (Int32.of_int64_trunc res)), true
       else Overdefined, false
     | Imm x', MAX_INT ->
       let res, can_evaluate =
         evaluate_binop (Int64.of_int32 x') (Int64.of_int32 Int32.max_value) op
       in
       if can_evaluate
       then Constant (Imm (Int32.of_int64_trunc res)), true
       else Overdefined, false
     | MAX_INT, Imm y' ->
       let res, can_evaluate =
         evaluate_binop (Int64.of_int32 Int32.max_value) (Int64.of_int32 y') op
       in
       if can_evaluate
       then Constant (Imm (Int32.of_int64_trunc res)), true
       else Overdefined, false
     | _ -> failwith "how did we end up here?")
;;

let is_executed edge cfg_edge_table =
  match Hashtbl.find cfg_edge_table edge with
  | None -> false
  | Some x -> x
;;

(* Instr_ID -> Operand -> Type *)
let mark_lattice_val operand instr_id lattice_table (tau : valTau) =
  let to_update =
    match Hashtbl.find lattice_table instr_id with
    | None ->
      let x = VarTable.create () in
      Hashtbl.set lattice_table ~key:instr_id ~data:x;
      x
    | Some x -> x
  in
  VarTable.set to_update ~key:operand ~data:tau
;;

(* Use this to set the lattic values for each operand. 
   Assume that every operand is undefined, even constants?
   Since those constants can be changed back anyway
   And if it's in SSA form/initialised correctly, there's no concern about them being assigned *)
let mark_vals_init instr instr_id lattice_table =
  Ssa.(
    match instr with
    | Binop { dest; lhs; rhs; _ } ->
      mark_lattice_val dest instr_id lattice_table Undefined;
      mark_lattice_val lhs instr_id lattice_table Undefined;
      mark_lattice_val rhs instr_id lattice_table Undefined
    | Mov { dest; src }
    | Movsx { dest; src }
    | Movzx { dest; src }
    | Mov_trunc { dest; src } ->
      mark_lattice_val dest instr_id lattice_table Undefined;
      mark_lattice_val src instr_id lattice_table Undefined
    | Cmp _ -> failwith "won't see a compare in ssa"
    | If { lhs; rhs; _ } ->
      mark_lattice_val lhs instr_id lattice_table Undefined;
      mark_lattice_val rhs instr_id lattice_table Undefined
    | Ret { src } -> mark_lattice_val src instr_id lattice_table Undefined
    | CallF { dest; args; _ } ->
      mark_lattice_val dest instr_id lattice_table Undefined;
      List.iter args ~f:(fun arg -> mark_lattice_val arg instr_id lattice_table Undefined)
    | Store { base; index; src; _ } ->
      mark_lattice_val base instr_id lattice_table Undefined;
      mark_lattice_val index instr_id lattice_table Undefined;
      mark_lattice_val src instr_id lattice_table Undefined
    | Load { base; index; dest; _ } ->
      mark_lattice_val base instr_id lattice_table Undefined;
      mark_lattice_val index instr_id lattice_table Undefined;
      mark_lattice_val dest instr_id lattice_table Undefined
    | Lea { base; index; dest; _ } ->
      mark_lattice_val base instr_id lattice_table Undefined;
      mark_lattice_val index instr_id lattice_table Undefined;
      mark_lattice_val dest instr_id lattice_table Undefined
    | Phi { dest; args } ->
      mark_lattice_val dest instr_id lattice_table Undefined;
      List.iter args ~f:(fun arg -> mark_lattice_val arg instr_id lattice_table Undefined)
    | Directive _ | Comment _ | Jump _ | Label _ | Ret_void | Nop -> ())
;;

(* let phi_to_label label_to_body =
  let phi_label_table = VarTable.create () in
  Hashtbl.iteri
    label_to_body
    ~f:(fun ~key:label ~data:instrs ->
      List.iter instrs ~f:(fun instr ->
        Ssa.(
          match instr with
          | Phi { dest; _ } -> Hashtbl.set phi_label_table ~key:dest ~data:label
          | _ -> ())))
    phi_label_table
;; *)

let add_phi_to_def phi_to_def instr_id phi =
  VarTable.set phi_to_def ~key:phi ~data:instr_id
;;

let add_phi_to_uses phi_to_uses instr_id phi =
  VarTable.update phi_to_uses phi ~f:(fun opt ->
    match opt with
    | None -> IdSet.of_list [ instr_id ]
    | Some x -> IdSet.add x instr_id)
;;

let initialise_tables label_to_bodies =
  let phi_to_def = VarTable.create () in
  let phi_to_uses = VarTable.create () in
  let lattice_values = Hashtbl.create (module Int) in
  (* instr id to value to tau *)
  let id_to_instr = Hashtbl.create (module Int) in
  let label_to_ids = Hashtbl.create (module String) in
  let id_to_label = Hashtbl.create (module Int) in
  let conditional_lattice_values = Hashtbl.create (module Int) in
  let counter = ref 0 in
  Hashtbl.iteri label_to_bodies ~f:(fun ~key:label ~data:instrs ->
    let instr_ids = ref [] in
    List.iter instrs ~f:(fun instr ->
      counter := !counter + 1;
      instr_ids := !counter :: !instr_ids;
      Hashtbl.set id_to_instr ~key:!counter ~data:instr;
      Hashtbl.set id_to_label ~key:!counter ~data:label;
      Ssa.(
        (* Values which are not temps should be stored in the lattices *)
        mark_vals_init instr !counter lattice_values;
        match instr with
        | Phi { dest; args } ->
          add_phi_to_def phi_to_def !counter dest;
          List.iter args ~f:(fun arg -> add_phi_to_uses phi_to_uses !counter arg)
        | Binop { dest; lhs; rhs; _ } ->
          if is_temp lhs
          then add_phi_to_uses phi_to_uses !counter lhs
          else mark_lattice_val lhs !counter lattice_values (Constant lhs);
          if is_temp rhs
          then add_phi_to_uses phi_to_uses !counter rhs
          else mark_lattice_val rhs !counter lattice_values (Constant rhs);
          add_phi_to_def phi_to_def !counter dest
        | Mov { src; dest }
        | Movsx { src; dest }
        | Movzx { src; dest }
        | Mov_trunc { src; dest } ->
          if is_temp src
          then add_phi_to_uses phi_to_uses !counter src
          else mark_lattice_val src !counter lattice_values (Constant src);
          add_phi_to_def phi_to_def !counter dest
        | If { lhs; rhs; _ } ->
          if is_temp lhs
          then add_phi_to_uses phi_to_uses !counter lhs
          else mark_lattice_val lhs !counter lattice_values (Constant lhs);
          if is_temp rhs
          then add_phi_to_uses phi_to_uses !counter rhs
          else mark_lattice_val rhs !counter lattice_values (Constant rhs);
          Hashtbl.set conditional_lattice_values ~key:!counter ~data:Undefined
        | Ret { src } -> if is_temp src then add_phi_to_uses phi_to_uses !counter src
        | CallF { args; dest; assign_res; _ } ->
          List.iter args ~f:(fun arg ->
            if is_temp arg
            then add_phi_to_uses phi_to_uses !counter arg
            else mark_lattice_val arg !counter lattice_values (Constant arg));
          if assign_res then add_phi_to_def phi_to_def !counter dest
        | Store { base; index; src; _ } ->
          if is_temp base
          then add_phi_to_uses phi_to_uses !counter base
          else mark_lattice_val base !counter lattice_values (Constant base);
          if is_temp index
          then add_phi_to_uses phi_to_uses !counter index
          else mark_lattice_val index !counter lattice_values (Constant index);
          if is_temp src
          then add_phi_to_uses phi_to_uses !counter src
          else mark_lattice_val src !counter lattice_values (Constant src)
        | Load { base; index; dest; _ } ->
          if is_temp base
          then add_phi_to_uses phi_to_uses !counter base
          else mark_lattice_val base !counter lattice_values (Constant base);
          if is_temp index
          then add_phi_to_uses phi_to_uses !counter index
          else mark_lattice_val index !counter lattice_values (Constant index);
          add_phi_to_def phi_to_def !counter dest
        | Lea { base; index; dest; _ } ->
          if is_temp base
          then add_phi_to_uses phi_to_uses !counter base
          else mark_lattice_val base !counter lattice_values (Constant base);
          if is_temp index
          then add_phi_to_uses phi_to_uses !counter index
          else mark_lattice_val index !counter lattice_values (Constant index);
          add_phi_to_def phi_to_def !counter dest
        | Directive _ | Comment _ | Jump _ | Label _ | Ret_void | Nop -> ()
        | Cmp _ -> failwith "no compares!");
      Hashtbl.set label_to_ids ~key:label ~data:!instr_ids));
  ( id_to_instr
  , label_to_ids
  , id_to_label
  , phi_to_uses
  , phi_to_def
  , lattice_values
  , conditional_lattice_values )
;;

let initialise_cfg_worklist root =
  let cfg_worklist = ref EdgeSet.empty in
  (* CFG.iter_succ
    (fun succ -> cfg_worklist := EdgeSet.add !cfg_worklist (root, succ))
    cfg
    root; *)
  let entry_node = "entry_node" in
  cfg_worklist := EdgeSet.add !cfg_worklist (entry_node, root);
  cfg_worklist
;;

let is_only_edge_executed edge cfg cfg_edge_table =
  let src, dest = edge in
  let preds = CFG.pred cfg dest in
  let rec helper preds =
    match preds with
    | [] -> true
    | h :: t ->
      if String.(src = h)
      then helper t
      else if is_executed (h, dest) cfg_edge_table
      then false
      else helper t
  in
  helper preds
;;

let dest_is_phi dest_id id_to_instr =
  Ssa.(
    match Hashtbl.find_exn id_to_instr dest_id with
    | Phi _ -> true
    | _ -> false)
;;

let dest_is_assignment dest_id id_to_instr =
  Ssa.(
    match Hashtbl.find_exn id_to_instr dest_id with
    | Binop _
    | Mov _
    | Movsx _
    | Movzx _
    | Mov_trunc _
    | Ret _
    | CallF _
    | Load _
    | Lea _
    | Store _ -> true (* Store not an assignment, but still consumes values *)
    | _ -> false)
;;

let get_dest_value target_val instr_id lattice_values =
  let instr = Hashtbl.find_exn lattice_values instr_id in
  Hashtbl.find_exn instr target_val
;;

let create_cfg_set dest phi_to_uses instr_id =
  let list_vals = IdSet.to_list (Hashtbl.find_exn phi_to_uses dest) in
  let list_edges = List.map list_vals ~f:(fun x -> instr_id, x) in
  SSAEdgeSet.of_list list_edges
;;

let get_lattice_val phi_val phi_to_def lattice_values =
  match phi_val with
  | Ssa.Temp _ ->
    let val_dest_line = Hashtbl.find_exn phi_to_def phi_val in
    get_dest_value phi_val val_dest_line lattice_values
  | x -> Constant x
;;

let evaluate_assign
  instr_id
  id_to_instr
  lattice_values
  phi_to_uses
  phi_to_def
  ssa_worklist
  =
  Ssa.(
    match Hashtbl.find_exn id_to_instr instr_id with
    | Binop { dest; lhs; rhs; op } ->
      let new_lhs_val = get_lattice_val lhs phi_to_def lattice_values in
      mark_lattice_val lhs instr_id lattice_values new_lhs_val;
      let new_rhs_val = get_lattice_val rhs phi_to_def lattice_values in
      mark_lattice_val rhs instr_id lattice_values new_rhs_val;
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value with
       | Overdefined -> ()
       | Undefined | Constant _ ->
         let evaluated_dest_value, _ =
           can_evaluate_operation new_lhs_val new_rhs_val op
         in
         if not (taus_are_equal evaluated_dest_value dest_value)
         then (
           mark_lattice_val dest instr_id lattice_values evaluated_dest_value;
           let out_edges = create_cfg_set dest phi_to_uses instr_id in
           ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
           (* Add all edges to worklist *)))
    | Mov { src; dest } ->
      let new_src_val = get_lattice_val src phi_to_def lattice_values in
      mark_lattice_val src instr_id lattice_values new_src_val;
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value, new_src_val with
       | Overdefined, _ -> ()
       | Undefined, Undefined -> ()
       | Constant _, Undefined -> failwith "constant <- undefined mov?"
       | Constant x, Constant y when Ssa.compare_operand x y = 0 -> ()
       | Constant _, Constant _ -> failwith "why the result different?"
       | Constant _, Overdefined | Undefined, _ ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    | Movsx { src; dest } ->
      let new_src_val = get_lattice_val src phi_to_def lattice_values in
      mark_lattice_val src instr_id lattice_values new_src_val;
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value, new_src_val with
       | Overdefined, _ -> ()
       | Undefined, Undefined -> ()
       | Constant _, Undefined -> failwith "constant <- undefined movsx?"
       | Constant x, Constant y when Ssa.compare_operand x y = 0 -> ()
       | Constant _, Constant _ -> failwith "why the result different movsx?"
       | Constant _, Overdefined ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
       | Undefined, Constant src_operand ->
         let src_int64 =
           match src_operand with
           | Imm x -> sign_extend x
           | MAX_INT -> sign_extend Int32.max_value
           | _ -> failwith "why?"
         in
         mark_lattice_val dest instr_id lattice_values (Constant (Addr_imm src_int64));
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
       | Undefined, _ ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    | Movzx { src; dest } ->
      let new_src_val = get_lattice_val src phi_to_def lattice_values in
      mark_lattice_val src instr_id lattice_values new_src_val;
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value, new_src_val with
       | Overdefined, _ -> ()
       | Undefined, Undefined -> ()
       | Constant _, Undefined -> failwith "constant <- undefined movzx?"
       | Constant x, Constant y when Ssa.compare_operand x y = 0 -> ()
       | Constant _, Constant _ -> failwith "why the result different movzx?"
       | Constant _, Overdefined ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
       | Undefined, Constant src_operand ->
         let src_int64 =
           match src_operand with
           | Imm x -> zero_extend x
           | MAX_INT -> zero_extend Int32.max_value
           | _ -> failwith "why?"
         in
         mark_lattice_val dest instr_id lattice_values (Constant (Addr_imm src_int64));
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
       | Undefined, _ ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    | Mov_trunc { src; dest } ->
      let new_src_val = get_lattice_val src phi_to_def lattice_values in
      mark_lattice_val src instr_id lattice_values new_src_val;
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value, new_src_val with
       | Overdefined, _ -> ()
       | Undefined, Undefined -> ()
       | Constant _, Undefined -> failwith "constant <- undefined mov_trunc?"
       | Constant x, Constant y when Ssa.compare_operand x y = 0 -> ()
       | Constant _, Constant _ -> failwith "why the result different mov_trunc?"
       | Constant _, Overdefined ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
       | Undefined, Constant src_operand ->
         let src_int32 =
           match src_operand with
           | Addr_imm x -> Int32.of_int64_trunc x
           | _ -> failwith "why?"
         in
         mark_lattice_val dest instr_id lattice_values (Constant (Imm src_int32));
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges
       | Undefined, _ ->
         mark_lattice_val dest instr_id lattice_values new_src_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    | Ret { src } ->
      let new_src_val = get_lattice_val src phi_to_def lattice_values in
      mark_lattice_val src instr_id lattice_values new_src_val
    | CallF { dest; args; assign_res; _ } ->
      List.iter args ~f:(fun arg ->
        let new_arg_val = get_lattice_val arg phi_to_def lattice_values in
        mark_lattice_val arg instr_id lattice_values new_arg_val);
      if assign_res
      then (
        (* mark as overdefined and then propagate the edges *)
        let new_dest_val = Overdefined in
        let dest_value = get_dest_value dest instr_id lattice_values in
        match dest_value with
        | Overdefined -> ()
        | Constant _ -> failwith "why callf give const?"
        | Undefined ->
          mark_lattice_val dest instr_id lattice_values new_dest_val;
          let out_edges = create_cfg_set dest phi_to_uses instr_id in
          ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    | Store { base; index; src; _ } ->
      let new_base_val = get_lattice_val base phi_to_def lattice_values in
      mark_lattice_val base instr_id lattice_values new_base_val;
      let new_index_val = get_lattice_val index phi_to_def lattice_values in
      mark_lattice_val index instr_id lattice_values new_index_val;
      let new_src_val = get_lattice_val src phi_to_def lattice_values in
      mark_lattice_val src instr_id lattice_values new_src_val
    | Load { base; index; dest; _ } ->
      let new_base_val = get_lattice_val base phi_to_def lattice_values in
      mark_lattice_val base instr_id lattice_values new_base_val;
      let new_index_val = get_lattice_val index phi_to_def lattice_values in
      mark_lattice_val index instr_id lattice_values new_index_val;
      let new_dest_val = Overdefined in
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value with
       | Overdefined -> ()
       | Constant _ -> failwith "why callf give const?"
       | Undefined ->
         mark_lattice_val dest instr_id lattice_values new_dest_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    | Lea { base; index; dest; _ } ->
      let new_base_val = get_lattice_val base phi_to_def lattice_values in
      mark_lattice_val base instr_id lattice_values new_base_val;
      let new_index_val = get_lattice_val index phi_to_def lattice_values in
      mark_lattice_val index instr_id lattice_values new_index_val;
      let new_dest_val = Overdefined in
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value with
       | Overdefined -> ()
       | Constant _ -> failwith "why callf give const?"
       | Undefined ->
         mark_lattice_val dest instr_id lattice_values new_dest_val;
         let out_edges = create_cfg_set dest phi_to_uses instr_id in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist out_edges)
    (* Technically can be evaluated...but fuck no *)
    | _ -> failwith "not an assign!")
;;

let evaluate_conditional_lhs_rhs_condition rhs lhs comparison =
  match lhs, rhs with
  | Overdefined, _ -> Overdefined
  | _, Overdefined -> Overdefined
  | Undefined, _ -> Undefined
  | _, Undefined -> Undefined
  | Constant x, Constant y ->
    Printf.printf
      "hi? %s %s %s\n"
      (Ssa.format_operand x)
      (Ssa.format_comparison comparison)
      (Ssa.format_operand y);
    let eval_res =
      match x, y with
      | Imm x', Imm y' ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(x' < y') then Int32.one else Int32.zero
           | Leq -> if Int32.(x' <= y') then Int32.one else Int32.zero
           | Gt -> if Int32.(x' > y') then Int32.one else Int32.zero
           | Geq -> if Int32.(x' >= y') then Int32.one else Int32.zero
           | Eq -> if Int32.(x' = y') then Int32.one else Int32.zero
           | Neq -> if Int32.(x' <> y') then Int32.one else Int32.zero))
      | MAX_INT, Imm y' ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(max_value < y') then Int32.one else Int32.zero
           | Leq -> if Int32.(max_value <= y') then Int32.one else Int32.zero
           | Gt -> if Int32.(max_value > y') then Int32.one else Int32.zero
           | Geq -> if Int32.(max_value >= y') then Int32.one else Int32.zero
           | Eq -> if Int32.(max_value = y') then Int32.one else Int32.zero
           | Neq -> if Int32.(max_value <> y') then Int32.one else Int32.zero))
      | Imm x', MAX_INT ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(x' < max_value) then Int32.one else Int32.zero
           | Leq -> if Int32.(x' <= max_value) then Int32.one else Int32.zero
           | Gt -> if Int32.(x' > max_value) then Int32.one else Int32.zero
           | Geq -> if Int32.(x' >= max_value) then Int32.one else Int32.zero
           | Eq -> if Int32.(x' = max_value) then Int32.one else Int32.zero
           | Neq -> if Int32.(x' <> max_value) then Int32.one else Int32.zero))
      | MAX_INT, MAX_INT ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(max_value < max_value) then Int32.one else Int32.zero
           | Leq -> if Int32.(max_value <= max_value) then Int32.one else Int32.zero
           | Gt -> if Int32.(max_value > max_value) then Int32.one else Int32.zero
           | Geq -> if Int32.(max_value >= max_value) then Int32.one else Int32.zero
           | Eq -> if Int32.(max_value = max_value) then Int32.one else Int32.zero
           | Neq -> if Int32.(max_value <> max_value) then Int32.one else Int32.zero))
      | Addr_imm x', Addr_imm y' ->
        Ssa.(
          (match comparison with
           | Lt -> if Int64.(x' < y') then Int32.one else Int32.zero
           | Leq -> if Int64.(x' <= y') then Int32.one else Int32.zero
           | Gt -> if Int64.(x' > y') then Int32.one else Int32.zero
           | Geq -> if Int64.(x' >= y') then Int32.one else Int32.zero
           | Eq -> if Int64.(x' = y') then Int32.one else Int32.zero
           | Neq -> if Int64.(x' <> y') then Int32.one else Int32.zero))
      | _ -> failwith "why did comparisons happen?"
    in
    Constant (Ssa.Imm eval_res)
;;

let evaluate_conditional
  instr_id
  id_to_instr
  lattice_values
  conditional_lattice_values
  phi_to_def
  cfg_worklist
  label
  cfg
  =
  Ssa.(
    match Hashtbl.find_exn id_to_instr instr_id with
    | If { lhs; rhs; condition; lt; lf } ->
      let lhs_tau = get_lattice_val lhs phi_to_def lattice_values in
      let rhs_tau = get_lattice_val rhs phi_to_def lattice_values in
      let evaluated_condition =
        evaluate_conditional_lhs_rhs_condition lhs_tau rhs_tau condition
      in
      let if_lattic_value = Hashtbl.find_exn conditional_lattice_values instr_id in
      (match if_lattic_value, evaluated_condition with
       | Overdefined, _ -> ()
       | Undefined, Undefined -> ()
       | _, Overdefined ->
         Hashtbl.set conditional_lattice_values ~key:instr_id ~data:Overdefined;
         (* get all the edges here *)
         CFG.iter_succ
           (fun succ -> cfg_worklist := EdgeSet.add !cfg_worklist (label, succ))
           cfg
           label
       | Constant _, Undefined -> failwith "why get undefined?"
       | Constant x, Constant y when Ssa.compare_operand x y <> 0 ->
         failwith "why get diff evaluation?"
       | Constant _, Constant _ -> () (* same constant, so ignore *)
       | Undefined, Constant x ->
         Hashtbl.set conditional_lattice_values ~key:instr_id ~data:(Constant x);
         (match x with
          | Imm x' when Int32.(x' = one) ->
            Printf.printf "one, %s\n\n" lt;
            cfg_worklist := EdgeSet.add !cfg_worklist (label, lt)
          | Imm x' when Int32.(x' <> one) ->
            Printf.printf "not one, %s\n\n" lf;
            cfg_worklist := EdgeSet.add !cfg_worklist (label, lf)
          | _ -> failwith "why not imm?"))
      (* If this instruction is evaluated, then it must be changed? *)
      (* Need to check if lhs and rhs *)
    | _ -> failwith "cant evaluate!")
;;

let evaluate_operands instr instr_id lattice_values id_to_label cfg_edge_table phi_to_def =
  Ssa.(
    match instr with
    | Phi { args; dest } ->
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value with
       | Overdefined -> ()
       | Undefined | Constant _ ->
         List.iter args ~f:(fun arg ->
           let arg_def_id = Hashtbl.find_exn phi_to_def arg in
           let arg_def_label = Hashtbl.find_exn id_to_label arg_def_id in
           let instr_label = Hashtbl.find_exn id_to_label instr_id in
           let cfg_edge = arg_def_label, instr_label in
           if is_executed cfg_edge cfg_edge_table
           then (
             let new_arg_val = get_dest_value arg arg_def_id lattice_values in
             (* (match new_arg_val with
              | Undefined -> Printf.printf "undefined\n\n"
              | Constant c -> Printf.printf "constant: %s\n" (Ssa.format_operand c)
              | _ -> failwith "not overdefiend"); *)
             mark_lattice_val arg instr_id lattice_values new_arg_val)))
    | _ -> failwith "not a phi function")
;;

let evaluate_result
  instr
  instr_id
  lattice_values
  id_to_label
  cfg_edge_table
  phi_to_def
  phi_to_uses
  ssa_worklist
  =
  Ssa.(
    match instr with
    | Phi { args; dest } ->
      let dest_value = get_dest_value dest instr_id lattice_values in
      (match dest_value with
       | Overdefined -> ()
       | Undefined | Constant _ ->
         let res_value =
           List.fold_left args ~init:Undefined ~f:(fun acc arg ->
             let arg_def_id = Hashtbl.find_exn phi_to_def arg in
             let arg_def_label = Hashtbl.find_exn id_to_label arg_def_id in
             let instr_label = Hashtbl.find_exn id_to_label instr_id in
             let executable = is_executed (arg_def_label, instr_label) cfg_edge_table in
             (* Need to check if it is executable. If it is, then need to account for it *)
             if executable
             then (
               let arg_tau = get_dest_value arg arg_def_id lattice_values in
               match arg_tau, acc with
               | Undefined, Constant _ -> acc
               | Overdefined, _ -> Overdefined
               | _, Overdefined -> Overdefined
               | Constant x, Constant y when Ssa.compare_operand x y = 0 -> acc
               | Constant _, Constant _ -> Overdefined
               | _, Undefined -> arg_tau)
             else acc)
         in
         mark_lattice_val dest instr_id lattice_values res_value;
         (* Iterate through all the stuff here... *)
         let phi_uses = IdSet.to_list (Hashtbl.find_exn phi_to_uses dest) in
         let phi_edges = List.map phi_uses ~f:(fun x -> instr_id, x) in
         ssa_worklist := SSAEdgeSet.union !ssa_worklist (SSAEdgeSet.of_list phi_edges))
    | _ -> failwith "not a phi function")
;;

let evaluate_phi
  dest_id
  id_to_instr
  lattice_values
  id_to_label
  cfg_edge_table
  phi_to_def
  phi_to_uses
  ssa_worklist
  =
  let instr = Hashtbl.find_exn id_to_instr dest_id in
  match instr with
  | Ssa.Phi _ ->
    evaluate_operands instr dest_id lattice_values id_to_label cfg_edge_table phi_to_def;
    evaluate_result
      instr
      dest_id
      lattice_values
      id_to_label
      cfg_edge_table
      phi_to_def
      phi_to_uses
      ssa_worklist
  | _ -> ()
;;

let evaluate_all_phis_in_block
  cfg_edge
  label_to_ids
  id_to_instr
  lattice_values
  id_to_label
  cfg_edge_table
  phi_to_def
  phi_to_uses
  ssa_worklist
  =
  let _, n = cfg_edge in
  let instr_ids = Hashtbl.find_exn label_to_ids n in
  List.iter instr_ids ~f:(fun instr_id ->
    let instr = Hashtbl.find_exn id_to_instr instr_id in
    match instr with
    | Ssa.Phi _ ->
      evaluate_operands
        instr
        instr_id
        lattice_values
        id_to_label
        cfg_edge_table
        phi_to_def
    | _ -> ());
  List.iter instr_ids ~f:(fun instr_id ->
    let instr = Hashtbl.find_exn id_to_instr instr_id in
    match instr with
    | Ssa.Phi _ ->
      evaluate_result
        instr
        instr_id
        lattice_values
        id_to_label
        cfg_edge_table
        phi_to_def
        phi_to_uses
        ssa_worklist
    | _ -> ())
;;

let get_updated_op op instr_id lattice_values =
  let op_tau = get_dest_value op instr_id lattice_values in
  match op_tau with
  | Undefined -> op
  | Overdefined -> op
  | Constant op' -> op'
;;

let replace_if lhs rhs condition lt lf instr_id conditional_lattice_values =
  match Hashtbl.find_exn conditional_lattice_values instr_id with
  | Overdefined -> Ssa.If { lhs; rhs; condition; lt; lf }
  | Undefined -> Ssa.If { lhs; rhs; condition; lt; lf }
  | Constant x ->
    Ssa.(
      (match x with
       | Imm x' when Int32.(x' = one) -> Ssa.Jump lt
       | Imm x' when Int32.(x' = zero) -> Ssa.Jump lf
       | _ -> failwith "only 1 or 0 allowed"))
;;

let update_instructions instr_id instr lattice_values conditional_lattice_values =
  Ssa.(
    match instr with
    | Binop { dest; lhs; rhs; op } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let lhs' = get_updated_op lhs instr_id lattice_values in
      let rhs' = get_updated_op rhs instr_id lattice_values in
      Binop { dest = dest'; lhs = lhs'; rhs = rhs'; op }
    | Mov { dest; src } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let src' = get_updated_op src instr_id lattice_values in
      Mov { dest = dest'; src = src' }
    | Movzx { dest; src } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let src' = get_updated_op src instr_id lattice_values in
      Movzx { dest = dest'; src = src' }
    | Movsx { dest; src } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let src' = get_updated_op src instr_id lattice_values in
      Movsx { dest = dest'; src = src' }
    | Mov_trunc { dest; src } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let src' = get_updated_op src instr_id lattice_values in
      Mov_trunc { dest = dest'; src = src' }
    | CallF { dest; ident; args; assign_res } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let args' =
        List.map args ~f:(fun arg -> get_updated_op arg instr_id lattice_values)
      in
      CallF { dest = dest'; ident; args = args'; assign_res }
    | Ret { src } ->
      let src' = get_updated_op src instr_id lattice_values in
      Ret { src = src' }
    | Store { disp; base; index; scale; src } ->
      let src' = get_updated_op src instr_id lattice_values in
      let base' = get_updated_op base instr_id lattice_values in
      let index' = get_updated_op index instr_id lattice_values in
      Store { disp; base = base'; index = index'; scale; src = src' }
    | Load { disp; base; index; scale; dest } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let base' = get_updated_op base instr_id lattice_values in
      let index' = get_updated_op index instr_id lattice_values in
      Load { disp; base = base'; index = index'; scale; dest = dest' }
    | Lea { disp; base; index; scale; dest } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let base' = get_updated_op base instr_id lattice_values in
      let index' = get_updated_op index instr_id lattice_values in
      Lea { disp; base = base'; index = index'; scale; dest = dest' }
    | Directive _ | Comment _ | Jump _ | Label _ | Ret_void | Nop -> instr
    | If { lhs; rhs; condition; lt; lf } ->
      replace_if lhs rhs condition lt lf instr_id conditional_lattice_values
    | Phi { args; dest } ->
      let dest' = get_updated_op dest instr_id lattice_values in
      let args' =
        List.map args ~f:(fun arg -> get_updated_op arg instr_id lattice_values)
      in
      Phi { dest = dest'; args = args' }
    | Cmp _ -> failwith "cmp not exist")
;;

let sccp (cfg, root, label_to_body, labels_in_order) =
  (* Printf.printf "\ngraph before sccp\n";
  Abstrtossa.print_label_to_body label_to_body; *)
  let ( id_to_instr
      , label_to_ids
      , id_to_label
      , phi_to_uses
      , phi_to_def
      , lattice_values
      , conditional_lattice_values )
    =
    initialise_tables label_to_body
  in
  let cfg_edge_table = Hashtbl.create (module CFG.EdgePair) in
  let cfg_worklist = initialise_cfg_worklist root in
  let ssa_worklist = ref SSAEdgeSet.empty in
  while
    (not (EdgeSet.is_empty !cfg_worklist)) || not (SSAEdgeSet.is_empty !ssa_worklist)
  do
    if not (EdgeSet.is_empty !cfg_worklist)
    then (
      Printf.printf "lol\n";
      let edge = EdgeSet.min_elt_exn !cfg_worklist in
      cfg_worklist := EdgeSet.remove !cfg_worklist edge;
      if not (is_executed edge cfg_edge_table)
      then (
        (* Printf.printf "edge: %s %s\n" (fst edge) (snd edge); *)
        Hashtbl.set cfg_edge_table ~key:edge ~data:true;
        evaluate_all_phis_in_block
          edge
          label_to_ids
          id_to_instr
          lattice_values
          id_to_label
          cfg_edge_table
          phi_to_def
          phi_to_uses
          ssa_worklist;
        (* Look through all the edges entering n *)
        if is_only_edge_executed edge cfg cfg_edge_table
        then (
          (* ????? do i iterate through all the instructions? *)
          let instrs = Hashtbl.find_exn label_to_ids (snd edge) in
          List.iter (List.rev instrs) ~f:(fun instr_id ->
            let instr = Hashtbl.find_exn id_to_instr instr_id in
            (* Printf.printf "hi %s\n\n\n" (Ssa.format_instr instr); *)
            match instr with
            | Binop _
            | Mov _
            | Movsx _
            | Movzx _
            | Mov_trunc _
            | Ret _
            | CallF _
            | Store _
            | Load _
            | Lea _ ->
              evaluate_assign
                instr_id
                id_to_instr
                lattice_values
                phi_to_uses
                phi_to_def
                ssa_worklist
            | If _ ->
              evaluate_conditional
                instr_id
                id_to_instr
                lattice_values
                conditional_lattice_values
                phi_to_def
                cfg_worklist
                (snd edge)
                cfg
            | Jump jump_label ->
              cfg_worklist := EdgeSet.add !cfg_worklist (snd edge, jump_label)
            | _ -> ()
            (* 
              Assignments include mov/binop/lea/load/callf
              Conditionals are only if
              Jump will be considered "assignment" in that the successor is considered
            *)))));
    if not (SSAEdgeSet.is_empty !ssa_worklist)
    then (
      (* Edges are id to id! *)
      Printf.printf "hi\n";
      SSAEdgeSet.iter !ssa_worklist ~f:(fun (x, y) ->
        Printf.printf
          "ssa edge: %s %s\n"
          (Ssa.format_instr (Hashtbl.find_exn id_to_instr x))
          (Ssa.format_instr (Hashtbl.find_exn id_to_instr y)));
      Printf.printf "bye\n";
      let edge = SSAEdgeSet.min_elt_exn !ssa_worklist in
      ssa_worklist := SSAEdgeSet.remove !ssa_worklist edge;
      let _, dest_id = edge in
      let dest_label = Hashtbl.find_exn id_to_label dest_id in
      (* Iterate through dest_label and find any executed *)
      let exists =
        Hashtbl.length
          (Hashtbl.filteri cfg_edge_table ~f:(fun ~key:(_, y) ~data:executed ->
             String.(y = dest_label) && executed))
        > 0
      in
      if exists
      then
        if dest_is_phi dest_id id_to_instr
        then
          (*Need to do include all the instructions*)
          evaluate_phi
            dest_id
            id_to_instr
            lattice_values
            id_to_label
            cfg_edge_table
            phi_to_def
            phi_to_uses
            ssa_worklist
        else if dest_is_assignment dest_id id_to_instr
        then
          evaluate_assign
            dest_id
            id_to_instr
            lattice_values
            phi_to_uses
            phi_to_def
            ssa_worklist
        else
          evaluate_conditional
            dest_id
            id_to_instr
            lattice_values
            conditional_lattice_values
            phi_to_def
            cfg_worklist
            dest_label
            cfg)
  done;
  (* Iterate through the instructions and replace the values in the binops accordingly *)
  Hashtbl.mapi_inplace id_to_instr ~f:(fun ~key:instr_id ~data:instr ->
    update_instructions instr_id instr lattice_values conditional_lattice_values);
  (* Now, delete the blocks which are unused *)
  (* How to delete blocks? Maybe just set unreachable blocks with nops? *)
  (* Build a new graph from all the edges that can be executed. Run BFS and add the vertices from root that are executable *)
  let temp_cfg = CFG.create () in
  Hashtbl.iteri cfg_edge_table ~f:(fun ~key:edge ~data:executed ->
    let a, b = edge in
    if executed then CFG.add_edge temp_cfg a b);
  CFG.add_vertex temp_cfg root;
  let only_accessible = CFG.create () in
  Bfs.iter_component (fun node -> CFG.add_vertex only_accessible node) temp_cfg root;
  (* BFS? *)
  let all_nodes = Hashtbl.copy label_to_ids in
  let filtered_nodes =
    Hashtbl.filter_keys all_nodes ~f:(fun node ->
      not (CFG.mem_vertex only_accessible node))
  in
  (* Delete the nodes which are filtered *)
  Hashtbl.iter_keys filtered_nodes ~f:(fun node -> CFG.remove_vertex only_accessible node);
  let labels_in_order' =
    List.filter labels_in_order ~f:(fun label -> CFG.mem_vertex only_accessible label)
  in
  let label_to_body' =
    Hashtbl.filter_keys label_to_body ~f:(fun label ->
      CFG.mem_vertex only_accessible label)
  in
  CFG.iter_edges
    (fun x y ->
      if CFG.mem_vertex only_accessible x && CFG.mem_vertex only_accessible y
      then CFG.add_edge only_accessible x y)
    cfg;
  (* Printf.printf "\ngraph at the end\n";
  Abstrtossa.print_label_to_body label_to_body'; *)
  only_accessible, root, label_to_body', labels_in_order'
;;
