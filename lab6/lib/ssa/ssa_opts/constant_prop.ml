(* L5 Compiler
 * Simple Constant Propagation
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>
 * Adapted from Modern Compiler Implementation (Appel)
 *)

open Core
module CFG = Cfg.CFG
module Node = CFG.Node
module VarTable = Type_modules.SSAVarTable
module IdSet = Set.Make (Int)

let id_to_instr = Hashtbl.create (module Int)
let label_to_ids = Hashtbl.create (module Node)
let id_to_label = Hashtbl.create (module Int)
let worklist = ref IdSet.empty

let operand_to_uses =
  VarTable.create () (* Operand must be temp, points to id of instructions *)
;;

let operand_to_def =
  VarTable.create () (* Operand must be temp, points to id of instruction *)
;;

let operand_in_mem = VarTable.create ()

let is_temp =
  Ssa.(
    function
    | Temp _ -> true
    | _ -> false)
;;

let is_temp_double operand =
  match operand with
  | Ssa.Temp t ->
    (match Temp.size t with
     | Temp.DOUBLE -> true
     | Temp.QUAD -> false)
  | _ -> false
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

(* After replacing operand, see if can process *)
let replace_operand instr operand constant =
  Ssa.(
    match instr with
    | Binop { dest; lhs; rhs; op } ->
      let lhs = if Ssa.compare_operand lhs operand = 0 then constant else lhs in
      let rhs = if Ssa.compare_operand rhs operand = 0 then constant else rhs in
      Binop { dest; lhs; rhs; op }
    | Mov { src; dest } ->
      let src = if Ssa.compare_operand src operand = 0 then constant else src in
      Mov { src; dest }
    | Movsx { src; dest } ->
      let src = if Ssa.compare_operand src operand = 0 then constant else src in
      Movsx { src; dest }
    | Movzx { src; dest } ->
      let src = if Ssa.compare_operand src operand = 0 then constant else src in
      Movzx { src; dest }
    | Mov_trunc { src; dest } ->
      let src = if Ssa.compare_operand src operand = 0 then constant else src in
      Mov_trunc { src; dest }
    | If { lhs; rhs; condition; lt; lf } ->
      let lhs = if Ssa.compare_operand lhs operand = 0 then constant else lhs in
      let rhs = if Ssa.compare_operand rhs operand = 0 then constant else rhs in
      If { lhs; rhs; condition; lt; lf }
    | Ret { src } ->
      let src = if Ssa.compare_operand src operand = 0 then constant else src in
      Ret { src }
    | Store { disp; base; index; scale; src } ->
      (* let base = if Ssa.compare_operand base operand = 0 then constant else base in
      let index = if Ssa.compare_operand index operand = 0 then constant else index in
      let src = if Ssa.compare_operand src operand = 0 then constant else src in *)
      Store { disp; base; index; scale; src }
    | Load { disp; base; index; scale; dest } ->
      (* let base = if Ssa.compare_operand base operand = 0 then constant else base in
      let index = if Ssa.compare_operand index operand = 0 then constant else index in
      let dest = if Ssa.compare_operand dest operand = 0 then constant else dest in *)
      Load { disp; base; index; scale; dest }
    | Lea { disp; base; index; scale; dest } ->
      (* let base = if Ssa.compare_operand base operand = 0 then constant else base in
      let index = if Ssa.compare_operand index operand = 0 then constant else index in
      let dest = if Ssa.compare_operand dest operand = 0 then constant else dest in *)
      Lea { disp; base; index; scale; dest }
    | CallF { dest; args; ident; assign_res } ->
      let args =
        List.map args ~f:(fun arg ->
          if Ssa.compare_operand arg operand = 0 then constant else arg)
      in
      CallF { dest; args; ident; assign_res }
    | Phi { dest; args } ->
      let args =
        List.map args ~f:(fun arg ->
          if Ssa.compare_operand arg operand = 0 then constant else arg)
      in
      Phi { dest; args }
    | _ -> instr)
;;

(* 
  Get defsite, usesites
  Delete operand_to_def
  Go id of instruction. Remove instruction with defsite
  Go through each use. Replace each operand instance with constant
  *)
let prop_constant operand constant =
  (* Printf.printf
    "propagating %s as %s\n"
    (Ssa.format_operand operand)
    (Ssa.format_operand constant); *)
  match Hashtbl.find operand_to_uses operand with
  | None -> ()
  | Some use_ids ->
    IdSet.iter use_ids ~f:(fun use_id ->
      Hashtbl.update id_to_instr use_id ~f:(fun x ->
        match x with
        | None ->
          Printf.printf
            "instr %s does not exist, used by %s\n"
            (string_of_int use_id)
            (Ssa.format_operand operand);
          failwith "instr should exist if id provided"
        | Some instr -> replace_operand instr operand constant))
;;

let add_to_def instr_id operand = VarTable.set operand_to_def ~key:operand ~data:instr_id

let add_to_uses instr_id operand =
  VarTable.update operand_to_uses operand ~f:(fun opt ->
    match opt with
    | None -> IdSet.of_list [ instr_id ]
    | Some x -> IdSet.add x instr_id)
;;

(* Only initialise the ones which will be used *)
let initialise_instr instr (instr_id : int) =
  Ssa.(
    match instr with
    | Phi { dest; args } ->
      if is_temp dest then add_to_def instr_id dest;
      List.iter args ~f:(fun arg -> if is_temp arg then add_to_uses instr_id arg)
    | Binop { dest; lhs; rhs; _ } ->
      if is_temp dest then add_to_def instr_id dest;
      if is_temp lhs then add_to_uses instr_id lhs;
      if is_temp rhs then add_to_uses instr_id rhs;
      if (not (is_temp lhs)) && not (is_temp rhs)
      then worklist := IdSet.add !worklist instr_id
    | Mov { src; dest }
    | Movsx { src; dest }
    | Movzx { src; dest }
    | Mov_trunc { src; dest } ->
      (* Only propagate if the dest is double! *)
      if not (is_temp_double dest)
      then ()
      else (
        if is_temp dest then add_to_def instr_id dest;
        if is_temp src
        then add_to_uses instr_id src
        else worklist := IdSet.add !worklist instr_id)
    | If { lhs; rhs; _ } ->
      if is_temp lhs then add_to_uses instr_id lhs;
      if is_temp rhs then add_to_uses instr_id rhs;
      if (not (is_temp lhs)) && not (is_temp rhs)
      then worklist := IdSet.add !worklist instr_id
    | Ret { src } -> if is_temp src then add_to_uses instr_id src
    | CallF { args; dest; assign_res; _ } ->
      List.iter args ~f:(fun arg -> if is_temp arg then add_to_uses instr_id arg);
      if assign_res then add_to_def instr_id dest
    | Store { base; index; src; _ } ->
      if is_temp base then add_to_uses instr_id base;
      if is_temp index then add_to_uses instr_id index;
      if is_temp src then add_to_uses instr_id src;
      VarTable.set operand_in_mem ~key:base ~data:();
      VarTable.set operand_in_mem ~key:index ~data:();
      VarTable.set operand_in_mem ~key:src ~data:()
    | Load { base; index; dest; _ } ->
      if is_temp base then add_to_uses instr_id base;
      if is_temp index then add_to_uses instr_id index;
      if is_temp dest then add_to_def instr_id dest;
      VarTable.set operand_in_mem ~key:base ~data:();
      VarTable.set operand_in_mem ~key:index ~data:();
      VarTable.set operand_in_mem ~key:dest ~data:()
    | Lea { base; index; dest; _ } ->
      if is_temp base then add_to_uses instr_id base;
      if is_temp index then add_to_uses instr_id index;
      if is_temp dest then add_to_def instr_id dest;
      VarTable.set operand_in_mem ~key:base ~data:();
      VarTable.set operand_in_mem ~key:index ~data:();
      VarTable.set operand_in_mem ~key:dest ~data:()
    | Directive _ | Comment _ | Jump _ | Label _ | Ret_void | Nop -> ()
    | Cmp _ -> failwith "no compares!")
;;

let sign_extend (x : Int32.t) : Int64.t =
  (*   
  let mask = Int64.of_int32 Int32.min_value in
  let extended = Int64.shift_left (Int64.of_int32 x) 32 in
  if Int64.(extended land mask <> Int64.zero)
  then Int64.(extended lor (Int64.of_int (-1) lsl 32))
  else extended *)
  Int64.of_int32 x
;;

let zero_extend (x : Int32.t) : Int64.t =
  let only_lower_32 = Int64.(shift_left one 32 - one) in
  Int64.(of_int32 x land only_lower_32)
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
    | Xor ->
      (* Printf.printf
        "%s %s %s\n"
        (Int32.to_string lhs)
        (Int32.to_string rhs)
        Int32.(to_string (lhs lxor rhs)); *)
      Int32.(lhs lxor rhs), true
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

let process_binop lhs rhs op =
  if is_temp lhs || is_temp rhs
  then None
  else
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

let process_mov src dest =
  if (not (is_temp src)) && is_temp_double dest then Some src else None
;;

let process_movsx _ =
  (* if not (is_temp src)
  then
    Some
      (match src with
       | Ssa.Imm x -> Ssa.Addr_imm (sign_extend x)
       | Ssa.MAX_INT -> Ssa.Addr_imm (sign_extend Int32.(~-one))
       | _ -> failwith "only imm or maxint")
  else None *)
  None
;;

let process_movzx _ =
  (* if not (is_temp src)
  then
    Some
      (match src with
       | Ssa.Imm x ->
         (* Printf.printf
           "zero extend: %s into %s\n"
           (Ssa.format_operand src)
           (Int64.to_string (zero_extend x)); *)
         Ssa.Addr_imm (zero_extend x)
       | Ssa.MAX_INT -> Ssa.Addr_imm (zero_extend Int32.(~-one))
       | _ -> failwith "only imm or maxint")
  else None *)
  None
;;

let process_mov_trunc src =
  if not (is_temp src)
  then
    Some
      (match src with
       | Ssa.Addr_imm x -> Ssa.Imm (Int32.of_int64_trunc x)
       | _ -> failwith "only addr imm allowed for truncation")
  else None
;;

let process_phi (args : Ssa.operand list) instr =
  let hd_opt = List.hd args in
  let hd =
    match hd_opt with
    | None ->
      Printf.printf "issues: %s\n" (Ssa.format_instr instr);
      failwith "???"
    | Some x -> x
  in
  List.fold_left args ~init:(Some hd) ~f:(fun acc arg ->
    match acc with
    | None -> None
    | Some acc_res ->
      if Ssa.compare_operand acc_res arg = 0 && not (is_temp arg)
      then Some acc_res
      else None)
;;

(* Delete the phis *)
let delete_phis succ_label pred_label preds =
  let pred_opt = List.findi preds ~f:(fun _ pred -> String.(pred = pred_label)) in
  let pred_index =
    match pred_opt with
    | None -> failwith "pred should have index"
    | Some x -> fst x
  in
  let instr_ids = Hashtbl.find_exn label_to_ids succ_label in
  List.iter instr_ids ~f:(fun instr_id ->
    match Hashtbl.find id_to_instr instr_id with
    | None -> ()
    | Some _ ->
      Hashtbl.update id_to_instr instr_id ~f:(fun instr_opt ->
        match instr_opt with
        | None ->
          (* Printf.printf
            "%s -> %s, getting succ_label instrs %s\n"
            pred_label
            succ_label
            (string_of_int instr_id); *)
          failwith "instr must exist if id exists when deleting phis"
        | Some instr ->
          (match instr with
           | Phi { dest; args } ->
             (* Printf.printf
               "deleting phi for %s, pred index is %s (%s -> %s)\n"
               (Ssa.format_instr instr)
               (string_of_int pred_index)
               pred_label
               succ_label; *)
             let new_args = List.filteri args ~f:(fun index _ -> index <> pred_index) in
             Phi { dest; args = new_args }
           | _ -> instr)))
;;

(* think recursively
  Base case:
    succ has a lot of children.contents
    delete_phis child succ_label cfg;   

*)
(* let rec delete_children_recursively succ_label pred_label cfg =
  if List.length (CFG.pred cfg succ_label) = 1
  then (
    let succ_children = CFG.succ cfg succ_label in
    let preds = List.map succ_children ~f:(fun child -> CFG.pred cfg child) in
    CFG.remove_vertex cfg succ_label;
    Hashtbl.remove label_to_ids succ_label;
    List.iter2_exn succ_children preds ~f:(fun child _ ->
      (* delete_phis child succ_label pred; *)
      delete_children_recursively child succ_label cfg))
  else (
    Printf.printf "deleting phi: %s -> %s\n" pred_label succ_label;
    let pred = CFG.pred cfg succ_label in
    delete_phis succ_label pred_label pred;
    CFG.remove_edge cfg pred_label succ_label)
;; *)

let delete_edge succ_label pred_label cfg =
  let pred = CFG.pred cfg succ_label in
  delete_phis succ_label pred_label pred;
  CFG.remove_edge cfg pred_label succ_label
;;

let process_if lhs rhs comparison lt lf =
  if is_temp lhs || is_temp rhs
  then None
  else (
    let res =
      match rhs, lhs with
      | Imm x', Imm y' ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(x' < y') then Jump lt, true else Jump lf, false
           | Leq -> if Int32.(x' <= y') then Jump lt, true else Jump lf, false
           | Gt -> if Int32.(x' > y') then Jump lt, true else Jump lf, false
           | Geq -> if Int32.(x' >= y') then Jump lt, true else Jump lf, false
           | Eq -> if Int32.(x' = y') then Jump lt, true else Jump lf, false
           | Neq -> if Int32.(x' <> y') then Jump lt, true else Jump lf, false))
      | MAX_INT, Imm y' ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(~-one < y') then Jump lt, true else Jump lf, false
           | Leq -> if Int32.(~-one <= y') then Jump lt, true else Jump lf, false
           | Gt -> if Int32.(~-one > y') then Jump lt, true else Jump lf, false
           | Geq -> if Int32.(~-one >= y') then Jump lt, true else Jump lf, false
           | Eq -> if Int32.(~-one = y') then Jump lt, true else Jump lf, false
           | Neq -> if Int32.(~-one <> y') then Jump lt, true else Jump lf, false))
      | Imm x', MAX_INT ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(x' < ~-one) then Jump lt, true else Jump lf, false
           | Leq -> if Int32.(x' <= ~-one) then Jump lt, true else Jump lf, false
           | Gt -> if Int32.(x' > ~-one) then Jump lt, true else Jump lf, false
           | Geq -> if Int32.(x' >= ~-one) then Jump lt, true else Jump lf, false
           | Eq -> if Int32.(x' = ~-one) then Jump lt, true else Jump lf, false
           | Neq -> if Int32.(x' <> ~-one) then Jump lt, true else Jump lf, false))
      | MAX_INT, MAX_INT ->
        Ssa.(
          (match comparison with
           | Lt -> if Int32.(~-one < ~-one) then Jump lt, true else Jump lf, false
           | Leq -> if Int32.(~-one <= ~-one) then Jump lt, true else Jump lf, false
           | Gt -> if Int32.(~-one > ~-one) then Jump lt, true else Jump lf, false
           | Geq -> if Int32.(~-one >= ~-one) then Jump lt, true else Jump lf, false
           | Eq -> if Int32.(~-one = ~-one) then Jump lt, true else Jump lf, false
           | Neq -> if Int32.(~-one <> ~-one) then Jump lt, true else Jump lf, false))
      | Addr_imm x', Addr_imm y' ->
        Ssa.(
          (match comparison with
           | Lt -> if Int64.(x' < y') then Jump lt, true else Jump lf, false
           | Leq -> if Int64.(x' <= y') then Jump lt, true else Jump lf, false
           | Gt -> if Int64.(x' > y') then Jump lt, true else Jump lf, false
           | Geq -> if Int64.(x' >= y') then Jump lt, true else Jump lf, false
           | Eq -> if Int64.(x' = y') then Jump lt, true else Jump lf, false
           | Neq -> if Int64.(x' <> y') then Jump lt, true else Jump lf, false))
      | _ -> failwith "why did comparisons happen?"
    in
    Some res)
;;

let update_usedef_worklist dest instr_id =
  match Hashtbl.find operand_to_uses dest with
  | None -> ()
  | Some uses_set ->
    worklist := IdSet.union !worklist uses_set;
    (match VarTable.find operand_in_mem dest with
     | Some _ -> ()
     | None ->
       Hashtbl.remove operand_to_def dest;
       Hashtbl.remove operand_to_uses dest;
       (* Printf.printf
         "removed %s, set as NOP %s\n"
         (string_of_int instr_id)
         (Ssa.format_instr (Hashtbl.find_exn id_to_instr instr_id)); *)
       Hashtbl.set id_to_instr ~key:instr_id ~data:Ssa.Nop)
;;

(* If process returns a result, then add it to worklist *)
let process_instr instr_id cfg =
  let instr = Hashtbl.find_exn id_to_instr instr_id in
  Ssa.(
    match instr with
    | Binop { dest; lhs; rhs; op } ->
      (match process_binop lhs rhs op with
       | None -> ()
       | Some res ->
         prop_constant dest res;
         update_usedef_worklist dest instr_id)
    | Mov { src; dest } ->
      (match process_mov src dest with
       | None -> ()
       | Some res ->
         prop_constant dest res;
         update_usedef_worklist dest instr_id)
    | Movsx { src; dest } ->
      (match process_movsx src with
       | None -> ()
       | Some res ->
         prop_constant dest res;
         update_usedef_worklist dest instr_id)
    | Movzx { src; dest } ->
      (match process_movzx src with
       | None -> ()
       | Some res ->
         prop_constant dest res;
         update_usedef_worklist dest instr_id)
    | Mov_trunc { src; dest } ->
      (match process_mov_trunc src with
       | None -> ()
       | Some res ->
         prop_constant dest res;
         update_usedef_worklist dest instr_id)
    | Phi { dest; args } ->
      (match process_phi args instr with
       | None -> ()
       | Some res ->
         prop_constant dest res;
         update_usedef_worklist dest instr_id)
    | If { lhs; rhs; condition; lt; lf } ->
      (* 
        In Some, since there are now jumps, we need to update the CFG
        Remove the edge of curr_label to lt/lf
        In current label, collect all the dests used into a set
        In phi functions in lt/lf, 
          filter and remove all instances of any dest if it were used
      *)
      (match process_if lhs rhs condition lt lf with
       | None -> ()
       | Some (res, remove_false) ->
         let curr_label = Hashtbl.find_exn id_to_label instr_id in
         if remove_false
         then delete_edge lf curr_label cfg
         else delete_edge lt curr_label cfg;
         Hashtbl.set id_to_instr ~key:instr_id ~data:res)
    | Lea _ | Load _ | Store _ | CallF _ ->
      () (* Nothing because they can't be propagated *)
    | Ret _ | Ret_void | Directive _ | Comment _ | Jump _ | Label _ | Nop -> ()
    | _ -> failwith "unimplemented")
;;

(* Need to remove edges and rebuild CFG *)
let scp (cfg_orig, root_orig, label_to_body, labels_in_order) =
  (* Printf.printf "\ngraph before scp\n";
  Abstrtossa.print_label_to_body label_to_body; *)
  Hashtbl.clear id_to_instr;
  Hashtbl.clear label_to_ids;
  Hashtbl.clear id_to_label;
  worklist := IdSet.empty;
  VarTable.clear operand_to_uses;
  VarTable.clear operand_to_def;
  VarTable.clear operand_in_mem;
  let counter = ref 0 in
  Hashtbl.iteri label_to_body ~f:(fun ~key:label ~data:instrs ->
    let instr_ids =
      List.fold_left instrs ~init:[] ~f:(fun acc instr ->
        counter := !counter + 1;
        initialise_instr instr !counter;
        Hashtbl.set id_to_instr ~key:!counter ~data:instr;
        Hashtbl.set id_to_label ~key:!counter ~data:label;
        !counter :: acc)
    in
    Hashtbl.set label_to_ids ~key:label ~data:instr_ids);
  while not (IdSet.is_empty !worklist) do
    let instr_id = IdSet.min_elt_exn !worklist in
    worklist := IdSet.remove !worklist instr_id;
    let instr_label = Hashtbl.find_exn id_to_label instr_id in
    if Hashtbl.mem label_to_ids instr_label then process_instr instr_id cfg_orig
  done;
  let label_to_body =
    Hashtbl.filter_keys label_to_body ~f:(fun label -> CFG.mem_vertex cfg_orig label)
  in
  let label_to_body =
    Hashtbl.mapi label_to_body ~f:(fun ~key:label ~data:_ ->
      let instr_ids = Hashtbl.find_exn label_to_ids label in
      List.filter_map (List.rev instr_ids) ~f:(fun instr_id ->
        let instr_opt = Hashtbl.find id_to_instr instr_id in
        match instr_opt with
        | None -> None
        | Some x ->
          Some
            (match x with
             | If { condition; lhs; rhs; lt; lf } -> update_if lhs rhs condition lt lf
             | _ -> x)))
  in
  let labels_in_order =
    List.filter labels_in_order ~f:(fun label -> CFG.mem_vertex cfg_orig label)
  in
  (* Printf.printf "\ngraph after scp\n";
  Abstrtossa.print_label_to_body label_to_body; *)
  cfg_orig, root_orig, label_to_body, labels_in_order
;;
