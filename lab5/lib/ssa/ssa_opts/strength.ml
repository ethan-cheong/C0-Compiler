(* 
  Implement Strength Reduction 
  Source:
    Hacker’s Delight 2nd Edition Chapter 10
*)

open Core
module ThreeAS = Threeaddrassem
module IntMap = Map.Make (Int32)

let pow_two_map =
  let vals =
    List.map
      [ 0
      ; 1
      ; 2
      ; 3
      ; 4
      ; 5
      ; 6
      ; 7
      ; 8
      ; 9
      ; 10
      ; 11
      ; 12
      ; 13
      ; 14
      ; 15
      ; 16
      ; 17
      ; 18
      ; 19
      ; 20
      ; 21
      ; 22
      ; 23
      ; 24
      ; 25
      ; 26
      ; 27
      ; 28
      ; 29
      ; 30
      ]
      ~f:(fun x ->
      let exponent = Int32.(of_int_trunc x) in
      Int32.(pow (of_int_trunc 2) exponent, exponent))
  in
  IntMap.of_alist_exn vals
;;

let process_div dest lhs rhs =
  match rhs with
  | Ssa.Imm x ->
    (match IntMap.find pow_two_map x with
     | Some base -> Some Ssa.(Binop { dest; lhs; rhs = Imm base; op = Sar })
     | None -> None)
  | _ -> None
;;

let process_mod dest lhs rhs =
  match rhs with
  | Ssa.Imm x ->
    (match IntMap.find pow_two_map x with
     | Some _ ->
       let bits = Int32.(x - one) in
       Some Ssa.(Binop { dest; lhs; rhs = Imm bits; op = And })
     | None -> None)
  | _ -> None
;;

let check_lea dest lhs rhs =
  match lhs with
  | Ssa.Temp _ ->
    (match rhs with
     | Ssa.Imm x when Int32.(x = of_int_trunc 3) ->
       Some Ssa.(Lea { disp = Int32.zero; base = lhs; index = lhs; scale = 2; dest })
     | Ssa.Imm x when Int32.(x = of_int_trunc 5) ->
       Some Ssa.(Lea { disp = Int32.zero; base = lhs; index = lhs; scale = 4; dest })
     | Ssa.Imm x when Int32.(x = of_int_trunc 9) ->
       Some Ssa.(Lea { disp = Int32.zero; base = lhs; index = lhs; scale = 8; dest })
     | _ -> None)
  | _ -> None
;;

let process_mul dest lhs rhs =
  match rhs with
  | Ssa.Imm x ->
    (match IntMap.find pow_two_map x with
     | Some base -> Some Ssa.(Binop { dest; lhs; rhs = Imm base; op = Sal })
     | None ->
       (match check_lea dest lhs rhs with
        | None -> check_lea dest rhs lhs
        | Some x -> Some x))
  | _ -> None
;;

let update_binop dest lhs rhs op =
  Ssa.(
    match op with
    | Div -> process_div dest lhs rhs
    | Mod -> None
    | Mul ->
      (match process_mul dest lhs rhs with
       | Some x -> Some x
       | None -> process_mul dest rhs lhs)
    | _ -> None)
;;

let update_instr instr =
  Ssa.(
    match instr with
    | Binop { dest; lhs; rhs; op } ->
      (match update_binop dest lhs rhs op with
       | None -> instr
       | Some x -> x)
    | _ -> instr)
;;

let update_instrs instrs = List.map instrs ~f:(fun instr -> update_instr instr)

let strength (cfg_orig, root_orig, label_to_body, labels_in_order) =
  (* Printf.printf "\ngraph before strength\n";
  Abstrtossa.print_label_to_body label_to_body; *)
  let new_label_to_body =
    Hashtbl.map label_to_body ~f:(fun instrs -> update_instrs instrs)
  in
  (* Printf.printf "\ngraph after strength\n";
  Abstrtossa.print_label_to_body new_label_to_body; *)
  cfg_orig, root_orig, new_label_to_body, labels_in_order
;;
