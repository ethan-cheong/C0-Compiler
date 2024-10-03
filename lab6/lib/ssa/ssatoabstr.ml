(* L5 Compiler
 * Convert SSA procedure to 3-addr abstr assem procedure. 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Algorithms adapted from Chapter 19 of Modern Compiler Implementation (Appel)
 *)
open Core
module ThreeAS = Threeaddrassem
module CFG = Cfg.CFG
module Dot = Cfg.Dot

let ssa_to_abstr (cfg, root, label_to_bodies, labels_in_order) ~print_cfg =
  (* Printf.printf "\ngraph at the end\n";
  Abstrtossa.print_label_to_body label_to_bodies; *)
  CFG.iter_vertex
    (fun v ->
      let body_opt = Hashtbl.find label_to_bodies v in
      match body_opt with
      | None -> ()
      | Some body ->
        let new_body =
          List.filter_map
            ~f:(fun instr ->
              match instr with
              (* For phi functions, for each argi insert the mov dest <- argi at the end of 
           the ith predecessor. *)
              | Ssa.Phi { args; dest } ->
                (* List may not be in order...? *)
                List.iteri
                  ~f:(fun i argi ->
                    let pred =
                      match List.nth (CFG.pred cfg v) i with
                      | None ->
                        Printf.printf "%s pred dont match\n" v;
                        failwith "nth exception"
                      | Some x -> x
                    in
                    (* let pred = List.nth_exn (CFG.pred cfg v) i in *)
                    let prev_pred_body = Hashtbl.find_exn label_to_bodies pred in
                    let new_pred_body =
                      match List.rev prev_pred_body with
                      | If { lhs; rhs; condition; lt; lf } :: tl ->
                        List.rev
                          Ssa.(
                            [ If { lhs; rhs; condition; lt; lf }
                            ; Mov { src = argi; dest }
                            ]
                            @ tl)
                      | Jump l :: tl ->
                        List.rev Ssa.([ Jump l; Mov { src = argi; dest } ] @ tl)
                      (* | Nop :: _ -> [ Nop ] *)
                      | _ ->
                        Printf.printf "label: %s\n" pred;
                        List.iter prev_pred_body ~f:(fun x ->
                          Printf.printf "%s" (Ssa.format_instr x));
                        Printf.printf "end\n\n";
                        failwith
                          "basic block structure not preserved in ssa body before \
                           converting back to 3as (this might be a problem after we \
                           optimize)."
                    in
                    Hashtbl.set label_to_bodies ~key:pred ~data:new_pred_body)
                  args;
                None
              | _ -> Some instr)
            body
        in
        Hashtbl.set label_to_bodies ~key:v ~data:new_body)
    cfg;
  (* Convert mapping to ThreeAS list *)
  (* Always start with the root so that the correct basic block starts when 
   entering a function *)
  (* if print_cfg
  then
    Dot.output_graph
      (Stdlib.open_out (Printf.sprintf "./cfg_outputs/%s_after.txt" root))
      cfg; *)
  let init =
    Hashtbl.find_and_remove label_to_bodies root
    |> Option.value_exn
    |> List.map ~f:ThreeAS.instr_of_ssa
  in
  if print_cfg then Printf.printf "labels in order after:\n";
  let ordered_instrs =
    List.filter_map (List.rev labels_in_order) ~f:(fun label ->
      match Hashtbl.find label_to_bodies label with
      | None -> None
      | Some instrs ->
        if print_cfg then Printf.printf "%s\n" label;
        Some (ThreeAS.Label label :: List.map ~f:ThreeAS.instr_of_ssa instrs))
  in
  init @ List.concat ordered_instrs
;;
(* 
  Hashtbl.fold label_to_bodies ~init ~f:(fun ~key:label ~data:body acc ->
    List.append acc (ThreeAS.Label label :: List.map ~f:ThreeAS.instr_of_ssa body)) *)
