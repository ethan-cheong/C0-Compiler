(* L5 Compiler
 * Convert 3AS procedure to SSA procedure. 
 * Author: Ethan Cheong <echeong@andrew.cs.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Algorithms adapted from Chapter 19 of Modern Compiler Implementation (Appel)
 *)
open Core
module ThreeAS = Threeaddrassem
module Dominator = Cfg.Dominator
module CFG = Cfg.CFG
module Node = CFG.Node
module Dfs = Cfg.Dfs
module NodeSet = Set.Make (Node)
module TempSet = Set.Make (Temp)

(******************** Utility functions for debugging *************************)
(* let print_tempset (tempset : TempSet.t) =
  TempSet.fold tempset ~init:"" ~f:(fun acc t -> Temp.name t ^ acc)
;; *)
(* 
let print_nodeset (nodeset : NodeSet.t) =
  NodeSet.fold nodeset ~init:"" ~f:(fun acc t -> t ^ ", " ^ acc)
;; *)

(* let print_aorig (hashtbl : (Node.t, TempSet.t) Hashtbl.t) =
  Hashtbl.iteri hashtbl ~f:(fun ~key:k ~data:v ->
    Printf.printf "%s: %s\n" k.label (print_tempset v))
;; *)
(* 
let print_defsites_or_aphi (defsites : (Temp.t, NodeSet.t) Hashtbl.t) =
  Hashtbl.iteri defsites ~f:(fun ~key:k ~data:v ->
    Printf.printf "%s: %s\n" (Temp.name k) (print_nodeset v))
;; *)

let print_label_to_body tbl =
  Hashtbl.iteri tbl ~f:(fun ~key:label ~data:body ->
    Printf.printf
      "\n%s:%s\n"
      label
      (List.fold ~init:"" ~f:(fun acc instr -> acc ^ "\n" ^ Ssa.format_instr instr) body))
;;

(* 
let rec print_dom_tree indent n dom_tree =
  Printf.printf "%s%s\n" (n_times "    " indent) n;
  List.iter ~f:(fun item -> print_dom_tree (indent + 1) item dom_tree) (dom_tree n)

and n_times s n =
  match n with
  | 0 -> ""
  | _ -> s ^ n_times s (n - 1)
;; *)

(************************** Functions for converting to ssa *******************)

(** [extract_vars func] gives the set of temps in func, including function args. *)
let extract_vars (func : ThreeAS.func) =
  let args = (fst func).args in
  let init =
    List.fold args ~init:TempSet.empty ~f:(fun acc op ->
      match op with
      | ThreeAS.Temp t -> TempSet.add acc t
      | _ -> acc)
  in
  let body = snd func in
  List.fold body ~init ~f:(fun acc instr ->
    match instr with
    | ThreeAS.Binop { dest = Temp t; _ }
    | Mov { dest = Temp t; _ }
    | Movsx { dest = Temp t; _ }
    | Movzx { dest = Temp t; _ }
    | Mov_trunc { dest = Temp t; _ }
    | CallF { dest = Temp t; _ }
    | Load { dest = Temp t; _ }
    | Lea { dest = Temp t; _ } -> TempSet.add acc t
    | _ -> acc)
;;

let rec build_graph cfg orig curr_node seen_nodes =
  match Hashtbl.find seen_nodes curr_node with
  | Some _ -> ()
  | None ->
    Hashtbl.set seen_nodes ~key:curr_node ~data:true;
    CFG.add_vertex cfg curr_node;
    CFG.iter_succ
      (fun succ ->
        CFG.add_edge cfg curr_node succ;
        build_graph cfg orig succ seen_nodes)
      orig
      curr_node
;;

let only_main cfg root label_to_body =
  (* Printf.printf "\ngraph after renaming\n";
  print_label_to_body label_to_body; *)
  let cfg_filtered = CFG.create () in
  (* From root, iterate through the edges? *)
  let seen_nodes =
    Hashtbl.create
      ~growth_allowed:false
      ~size:(Hashtbl.length label_to_body)
      (module String)
  in
  build_graph cfg_filtered cfg root seen_nodes;
  let filtered_labels =
    Hashtbl.filter_keys label_to_body ~f:(fun key -> CFG.mem_vertex cfg_filtered key)
  in
  (* Printf.printf "\ngraph after filtering\n";
  print_label_to_body filtered_labels; *)
  cfg_filtered, root, filtered_labels
;;

let abstr_to_ssa (func : ThreeAS.func) ~print_cfg =
  let cfg, root, label_to_body, labels_in_order = Buildcfg.build_cfg ~print_cfg func in
  let cfg, root, label_to_body = only_main cfg root label_to_body in
  (* Printf.printf "\ngraph at start:\n";
  print_label_to_body label_to_body;
  Printf.printf "\n\n\n"; *)
  let vars = extract_vars func in
  (* Printf.printf " vars at start:\n";
  TempSet.iter vars ~f:(fun t -> Printf.printf "%s\n" (Temp.name t)); *)
  let get_body (label : string) : Ssa.instr list = Hashtbl.find_exn label_to_body label in
  let idom = Dominator.compute_idom cfg root in
  let dom_tree = Dominator.idom_to_dom_tree cfg idom in
  let df = Dominator.compute_dom_frontier cfg dom_tree idom in
  let defsites = Hashtbl.create ~growth_allowed:true ~size:64 (module Temp) in
  let a_orig = Hashtbl.create ~growth_allowed:true ~size:64 (module Node) in
  (* Algorithm to place phi functions. (Algorithm 19.6 in Appel, 1993) *)
  (* Get defsites: *)
  CFG.iter_vertex
    (fun n ->
      (* For each node n *)
      Hashtbl.set ~key:n ~data:TempSet.empty a_orig;
      List.iter (get_body n) ~f:(fun instr ->
        (* match defined variables *)
        match instr with
        | Ssa.Binop { dest = Temp t; _ }
        | Mov { dest = Temp t; _ }
        | Movsx { dest = Temp t; _ }
        | Movzx { dest = Temp t; _ }
        | Mov_trunc { dest = Temp t; _ }
        | CallF { dest = Temp t; _ }
        | Load { dest = Temp t; _ }
        | Lea { dest = Temp t; _ } ->
          let curr_a = Hashtbl.find_exn a_orig n in
          Hashtbl.set ~key:n ~data:(TempSet.add curr_a t) a_orig
          (* Fill up Aorig *)
        | _ -> ());
      let a_orig_n = Hashtbl.find_exn a_orig n in
      TempSet.iter a_orig_n ~f:(fun a ->
        let curr_defsites =
          Hashtbl.find_or_add defsites a ~default:(fun () -> NodeSet.empty)
        in
        Hashtbl.set defsites ~key:a ~data:(NodeSet.add curr_defsites n)))
    cfg;
  Hashtbl.iteri defsites ~f:(fun ~key:a ~data:defs ->
    (* For each variable a *)
    let phi_added = ref NodeSet.empty in
    let w = ref defs in
    while not (NodeSet.is_empty !w) do
      let n = NodeSet.min_elt_exn !w in
      w := NodeSet.remove !w n;
      List.iter (df n) ~f:(fun y ->
        if not (NodeSet.mem !phi_added y)
        then (
          (* add phi functions *)
          let n_preds = CFG.in_degree cfg y in
          let current_body = Hashtbl.find_exn label_to_body y in
          Hashtbl.set
            label_to_body
            ~key:y
            ~data:
              (Ssa.Phi
                 { dest = Temp a; args = List.init n_preds ~f:(fun _ -> Ssa.Temp a) }
               :: current_body);
          (* A phi [a] <- ... *)
          phi_added := NodeSet.add !phi_added y;
          if not (TempSet.mem (Hashtbl.find_exn a_orig y) a) then w := NodeSet.add !w y))
    done);
  (* Printf.printf "\ngraph after phi functions are added, before renaming\n";
  print_label_to_body label_to_body; *)
  (* Renaming variables (Algorithm 19.7 in Appel, 1993) *)
  let count =
    Hashtbl.create ~growth_allowed:false ~size:(TempSet.length vars) (module Temp)
  in
  let stack =
    Hashtbl.create ~growth_allowed:false ~size:(TempSet.length vars) (module Temp)
  in
  (* Helper functions for manipulating stack for variables *)
  let replace_use (op : Ssa.operand) =
    match op with
    | Temp x ->
      let i = List.hd_exn (Hashtbl.find_exn stack x) in
      let xi = Temp.make_version x i in
      (* Printf.printf "%s was used; replaced with %s\n" (Temp.name x) (Temp.name xi); *)
      Ssa.Temp xi
    | _ -> op
  in
  let replace_def (op : Ssa.operand) def_counter =
    match op with
    | Temp a ->
      let def_counts = Hashtbl.find_or_add def_counter a ~default:(fun () -> 0) in
      Hashtbl.set ~key:a ~data:(def_counts + 1) def_counter;
      Hashtbl.set ~key:a ~data:(Hashtbl.find_exn count a + 1) count;
      let i = Hashtbl.find_exn count a in
      Hashtbl.set ~key:a ~data:(i :: Hashtbl.find_exn stack a) stack;
      let ai = Temp.make_version a i in
      Ssa.Temp ai
    | _ -> op
  in
  TempSet.iter vars ~f:(fun a ->
    Hashtbl.set ~key:a ~data:0 count;
    Hashtbl.set ~key:a ~data:[ 0 ] stack);
  let rec rename n : unit =
    let body = get_body n in
    let defs = Hashtbl.create ~growth_allowed:true ~size:5 (module Temp) in
    let modified_body =
      List.map
        ~f:(fun instr ->
          match instr with
          | Ssa.Phi { dest; args } -> Ssa.Phi { dest = replace_def dest defs; args }
          (* Always replace uses before defs. *)
          | Binop { dest; lhs; op; rhs } ->
            let lhs = replace_use lhs in
            let rhs = replace_use rhs in
            let dest = replace_def dest defs in
            Ssa.Binop { lhs; rhs; dest; op }
          | Mov { dest; src } ->
            let src = replace_use src in
            let dest = replace_def dest defs in
            Mov { src; dest }
          | Movsx { dest; src } ->
            let src = replace_use src in
            let dest = replace_def dest defs in
            Movsx { src; dest }
          | Movzx { dest; src } ->
            let src = replace_use src in
            let dest = replace_def dest defs in
            Movzx { src; dest }
          | Mov_trunc { dest; src } ->
            let src = replace_use src in
            let dest = replace_def dest defs in
            Mov_trunc { src; dest }
          | Cmp { lhs; rhs } -> Cmp { lhs = replace_use lhs; rhs = replace_use rhs }
          | If { lhs; rhs; condition; lt; lf } ->
            If { lhs = replace_use lhs; rhs = replace_use rhs; condition; lt; lf }
          | Ret { src } -> Ret { src = replace_use src }
          | CallF { dest; ident; args; assign_res } ->
            let args = List.map ~f:replace_use args in
            let dest = replace_def dest defs in
            CallF { ident; args; dest; assign_res }
          | Store { disp; base; index; scale; src } ->
            let base = replace_use base in
            let index = replace_use index in
            let src = replace_use src in
            Store { disp; base; index; scale; src }
          | Load { disp; base; index; scale; dest } ->
            let base = replace_use base in
            let index = replace_use index in
            let dest = replace_def dest defs in
            Load { disp; base; index; scale; dest }
          | Lea { disp; base; index; scale; dest } ->
            let base = replace_use base in
            let index = replace_use index in
            let dest = replace_def dest defs in
            Lea { disp; base; index; scale; dest }
          | Nop | Ret_void | Jump _ | Directive _ | Comment _ | Label _ -> instr)
        body
    in
    (* Substitute the modified body in *)
    Hashtbl.set ~key:n ~data:modified_body label_to_body;
    (* For each successor of the block, ... *)
    CFG.iter_succ
      (fun y ->
        let preds = CFG.pred cfg y in
        let j =
          List.findi preds ~f:(fun _ e -> String.(e = n)) |> Option.value_exn |> fst
        in
        let y_body = Hashtbl.find_exn label_to_body y in
        let y_body_new =
          List.map
            ~f:(fun instr ->
              match instr with
              | Phi { args; dest } ->
                let a =
                  match List.nth_exn args j with
                  | Temp t -> t
                  | _ -> failwith "phi functions should only contain temps"
                in
                let i = List.hd_exn (Hashtbl.find_exn stack a) in
                let new_args =
                  List.mapi args ~f:(fun idx old_arg ->
                    if idx = j
                    then (
                      let ai = Temp.make_version a i in
                      Ssa.Temp ai)
                    else old_arg)
                in
                Ssa.Phi { args = new_args; dest }
              | _ -> instr)
            y_body
        in
        Hashtbl.set ~key:y ~data:y_body_new label_to_body)
      cfg
      n;
    List.iter ~f:rename (dom_tree n);
    (* todo: a variable might be defined multiple times, the popping must happen that same number of times *)
    Hashtbl.iteri defs ~f:(fun ~key:a ~data:def_count ->
      Hashtbl.set
        stack
        ~key:a
        ~data:
          (let rec pop_helper curr_tail count =
             match curr_tail, count with
             | _, 0 -> curr_tail
             | [], _ -> failwith "tail not supposed to be empty"
             | _ :: t, rem -> pop_helper t (rem - 1)
           in
           pop_helper (Hashtbl.find_exn stack a) def_count))
  in
  rename root;
  (* Printf.printf "\ngraph after phi functions are added, after renaming\n";
  print_label_to_body label_to_body; *)
  (* TODO: only keep the part of the graph that is connected *)
  cfg, root, label_to_body, labels_in_order
;;
