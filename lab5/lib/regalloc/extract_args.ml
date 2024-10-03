(* L3 Compiler
 * Extract the func label instruction for liveness analysis
 *)

open Core
module AS = Assem
module NodeSet = Regalloc_modules.NodeSet

let node_of_operand_list ~(args : AS.operand list) : Node.t list =
  List.fold_left args ~init:[] ~f:(fun acc arg ->
    match arg with
    | AS.Temp _ -> Node.node_of_operand arg :: acc
    (* Ignore any non-temps, since these indicate that we've already decided 
       the colouring for those args and hence don't have to allocate them.*)
    | _ -> acc)
;;

let extract_args funcs =
  let label_args = Hashtbl.create ~growth_allowed:true ~size:6 (module String) in
  List.iter funcs ~f:(fun ((signature : AS.signature), _) ->
    let label = signature.label in
    let args = signature.args in
    match
      Hashtbl.add
        label_args
        ~key:label
        ~data:(NodeSet.of_list (node_of_operand_list ~args))
    with
    | `Ok -> ()
    | `Duplicate -> failwith "no duplicate function names expected");
  label_args
;;
