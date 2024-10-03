(* L5 Compiler
 * Function Inlining
 * Author: Ethan Cheong, Wu Meng Hui
 *
 * Based on 15411 Lecture Notes.
 *)
open Core
module ThreeAS = Threeaddrassem
module StringSet = Set.Make (String)

(* Debugging utils *)
(* let print_set_table tbl =
  Hashtbl.iteri tbl ~f:(fun ~key:ident ~data:callers ->
    let callers = StringSet.fold callers ~init:"" ~f:(fun c acc -> c ^ ", " ^ acc) in
    Printf.printf "%s was called by %s \n" ident callers)
;; *)

(** Given a list of instructions [callee_body], prepend a list of moves from 
    the caller args to the callee args, replace any rets to a move to caller_dest.
    End off with an inlining_end label. Produce in reverse.
     *)
let replace_body
  caller_dest
  caller_args
  callee_args
  callee_body
  inline_count
  caller_ident
  callee_ident
  =
  let callee_to_caller_arg =
    Hashtbl.create ~growth_allowed:true ~size:10 (module ThreeAS)
  in
  List.iter2_exn callee_args caller_args ~f:(fun callee caller ->
    Hashtbl.set callee_to_caller_arg ~key:callee ~data:caller);
  let prologue =
    List.map2_exn caller_args callee_args ~f:(fun caller_arg callee_arg ->
      ThreeAS.Mov { src = caller_arg; dest = callee_arg })
  in
  let inlining_end_label =
    Printf.sprintf "inlining_end_%d%s%s" inline_count caller_ident callee_ident
  in
  let rec body_helper acc lst =
    match lst with
    | [] -> ThreeAS.Label inlining_end_label :: acc
    | ThreeAS.Label l :: tl ->
      body_helper (Label (Printf.sprintf "%s_%d%s" l inline_count caller_ident) :: acc) tl
    | If { lhs; rhs; condition; lt; lf } :: tl ->
      let lt = Printf.sprintf "%s_%d%s" lt inline_count caller_ident in
      let lf = Printf.sprintf "%s_%d%s" lf inline_count caller_ident in
      body_helper (If { lhs; rhs; condition; lt; lf } :: acc) tl
    | Jump l :: tl ->
      body_helper (Jump (Printf.sprintf "%s_%d%s" l inline_count caller_ident) :: acc) tl
    | Ret { src } :: tl ->
      body_helper (Jump inlining_end_label :: Mov { src; dest = caller_dest } :: acc) tl
    | Ret_void :: tl -> body_helper (Jump inlining_end_label :: acc) tl
    | instr :: tl -> body_helper (instr :: acc) tl
  in
  body_helper prologue callee_body
;;

(* New plan:
  First, make a hashmap mapping all inlineable functions to their bodies.
  
  Then, iterate through each function body, replacing calls to inlineable functions
with the corresponding body.
*)

(** Inlines non-recursive functions with less than [_inline_threshold] temps. *)
let inline_functions (program : ThreeAS.func list) ~_inline_threshold =
  (* Printf.printf "Program before inlining: %s\n" (ThreeAS.format program); *)
  let inlineable_func_to_args_body =
    Hashtbl.create ~growth_allowed:true ~size:10 (module String)
  in
  List.iter program ~f:(fun ({ ident; recursive; num_temps; args; _ }, body) ->
    if (not recursive) && num_temps < _inline_threshold
    then Hashtbl.set inlineable_func_to_args_body ~key:ident ~data:(args, body));
  List.map
    program
    ~f:(fun ({ ident = caller_ident; args; tail_rec; num_temps; _ }, caller_body) ->
    let inline_counter = ref (-1) in
    let rec replace_calls_helper acc lst =
      match lst with
      | [] -> List.rev acc
      | ThreeAS.CallF { ident; dest = caller_dest; args = caller_args; _ } :: tl
        when Hashtbl.mem inlineable_func_to_args_body ident ->
        incr inline_counter;
        let callee_args, callee_body =
          Hashtbl.find_exn inlineable_func_to_args_body ident
        in
        (replace_calls_helper
           (replace_body
              caller_dest
              caller_args
              callee_args
              callee_body
              !inline_counter
              caller_ident
              ident
            @ acc))
          tl
      | instr :: tl -> replace_calls_helper (instr :: acc) tl
    in
    let body' = replace_calls_helper [] caller_body in
    (* Check if now recursive ! *)
    let recursive' =
      List.mem
        body'
        (ThreeAS.CallF
           { ident = caller_ident; args = []; dest = Imm Int32.zero; assign_res = false })
        ~equal:(fun a b ->
          match a, b with
          | CallF { ident = i; _ }, CallF { ident = i'; _ } -> String.(i = i')
          | _ -> true)
    in
    ( ThreeAS.{ ident = caller_ident; args; tail_rec; num_temps; recursive = recursive' }
    , body' ))
;;

(* 
  let defined_functions = Hashtbl.create ~growth_allowed:true ~size:10 (module String) in
  let callee_to_callers = Hashtbl.create ~growth_allowed:true ~size:10 (module String) in
  let number_of_temps = Hashtbl.create ~growth_allowed:true ~size:10 (module String) in
  List.iter program ~f:(fun ({ ident; _ }, _) ->
    Hashtbl.set defined_functions ~key:ident ~data:"");
  let non_recursive_functions =
    Hashtbl.create ~growth_allowed:true ~size:10 (module String)
  in
  let call_function callee caller =
    Hashtbl.update callee_to_callers callee ~f:(fun opt ->
      match opt with
      | None -> StringSet.add StringSet.empty caller
      | Some set -> StringSet.add set caller)
  in
  List.iter program ~f:(fun ({ ident = caller; num_temps; recursive; _ }, body) ->
    Hashtbl.set number_of_temps ~key:caller ~data:num_temps;
    if not recursive then Hashtbl.set non_recursive_functions ~key:caller ~data:"";
    List.iter body ~f:(fun instr ->
      match instr with
      (* Only count l4 function calls. *)
      | ThreeAS.CallF { ident = callee; _ } when String.is_prefix callee ~prefix:"_f" ->
        call_function callee caller
      | _ -> ()));
  let inlined_functions = StringSet.empty in
  (* let program', inlined_functions' = *)
  let program', _ =
    Hashtbl.fold
      callee_to_callers
      ~init:(program, inlined_functions)
      ~f:(fun ~key:callee ~data:callers acc ->
      (* we only inline if the number of temps of the callee is less than 
       _inline_threshold, and the callee is not recursive, and the callee was 
       defined in the program. *)
      if Hashtbl.mem non_recursive_functions callee
         && Hashtbl.find_exn number_of_temps callee < _inline_threshold
         && Hashtbl.mem defined_functions callee
      then inline_func (fst acc) callee callers, StringSet.add inlined_functions callee
      else acc)
  in
  (* Remove inlined functions *)
  (* let program'' =
    StringSet.fold inlined_functions' ~init:program' ~f:(fun acc inlined_func ->
      List.Assoc.remove
        acc
        ~equal:(fun a b -> String.(a.ident = b.ident))
        ThreeAS.
          { ident = inlined_func
          ; args = []
          ; tail_rec = false
          ; num_temps = 0
          ; recursive = false
          })
  in *)
  (* Remove all inlined functions from the original program *)
  (* Printf.printf "Program after inlining: %s\n" (ThreeAS.format program''); *)
  program'
;; *)
