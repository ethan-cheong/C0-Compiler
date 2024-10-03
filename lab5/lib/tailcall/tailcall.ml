(* L5 Compiler
 * Tail-Call Optimization
 * Author: Ethan Cheong, Wu Meng Hui
 *
 * Based on 15411 Lecture Notes.
 *)
open Core
module ThreeAS = Threeaddrassem

(** Perform simple tail-call optimization on the body of a recursive function. *)
let tail_call_body ident args body =
  let arg_to_temp = Hashtbl.create ~growth_allowed:true ~size:10 (module ThreeAS) in
  let replace_arg op =
    match Hashtbl.find arg_to_temp op with
    | Some t -> ThreeAS.Temp t
    | None -> op
  in
  (* The destinations of all TR function calls need to be tracked, and any rets
     that return them need to be eliminated. *)
  let tr_call_dest = Hashtbl.create ~growth_allowed:true ~size:10 (module ThreeAS) in
  let prologue =
    (* Idea: Since we don't have arg registers, for each arg, instead 
       introduce a temp. e.g. if args are
       args = t1 t2 t3

       then add

        t5 <- t1
        t6 <- t2
        t7 <- t3
       goto ident (this goto is necessary for basic block structure)
       ident:
       as a prologue
       then replace all in the function body with the corresponding temp
       then replace call ident with 
       t1 <- t5
       t2 <- t6
       t3 <- t7
       goto ident
       *)
    List.map args ~f:(fun arg ->
      let temp =
        Temp.create_of_size
          (match arg with
           | ThreeAS.Imm _ | MAX_INT -> Temp.DOUBLE
           | Addr_imm _ -> QUAD
           | Temp t -> Temp.size t)
      in
      Hashtbl.set arg_to_temp ~key:arg ~data:temp;
      ThreeAS.Mov { src = arg; dest = Temp temp })
    @ [ ThreeAS.Jump ident; ThreeAS.Label ident ]
  in
  let rec replace_body_helper acc lst =
    match lst with
    | [] -> List.rev acc
    | ThreeAS.Binop { op; dest; lhs; rhs } :: tl ->
      replace_body_helper
        (ThreeAS.Binop
           { op; dest = replace_arg dest; lhs = replace_arg lhs; rhs = replace_arg rhs }
         :: acc)
        tl
    | Mov { dest; src } :: tl ->
      replace_body_helper
        (Mov { dest = replace_arg dest; src = replace_arg src } :: acc)
        tl
    | Movsx { dest; src } :: tl ->
      replace_body_helper
        (Movsx { dest = replace_arg dest; src = replace_arg src } :: acc)
        tl
    | Movzx { dest; src } :: tl ->
      replace_body_helper
        (Movzx { dest = replace_arg dest; src = replace_arg src } :: acc)
        tl
    | Mov_trunc { dest; src } :: tl ->
      replace_body_helper
        (Mov_trunc { dest = replace_arg dest; src = replace_arg src } :: acc)
        tl
    | Cmp { lhs; rhs } :: tl ->
      replace_body_helper (Cmp { lhs = replace_arg lhs; rhs = replace_arg rhs } :: acc) tl
    | If { lhs; rhs; condition; lt; lf } :: tl ->
      replace_body_helper
        (If { lhs = replace_arg lhs; rhs = replace_arg rhs; condition; lt; lf } :: acc)
        tl
    (* Eliminate any returns that come right after a TR call. *)
    | Ret { src } :: tl when Hashtbl.mem tr_call_dest src -> replace_body_helper acc tl
    | Ret { src } :: tl -> replace_body_helper (Ret { src = replace_arg src } :: acc) tl
    | Store { disp; base; index; scale; src } :: tl ->
      replace_body_helper
        (Store
           { disp
           ; base = replace_arg base
           ; index = replace_arg index
           ; scale
           ; src = replace_arg src
           }
         :: acc)
        tl
    | Load { disp; base; index; scale; dest } :: tl ->
      replace_body_helper
        (Load
           { disp
           ; base = replace_arg base
           ; index = replace_arg index
           ; scale
           ; dest = replace_arg dest
           }
         :: acc)
        tl
    | Lea { disp; base; index; scale; dest } :: tl ->
      replace_body_helper
        (Lea
           { disp
           ; base = replace_arg base
           ; index = replace_arg index
           ; scale
           ; dest = replace_arg dest
           }
         :: acc)
        tl
    | CallF { ident = i; dest; args = callee_args; _ } :: tl when String.(ident = i) ->
      (* We can throw away everything (even the assignment to dest) since the 
         tail recursion deals with it in the base case. However we need to track
         any temps that were assigned to by a TR call, so we can eliminate 
         their returns. *)
      Hashtbl.set tr_call_dest ~key:dest ~data:"";
      replace_body_helper
        (* dest: (args -> arg_to_temp) src: callee_args *)
        ((ThreeAS.Jump ident
          :: List.map2_exn args callee_args ~f:(fun arg callee_arg ->
               let caller_temp = Hashtbl.find_exn arg_to_temp arg in
               ThreeAS.Mov { dest = Temp caller_temp; src = callee_arg }))
         @ acc)
        tl
    | instr :: tl -> replace_body_helper (instr :: acc) tl
  in
  let body' = replace_body_helper [] body in
  List.append prologue body'
;;

let tail_call_optimization (program : ThreeAS.func list) =
  let tail_rec_funcs = Hashtbl.create ~growth_allowed:true ~size:10 (module String) in
  (* Replace insides of all tail recursive functions. *)
  let program' =
    List.map program ~f:(fun (signature, body) ->
      if signature.tail_rec
      then (
        Hashtbl.set tail_rec_funcs ~key:signature.ident ~data:"";
        let body' = tail_call_body signature.ident signature.args body in
        (* After applying the optimization, functions are no longer tail
           recursive nor recursive, so we can apply inlining to them. *)
        ( { signature with
            ident = signature.ident ^ "_prologue"
          ; tail_rec = false
          ; recursive = false
          }
        , body' ))
      else signature, body)
    (* The new header is _f_..._prologue. *)
  in
  (* Replace all function calls to tail recursive functions. *)
  let program'' =
    List.map program' ~f:(fun (signature, body) ->
      let body' =
        List.map body ~f:(fun instr ->
          match instr with
          | ThreeAS.CallF { dest; ident; args; assign_res }
            when Hashtbl.mem tail_rec_funcs ident ->
            ThreeAS.CallF { dest; ident = ident ^ "_prologue"; args; assign_res }
          | _ -> instr)
      in
      signature, body')
  in
  program''
;;
