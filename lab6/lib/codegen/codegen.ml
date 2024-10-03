(* L1 Compiler
 * Assembly Code Generator for final representation of assembly 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Converts assembly with registers and stack refs to x86 assembly.
 *)
open Core
module AS = Assem

(* Current rule: use an intermediate register if both are stack refs..
   We load from src into R10, then mov from R10 into stack ref.. *)
let expand_mov (dest : AS.operand) (src : AS.operand) ~trunc : AS.instr list =
  match src, dest with
  | _, _ when AS.equal_operand src dest -> [] (* Delete replicated movs *)
  | Temp _, _ | _, Temp _ -> failwith "IR should have no more temps after stack spilling"
  | _, Imm _ -> failwith "Destination of mov cannot be an immediate"
  | Stack_ref { size = src_size; _ }, Stack_ref _ ->
    let mov =
      if trunc
      then AS.Mov_trunc { src = Reg { reg = R10; size = src_size }; dest }
      else Mov { src = Reg { reg = R10; size = src_size }; dest }
    in
    AS.[ mov; Mov { src; dest = Reg { reg = R10; size = src_size } } ]
  | _ -> if trunc then AS.[ Mov_trunc { src; dest } ] else AS.[ Mov { src; dest } ]
;;

(* If dest is a memory location, we have to use an intermediate register. *)
let expand_movsx (dest : AS.operand) (src : AS.operand) : AS.instr list =
  match dest with
  | Stack_ref _ ->
    AS.
      [ Mov { src = Reg { reg = R10; size = QUAD }; dest }
      ; Movsx { src; dest = Reg { reg = R10; size = QUAD } }
      ]
  | _ -> AS.[ Movsx { src; dest } ]
;;

(* If dest is a memory location, we have to use an intermediate register. *)
let expand_movzx (dest : AS.operand) (src : AS.operand) : AS.instr list =
  match dest with
  | Stack_ref _ ->
    AS.
      [ Mov { src = Reg { reg = R10; size = QUAD }; dest }
      ; Movzx { src; dest = Reg { reg = R10; size = QUAD } }
      ]
  | _ -> AS.[ Movzx { src; dest } ]
;;

(* After stack spilling, Store can contain anything from 0 to 3 stack refs, 
   depending on the result of register allocation. We might need to use some 
   extra scratch registers; to accomplish this, it pushes the contents of RR15
   and R11 when needed to the stack, and then restores them at the end. Stack 
   offsets in the generated code need to be adjusted by 8 or 16, depending on whether
   1 or 2 registers are pushed to the stack.

   This means that Stores with 3 stack refs are extremely expensive, and should
   be avoided as much as possible through good register allocation. (in fact
   stores with any stack refs should be avoided as much as possible, but having
   one stack ref is slightly acceptable).
   
   there are 8 cases: 
   3 stack refs: (1 case)
    M(disp(b(rsp), i(rsp), s)) <-- src(rsp):
      push RR15; push R11; src(rsp) --> R15; b(rsp) --> R10; i(rsp) --> R11; 
      M(disp(R10, R11, s)) <-- R15, pop R11, pop RR15

   2 stack refs: (3C2 = 3 cases)
    M(disp(b(rsp), i, s)) <-- src(rsp):  
      push RR15; src(rsp) --> R10, b(rsp) --> R15, M(disp(R15, i, s)) <-- R10, pop RR15
    
    M(disp(b, i(rsp), s)) <-- src(rsp):
      push RR15, src(rsp) --> R10, i(rsp) --> R15, M(disp(b, R15, s)) <-- R10, pop RR15
    
    M(disp(b(rsp), i(rsp), s)) <-- src
      push RR15, b(rsp) --> R10, i(rsp) --> R15, M(disp(R10, R15, s)) <-- src, pop RR15

   1 stack ref (3C1 = 3 cases):
    M(disp(b(rsp), i, scale)) <-- src:   
      b(rsp) --> R10,  M(disp(R10), i, scale)  <-- src
    
    M(disp(b, i(rsp), s)) <-- src:
      i(rsp) --> R10, M(disp(b, R10, s)) <-- src

    M(disp(b, i, s)) <-- src(rsp):
      s(rsp)  --> R10,  M(disp(b, i, s)) <-- R10
    
   0 stack ref (1 case):
   keep it the same.
   *)
let expand_store disp (base : AS.operand) (index : AS.operand) scale (src : AS.operand)
  : AS.instr list
  =
  match base, index, src with
  | ( Stack_ref { size = base_size; offset = base_offset }
    , Stack_ref { size = index_size; offset = index_offset }
    , Stack_ref { size = src_size; offset = src_offset } ) ->
    AS.
      [ Comment "3 Ref Store End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Pop (Reg { reg = R11; size = QUAD })
      ; Store
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index = Reg { reg = R11; size = index_size }
          ; scale
          ; src = Reg { reg = R15; size = src_size }
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 16) }
          ; dest = Reg { reg = R11; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 16) }
          ; dest = Reg { reg = R10; size = base_size }
          }
      ; Mov
          { src =
              Stack_ref { size = src_size; offset = Int32.(src_offset + of_int_exn 16) }
          ; dest = Reg { reg = R15; size = src_size }
          }
      ; Push (Reg { reg = R11; size = QUAD })
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "3 Ref Store Start"
      ]
  | ( Stack_ref { size = base_size; offset = base_offset }
    , _
    , Stack_ref { size = src_size; offset = src_offset } ) ->
    AS.
      [ Comment "2 Ref Store (base and src) End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Store
          { disp
          ; base = Reg { reg = R15; size = base_size }
          ; index
          ; scale
          ; src = Reg { reg = R10; size = src_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = base_size }
          }
      ; Mov
          { src =
              Stack_ref { size = src_size; offset = Int32.(src_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = src_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "2 Ref Store (base and src) Start"
      ]
  | ( _
    , Stack_ref { size = index_size; offset = index_offset }
    , Stack_ref { size = src_size; offset = src_offset } ) ->
    AS.
      [ Comment "2 Ref Store (index and src) End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Store
          { disp
          ; base
          ; index = Reg { reg = R15; size = index_size }
          ; scale
          ; src = Reg { reg = R10; size = src_size }
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = src_size; offset = Int32.(src_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = src_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "2 Ref Store (index and src) Start"
      ]
  | ( Stack_ref { size = base_size; offset = base_offset }
    , Stack_ref { size = index_size; offset = index_offset }
    , _ ) ->
    AS.
      [ Comment "2 Ref Store (base and index) End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Store
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index = Reg { reg = R15; size = index_size }
          ; scale
          ; src
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = base_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "2 Ref Store (base and index) Start"
      ]
  | Stack_ref { size = base_size; _ }, _, _ ->
    AS.
      [ Comment "1 Ref Store (base) End"
      ; Store { disp; base = Reg { reg = R10; size = base_size }; index; scale; src }
      ; Mov { src = base; dest = Reg { reg = R10; size = base_size } }
      ; Comment "1 Ref Store (base) Start"
      ]
  | _, Stack_ref { size = index_size; _ }, _ ->
    AS.
      [ Comment "1 Reg Store (index) End"
      ; Store { disp; base; index = Reg { reg = R10; size = index_size }; scale; src }
      ; Mov { src = index; dest = Reg { reg = R10; size = index_size } }
      ; Comment "1 Reg Store (index) Start"
      ]
  | _, _, Stack_ref { size = src_size; _ } ->
    AS.
      [ Comment "1 Reg Store (src) End"
      ; Store { disp; base; index; scale; src = Reg { reg = R10; size = src_size } }
      ; Mov { src; dest = Reg { reg = R10; size = src_size } }
      ; Comment "1 Reg Store (src) Start"
      ]
  | _ -> AS.[ Store { disp; base; index; scale; src } ]
;;

(* Load uses a similar fix to store.
   
   there are 8 cases: 
   3 stack refs: (1 case)
    M(disp(b(rsp), i(rsp), s)) --> dest(rsp):
      push RR15, b(rsp) --> R10, i(rsp) --> RR15,
      M(disp(R10, RR15, s)) --> R15, R15 --> dest(rsp), pop R15

   2 stack refs: (3C2 = 3 cases)
    M(disp(b(rsp), i, s)) --> dest(rsp):  
      b(rsp) --> R10, M(disp(R10, i, s)) --> R10, R10 --> dest(rsp)
    
    M(disp(b, i(rsp), s)) --> dest(rsp):
      i(rsp) --> R10, M(disp(b, R10, s)) --> R10, R10 --> dest(rsp)
    
    M(disp(b(rsp), i(rsp), s)) --> dest
      push R15, b(rsp) --> R10, i(rsp) --> R15, M(disp(R10, R15, s)) --> dest, pop R15

   1 stack ref (3C1 = 3 cases):
    M(disp(b(rsp), i, s)) --> dest:   
      b(rsp) --> R10,  M(disp(R10), i, s))  --> dest
    
    M(disp(b, i(rsp), s)) --> dest:
      i(rsp) --> R10, M(disp(b, R10, s)) --> dest

    M(disp(b, i, s)) --> dest(rsp):
      M(disp(b, i, s)) --> R10, R10  --> dest(rsp)
    
   0 stack ref (1 case):
   keep it the same.

   *)
let expand_load disp (base : AS.operand) (index : AS.operand) scale (dest : AS.operand)
  : AS.instr list
  =
  match base, index, dest with
  | ( Stack_ref { size = base_size; offset = base_offset }
    , Stack_ref { size = index_size; offset = index_offset }
    , Stack_ref { size = dest_size; offset = dest_offset } ) ->
    AS.
      [ Comment "3 Ref Load End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Mov
          { src = Reg { reg = R15; size = dest_size }
          ; dest =
              Stack_ref { size = dest_size; offset = Int32.(dest_offset + of_int_exn 8) }
          }
      ; Load
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index = Reg { reg = R15; size = index_size }
          ; scale
          ; dest = Reg { reg = R15; size = dest_size }
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = base_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "3 Ref Load Begin"
      ]
  | Stack_ref { size = base_size; _ }, _, Stack_ref { size = dest_size; _ } ->
    AS.
      [ Comment "2 Ref Load (base, dest) End"
      ; Mov { src = Reg { reg = R10; size = dest_size }; dest }
      ; Load
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index
          ; scale
          ; dest = Reg { reg = R10; size = dest_size }
          }
      ; Mov { src = base; dest = Reg { reg = R10; size = base_size } }
      ; Comment "2 Ref Load (base, dest) Begin"
      ]
  | ( _
    , Stack_ref { size = index_size; offset = _ }
    , Stack_ref { size = dest_size; offset = _ } ) ->
    AS.
      [ Comment "2 Ref Load (index, dest) End"
      ; Mov { src = Reg { reg = R10; size = dest_size }; dest }
      ; Load
          { disp
          ; base
          ; index = Reg { reg = R10; size = index_size }
          ; scale
          ; dest = Reg { reg = R10; size = dest_size }
          }
      ; Mov { src = index; dest = Reg { reg = R10; size = index_size } }
      ; Comment "2 Ref Load (index, dest) Begin"
      ]
  | ( Stack_ref { size = base_size; offset = base_offset }
    , Stack_ref { size = index_size; offset = index_offset }
    , _ ) ->
    AS.
      [ Comment "2 Reg Load(base, index) End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Load
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index = Reg { reg = R15; size = index_size }
          ; scale
          ; dest
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = base_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "2 Reg Load(base, index) Begin"
      ]
  | Stack_ref { size = base_size; _ }, _, _ ->
    AS.
      [ Comment "1 Reg Load (base) End"
      ; Load { disp; base = Reg { reg = R10; size = base_size }; index; scale; dest }
      ; Mov { src = base; dest = Reg { reg = R10; size = base_size } }
      ; Comment "1 Reg Load (base) Begin"
      ]
  | _, Stack_ref { size = index_size; _ }, _ ->
    AS.
      [ Comment "1 Reg Load (index) End"
      ; Load { disp; base; index = Reg { reg = R10; size = index_size }; scale; dest }
      ; Mov { src = index; dest = Reg { reg = R10; size = index_size } }
      ; Comment "1 Reg Load (index) Begin"
      ]
  | _, _, Stack_ref { size = dest_size; _ } ->
    AS.
      [ Comment "1 Reg Load (dest) End"
      ; Mov { src = Reg { reg = R10; size = dest_size }; dest }
      ; Load { disp; base; index; scale; dest = Reg { reg = R10; size = dest_size } }
      ; Comment "1 Reg Load (dest) Begin"
      ]
    (* M(disp(b, i, s)) --> R10, R10  --> dest(rsp) *)
  | _ -> AS.[ Load { disp; base; index; scale; dest } ]
;;

(* Lea follows a similar pattern to Load - the only change is that all memory
loads are replaced with load effective addresses.
   *)
let expand_lea disp (base : AS.operand) (index : AS.operand) scale (dest : AS.operand)
  : AS.instr list
  =
  match base, index, dest with
  | ( Stack_ref { size = base_size; offset = base_offset }
    , Stack_ref { size = index_size; offset = index_offset }
    , Stack_ref { size = dest_size; offset = dest_offset } ) ->
    AS.
      [ Comment "3 Ref Lea End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Mov
          { src = Reg { reg = R15; size = dest_size }
          ; dest =
              Stack_ref { size = dest_size; offset = Int32.(dest_offset + of_int_exn 8) }
          }
      ; Lea
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index = Reg { reg = R15; size = index_size }
          ; scale
          ; dest = Reg { reg = R15; size = dest_size }
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = base_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "3 Ref Lea Begin"
      ]
  | Stack_ref { size = base_size; _ }, _, Stack_ref { size = dest_size; _ } ->
    AS.
      [ Comment "2 Ref Lea (base, dest) End"
      ; Mov { src = Reg { reg = R10; size = dest_size }; dest }
      ; Lea
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index
          ; scale
          ; dest = Reg { reg = R10; size = dest_size }
          }
      ; Mov { src = base; dest = Reg { reg = R10; size = base_size } }
      ; Comment "2 Ref Lea (base, dest) Begin"
      ]
  | ( _
    , Stack_ref { size = index_size; offset = _ }
    , Stack_ref { size = dest_size; offset = _ } ) ->
    AS.
      [ Comment "2 Ref Lea (index, dest) End"
      ; Mov { src = Reg { reg = R10; size = dest_size }; dest }
      ; Lea
          { disp
          ; base
          ; index = Reg { reg = R10; size = index_size }
          ; scale
          ; dest = Reg { reg = R10; size = dest_size }
          }
      ; Mov { src = index; dest = Reg { reg = R10; size = index_size } }
      ; Comment "2 Ref Lea (index, dest) Begin"
      ]
  | ( Stack_ref { size = base_size; offset = base_offset }
    , Stack_ref { size = index_size; offset = index_offset }
    , _ ) ->
    AS.
      [ Comment "2 Reg Lea(base, index) End"
      ; Pop (Reg { reg = R15; size = QUAD })
      ; Lea
          { disp
          ; base = Reg { reg = R10; size = base_size }
          ; index = Reg { reg = R15; size = index_size }
          ; scale
          ; dest
          }
      ; Mov
          { src =
              Stack_ref
                { size = index_size; offset = Int32.(index_offset + of_int_exn 8) }
          ; dest = Reg { reg = R15; size = index_size }
          }
      ; Mov
          { src =
              Stack_ref { size = base_size; offset = Int32.(base_offset + of_int_exn 8) }
          ; dest = Reg { reg = R10; size = base_size }
          }
      ; Push (Reg { reg = R15; size = QUAD })
      ; Comment "2 Reg Lea(base, index) Begin"
      ]
  | Stack_ref { size = base_size; _ }, _, _ ->
    AS.
      [ Comment "1 Reg Lea (base) End"
      ; Lea { disp; base = Reg { reg = R10; size = base_size }; index; scale; dest }
      ; Mov { src = base; dest = Reg { reg = R10; size = base_size } }
      ; Comment "1 Reg Lea (base) Begin"
      ]
  | _, Stack_ref { size = index_size; _ }, _ ->
    AS.
      [ Comment "1 Reg Lea (index) End"
      ; Lea { disp; base; index = Reg { reg = R10; size = index_size }; scale; dest }
      ; Mov { src = index; dest = Reg { reg = R10; size = index_size } }
      ; Comment "1 Reg Lea (index) Begin"
      ]
  | _, _, Stack_ref { size = dest_size; _ } ->
    AS.
      [ Comment "1 Reg Lea (dest) End"
      ; Mov { src = Reg { reg = R10; size = dest_size }; dest }
      ; Lea { disp; base; index; scale; dest = Reg { reg = R10; size = dest_size } }
      ; Comment "1 Reg Lea (dest) Begin"
      ]
    (* M(disp(b, i, s)) --> R10, R10  --> dest(rsp) *)
  | _ -> AS.[ Lea { disp; base; index; scale; dest } ]
;;

let code_gen (lst : AS.func list) ~_peephole ~_peephole_invert : AS.program =
  (* Replace all special chars with escape sequences *)
  let replace_escape_chars s = String.escaped s in
  let string_table = Hashtbl.create ~growth_allowed:true ~size:10 (module String) in
  (* Checks operands against the current global string table, returning the appropriate label. *)
  let ref_string_table op =
    match op with
    | AS.String s ->
      let s' = replace_escape_chars s in
      let label =
        Hashtbl.find_or_add string_table s' ~default:(fun () ->
          Printf.sprintf ".LC%d" (Hashtbl.length string_table))
      in
      AS.Label_op label
    | _ -> op
  in
  let rec code_gen_rec (lst : AS.instr list) (acc : AS.instr list) : AS.instr list =
    match lst with
    | [] -> acc
    | Mov { dest; src } :: t ->
      code_gen_rec t (expand_mov dest (ref_string_table src) ~trunc:false @ acc)
    | Mov_trunc { dest; src } :: t ->
      code_gen_rec t (expand_mov dest (ref_string_table src) ~trunc:true @ acc)
    | Movsx { dest; src } :: t ->
      code_gen_rec t (expand_movsx dest (ref_string_table src) @ acc)
    | Movzx { dest; src } :: t ->
      code_gen_rec t (expand_movzx dest (ref_string_table src) @ acc)
    | Store { disp; base; index; scale; src } :: t ->
      code_gen_rec t (expand_store disp base index scale (ref_string_table src) @ acc)
    | Load { disp; base; index; scale; dest } :: t ->
      code_gen_rec t (expand_load disp base index scale dest @ acc)
    | Lea { disp; base; index; scale; dest } :: t ->
      code_gen_rec t (expand_lea disp base index scale dest @ acc)
    | h :: t -> code_gen_rec t (h :: acc)
  in
  let code_gen_helper (func : AS.func) : AS.func =
    let signature, body = func in
    let translated_body = List.rev (code_gen_rec body []) in
    if _peephole
    then signature, Peephole.peephole ~_peephole_invert translated_body
    else signature, translated_body
  in
  string_table, List.map lst ~f:(fun l -> code_gen_helper l)
;;
(* Apply code_gen_helper to all lists and flatten the result.*)
