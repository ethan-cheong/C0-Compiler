(* L1 Compiler
 * Elaborate on the initial AST
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
 * Elaborate out the initialisation of a declaration after type checking
 *)

open Core
module SymbolTable = Type_modules.SymbolTable
module Int32Table = Type_modules.Int32Table

let print_struct_offsets all_struct_offsets struct_sizes ident fields =
  let struct_offsets =
    match SymbolTable.find all_struct_offsets ident with
    | None -> failwith "struct doesnt exist in struct offsets"
    | Some x -> x
  in
  match SymbolTable.find struct_sizes ident with
  | None -> failwith "struct doesnt exist in struct sizes"
  | Some (x, _) ->
    Printf.printf "struct (%s) size: (%s)\n" (Symbol.name ident) (Int64.to_string x);
    List.iteri fields ~f:(fun ind (s, _) ->
      match Int32Table.find struct_offsets (Int32.of_int_trunc ind) with
      | None -> failwith (sprintf "%s does not exist in struct offset" (Symbol.name s))
      | Some x ->
        Printf.printf "field (%s) offset: (%s)\n" (Symbol.name s) (Int64.to_string x))
;;

let print_from_program all_struct_offsets struct_sizes (program_list : Ast.program) : unit
  =
  List.iter program_list ~f:(fun mprog ->
    let prog = Mark.data mprog in
    match prog with
    | Ast.Struct_Def { ident; fields } ->
      print_struct_offsets all_struct_offsets struct_sizes ident fields
    | _ -> ())
;;

(* Helper function to Mark something with the lexing positions *)
let mark_with_pos (data : 'a) (start_pos : Lexing.position) (end_pos : Lexing.position)
  : 'a Mark.t
  =
  let src_span = Mark.of_positions start_pos end_pos in
  Mark.mark data src_span
;;

(* Helper function to Mark something with the source span *)
let mark_with_span (data : 'a) (span : Mark.src_span) = Mark.mark data span

(* Helper function to generate the source span, will generate a dummy one if there isn't a span for a given statement *)
let get_start_end marked_stmt =
  match Mark.src_span marked_stmt with
  | Some span -> span
  | None -> Mark.of_positions Lexing.dummy_pos Lexing.dummy_pos
;;

let is_variable = function
  | Ast.Var _ -> true
  | _ -> false
;;

let extract_struct_symbol s =
  let s_data = Mark.data s in
  let s_type =
    Ast.(
      match s_data with
      | Var { var_type; _ } -> var_type
      | Ternary { result_type; _ } -> result_type
      | Deref { pointer_type; _ } -> pointer_type
      | Struct_access_parse { field_type; _ } -> field_type
      | Struct_access { field_type; _ } -> field_type
      | Array_access { array_type; _ } -> array_type
      | Anno_elem t -> t (* Get the type for the anno element? *)
      | _ ->
        Printf.printf "%s\n" (Ast.Print.pp_exp s_data);
        failwith "do not return valid type for struct access")
  in
  match s_type with
  | Ast.Struct sym -> sym
  | _ -> failwith "not a struct access"
;;

let rec replace_struct_access offsets struct_field_to_ind (e : Ast.mexp) : Ast.mexp =
  let e_span = get_start_end e in
  let e_data = Mark.data e in
  Ast.(
    match e_data with
    | Paren _ -> failwith "no more parens"
    | Var _ | Const _ | Alloc _ | Null_pointer -> e
    | Binop_pure { op; lhs; rhs } ->
      mark_with_span
        (Binop_pure
           { op
           ; lhs = replace_struct_access offsets struct_field_to_ind lhs
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        e_span
    | Binop_impure { op; lhs; rhs } ->
      mark_with_span
        (Binop_impure
           { op
           ; lhs = replace_struct_access offsets struct_field_to_ind lhs
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        e_span
    | Unop { op; operand } ->
      mark_with_span
        (Unop { op; operand = replace_struct_access offsets struct_field_to_ind operand })
        e_span
    | Function_call { ident; args; return_type } ->
      let extracted_args =
        List.map args ~f:(fun x -> replace_struct_access offsets struct_field_to_ind x)
      in
      mark_with_span (Function_call { ident; args = extracted_args; return_type }) e_span
    | Comparison { op; lhs; rhs } ->
      mark_with_span
        (Comparison
           { op
           ; lhs = replace_struct_access offsets struct_field_to_ind lhs
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        e_span
    | And { lhs; rhs } ->
      mark_with_span
        (And
           { lhs = replace_struct_access offsets struct_field_to_ind lhs
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        e_span
    | Or { lhs; rhs } ->
      mark_with_span
        (Or
           { lhs = replace_struct_access offsets struct_field_to_ind lhs
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        e_span
    | Ternary { condition; lhs; rhs; result_type } ->
      mark_with_span
        (Ternary
           { condition = replace_struct_access offsets struct_field_to_ind condition
           ; lhs = replace_struct_access offsets struct_field_to_ind lhs
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           ; result_type
           })
        e_span
    | Deref { address; pointer_type } ->
      mark_with_span
        (Deref
           { address = replace_struct_access offsets struct_field_to_ind address
           ; pointer_type
           })
        e_span
    | Alloc_array { array_type; size } ->
      mark_with_span
        (Alloc_array
           { array_type; size = replace_struct_access offsets struct_field_to_ind size })
        e_span
    | Array_access { array; index; array_type } ->
      mark_with_span
        (Array_access
           { array = replace_struct_access offsets struct_field_to_ind array
           ; index = replace_struct_access offsets struct_field_to_ind index
           ; array_type
           })
        e_span
    | Anno_result -> e
    | Anno_index -> e
    | Anno_elem _ -> e
    | String_const _ -> e
    | Forall { arr; condition } ->
      mark_with_span
        (Forall
           { arr = replace_struct_access offsets struct_field_to_ind arr
           ; condition = replace_struct_access offsets struct_field_to_ind condition
           })
        e_span
    | Exists { arr; condition } ->
      mark_with_span
        (Exists
           { arr = replace_struct_access offsets struct_field_to_ind arr
           ; condition = replace_struct_access offsets struct_field_to_ind condition
           })
        e_span
    | Anno_length mexp ->
      mark_with_span
        (Anno_length (replace_struct_access offsets struct_field_to_ind mexp))
        e_span
    | Cast { pointer_type; operand; orig_type } ->
      mark_with_span
        (Cast
           { pointer_type
           ; operand = replace_struct_access offsets struct_field_to_ind operand
           ; orig_type
           })
        e_span
    | Struct_access_parse { s; field; field_type } ->
      (* s must be a variable? *)
      let s_type = extract_struct_symbol s in
      let offset_table =
        match SymbolTable.find offsets s_type with
        | None ->
          failwith (sprintf "offset table doesnt exist for %s" (Symbol.name s_type))
        | Some x -> x
      in
      let field_to_ind_table =
        match SymbolTable.find struct_field_to_ind s_type with
        | None ->
          failwith (sprintf "field to ind table doesnt exist for %s" (Symbol.name s_type))
        | Some x -> x
      in
      let field_index =
        match SymbolTable.find field_to_ind_table field with
        | None -> failwith (sprintf "field index doesnt exist for %s" (Symbol.name field))
        | Some x -> x
      in
      let field_offset =
        match Int32Table.find offset_table field_index with
        | None ->
          failwith
            (sprintf
               "offset doesnt exist for struct %s field %s"
               (Symbol.name s_type)
               (Symbol.name field))
        | Some x -> x
      in
      mark_with_span
        (Struct_access
           { s = replace_struct_access offsets struct_field_to_ind s
           ; offset = field_offset
           ; field_type
           })
        e_span
    | Struct_access { s; offset; field_type } ->
      mark_with_span
        (Struct_access
           { s = replace_struct_access offsets struct_field_to_ind s; offset; field_type })
        e_span)

and process_anno offsets struct_field_to_ind anno =
  List.map anno ~f:(fun spec ->
    Ast.(
      match spec with
      | Requires e -> Requires (replace_struct_access offsets struct_field_to_ind e)
      | Ensures e -> Ensures (replace_struct_access offsets struct_field_to_ind e)
      | Loop_invariant e ->
        Loop_invariant (replace_struct_access offsets struct_field_to_ind e)
      | Assert_spec e -> Assert_spec (replace_struct_access offsets struct_field_to_ind e)))
;;

(* Expands on the initial mstm list by recursively going into each of the branches
   and processing each statement *)
let rec process offsets struct_field_to_ind h =
  let stm_data = Mark.data h in
  let stm_src = get_start_end h in
  match stm_data with
  (* If have declare intermediate, need to process it... *)
  | Ast.Declare_intermediate _ -> failwith "no more declare_intermediates after typecheck"
  | Ast.Block_intermediate _ -> failwith "no more blocks after typecheck"
  | Ast.Asnop_pure_mem_intermediate _ ->
    failwith "no more asnop_pure_mem_intermediate after typecheck"
  | Ast.Asnop_impure_mem_intermediate _ ->
    failwith "no more asnop_impure_mem_intermediate after typecheck"
  | Ast.For _ -> failwith "no more for after typecheck"
  | Ast.Assign (e1, e2) ->
    mark_with_span
      (Ast.Assign
         ( replace_struct_access offsets struct_field_to_ind e1
         , replace_struct_access offsets struct_field_to_ind e2 ))
      stm_src
  | Ast.Return e ->
    mark_with_span
      (Ast.Return (replace_struct_access offsets struct_field_to_ind e))
      stm_src
  | Ast.Return_void -> h
  | Ast.Nop -> h
  | Ast.Expr_stm e ->
    mark_with_span
      (Ast.Expr_stm (replace_struct_access offsets struct_field_to_ind e))
      stm_src
  | Ast.Assert e ->
    mark_with_span
      (Ast.Assert (replace_struct_access offsets struct_field_to_ind e))
      stm_src
  | Ast.If (mexp, s1, s2) ->
    mark_with_span
      (Ast.If
         ( replace_struct_access offsets struct_field_to_ind mexp
         , process offsets struct_field_to_ind s1
         , process offsets struct_field_to_ind s2 ))
      stm_src
  | Ast.Seq (s1, s2) ->
    mark_with_span
      (Ast.Seq
         (process offsets struct_field_to_ind s1, process offsets struct_field_to_ind s2))
      stm_src
  | Ast.While (e, s) ->
    mark_with_span
      (Ast.While
         ( replace_struct_access offsets struct_field_to_ind e
         , process offsets struct_field_to_ind s ))
      stm_src
  | Ast.Declare (decl, tau, mstm) ->
    mark_with_span (process_decl offsets struct_field_to_ind decl tau mstm) stm_src
  (* Asnops should not need further elaboration *)
  | Ast.Asnop_pure_mem { lhs; op; rhs } ->
    let replaced_lhs = replace_struct_access offsets struct_field_to_ind lhs in
    if not (is_variable (Mark.data replaced_lhs))
    then
      mark_with_span
        (Ast.Asnop_pure_mem
           { lhs = replaced_lhs
           ; op
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        stm_src
    else
      mark_with_span
        (Ast.Assign
           ( replaced_lhs
           , mark_with_span
               (Ast.Binop_pure
                  { lhs = replaced_lhs
                  ; op
                  ; rhs = replace_struct_access offsets struct_field_to_ind rhs
                  })
               stm_src ))
        stm_src
  | Asnop_impure_mem { lhs; op; rhs } ->
    let replaced_lhs = replace_struct_access offsets struct_field_to_ind lhs in
    if not (is_variable (Mark.data replaced_lhs))
    then
      mark_with_span
        (Ast.Asnop_impure_mem
           { lhs = replaced_lhs
           ; op
           ; rhs = replace_struct_access offsets struct_field_to_ind rhs
           })
        stm_src
    else
      mark_with_span
        (Ast.Assign
           ( replaced_lhs
           , mark_with_span
               (Ast.Binop_impure
                  { lhs = replaced_lhs
                  ; op
                  ; rhs = replace_struct_access offsets struct_field_to_ind rhs
                  })
               stm_src ))
        stm_src
  | Postop _ -> failwith "no more postop after typecheck"
  | Annotated_stm_intermediate _ ->
    failwith "no more annotated stm intermediates after typecheck"
  | Annotated_stm (anno, mstm) ->
    mark_with_span
      (Ast.Annotated_stm
         ( process_anno offsets struct_field_to_ind anno
         , process offsets struct_field_to_ind mstm ))
      stm_src

(* Elaborates on a declaration statement. Splits up a declare that initialises a value
  into a declaration of a new variable and an assignment *)
and process_decl offsets struct_field_to_ind decl tau mstm =
  match decl with
  | Ast.New_var _ -> Ast.Declare (decl, tau, process offsets struct_field_to_ind mstm)
  (* All of them should be able to be elaborated now, try first *)
  | Ast.Init (sym, mexp) ->
    let assign_mstm =
      mark_with_pos
        (Ast.Assign
           ( mark_with_pos
               (Ast.Var { ident = sym; var_type = tau })
               Lexing.dummy_pos
               Lexing.dummy_pos
           , replace_struct_access offsets struct_field_to_ind mexp ))
        Lexing.dummy_pos
        Lexing.dummy_pos
    in
    let mstm_span = get_start_end mstm in
    Ast.Declare
      ( Ast.New_var sym
      , tau
      , mark_with_span
          (Ast.Seq (assign_mstm, process offsets struct_field_to_ind mstm))
          mstm_span )
;;

let correct_offset curr_size largest_field_size =
  Int64.((curr_size % largest_field_size) + curr_size)
;;

(* size + size of largest offset *)
let rec sizeof struct_sizes tau : Int64.t * Int64.t =
  match tau with
  | Ast.Int -> Int64.of_int 4, Int64.of_int 4
  | Ast.Bool -> Int64.of_int 4, Int64.of_int 4
  | Ast.Pointer _ -> Int64.of_int 8, Int64.of_int 8
  | Ast.Array _ -> Int64.of_int 8, Int64.of_int 8
  | Ast.Char -> Int64.one, Int64.one
  | Ast.String -> Int64.of_int 8, Int64.of_int 8
  | Ast.Struct s ->
    (match SymbolTable.find struct_sizes s with
     | Some x -> x
     | None -> failwith "struct size when calling sizeof should be defined beforehand")
  | Ast.Void -> failwith "no voids for sizeof"
  | Ast.Dummy -> failwith "no dummy for sizeof"
  | Ast.Alias _ -> failwith "no alias for sizeof"
  | Ast.Any -> failwith "no any for sizeof?"

and process_struct_sizes
  (all_struct_offsets : Int64.t Int32Table.t SymbolTable.t)
  (struct_sizes : (Int64.t * Int64.t) SymbolTable.t)
  (ident : Symbol.t)
  (fields : (Symbol.t * Ast.tau) list)
  : Int64.t * Int64.t
  =
  (*  *)
  let struct_offsets =
    match SymbolTable.find all_struct_offsets ident with
    | Some x -> x
    | None -> failwith (sprintf "struct %s doesn't exist in table" (Symbol.name ident))
  in
  let fields_ind = List.mapi fields ~f:(fun ind x -> ind, x) in
  let final_offset, largest_field_size =
    List.fold_left
      fields_ind
      ~init:(Int64.zero, Int64.zero)
      ~f:(fun (curr_offset, curr_largest) (ind, (_, tau)) ->
      let tau_size, largest_field_size = sizeof struct_sizes tau in
      let is_modulo =
        if Int64.(largest_field_size <> Int64.zero)
        then Int64.(equal (curr_offset % largest_field_size) Int64.zero)
        else true
      in
      let new_offset =
        if is_modulo
        then (
          Int32Table.set struct_offsets ~key:(Int32.of_int_trunc ind) ~data:curr_offset;
          Int64.(curr_offset + tau_size))
        else (
          let corrected_offset = correct_offset curr_offset largest_field_size in
          Int32Table.set
            struct_offsets
            ~key:(Int32.of_int_trunc ind)
            ~data:corrected_offset;
          Int64.(corrected_offset + tau_size))
      in
      new_offset, Int64.max curr_largest largest_field_size)
  in
  let final_size =
    if Int64.(largest_field_size <> Int64.zero)
    then correct_offset final_offset largest_field_size
    else Int64.zero
  in
  SymbolTable.set struct_sizes ~key:ident ~data:(final_size, largest_field_size);
  final_size, largest_field_size
;;

let elaborate_header ?(debug = false) (program_list : Ast.program) (env : Typechecker.env)
  : Int64.t Int32Table.t SymbolTable.t
    * Int32.t SymbolTable.t SymbolTable.t
    * (Int64.t * Int64.t) SymbolTable.t
  =
  let struct_tbl = env.sigma in
  let all_struct_offsets =
    SymbolTable.map struct_tbl ~f:(fun _ -> Int32Table.create ())
  in
  let struct_field_to_ind =
    SymbolTable.map struct_tbl ~f:(fun _ -> SymbolTable.create ())
  in
  (* struct to sizes and its largest offset *)
  let struct_sizes =
    SymbolTable.map struct_tbl ~f:(fun _ -> Int64.of_int (-1), Int64.of_int (-1))
  in
  let header_items =
    List.map program_list ~f:(fun mprog ->
      let prog = Mark.data mprog in
      match prog with
      | Ast.Function_Def_Anno _
      | Ast.Function_Def _
      | Ast.Function_Decl _
      | Ast.Typedef _
      | Struct_Decl _ -> mprog
      | Ast.Struct_Def { ident; fields } ->
        let (_ : Int64.t * Int64.t) =
          process_struct_sizes all_struct_offsets struct_sizes ident fields
        in
        let curr_struct =
          match SymbolTable.find struct_field_to_ind ident with
          | Some x -> x
          | None -> failwith "curr struct does not exist in field to index mapping"
        in
        List.iteri fields ~f:(fun ind (field, _) ->
          SymbolTable.set curr_struct ~key:field ~data:(Int32.of_int_trunc ind));
        mprog
      | Ast.Function_Def_Anno_Intermediate _ ->
        failwith "no more function def anno intermediate after typecheck"
      | Ast.Function_Def_Intermediate _ ->
        failwith "no more function def intermediate after typecheck"
      | Ast.Struct_Def_Intermediate _ ->
        failwith "no more struct def intermediate after typecheck")
  in
  if debug then print_from_program all_struct_offsets struct_sizes header_items;
  all_struct_offsets, struct_field_to_ind, struct_sizes
;;

let elaborate_decl
  ?(debug = false)
  (program_list : Ast.program)
  (tables :
    Int64.t Int32Table.t SymbolTable.t
    * Int32.t SymbolTable.t SymbolTable.t
    * (Int64.t * Int64.t) SymbolTable.t)
  : Ast.program * (Int64.t * Int64.t) SymbolTable.t
  =
  let all_struct_offsets, struct_field_to_ind, struct_sizes = tables in
  let elaborated_programs =
    List.map program_list ~f:(fun mprog ->
      let span = get_start_end mprog in
      let prog = Mark.data mprog in
      match prog with
      | Ast.Function_Def { ret_type; ident; params; fn_block } ->
        mark_with_span
          (Ast.Function_Def
             { ret_type
             ; ident
             ; params
             ; fn_block = process all_struct_offsets struct_field_to_ind fn_block
             })
          span
      | Ast.Function_Def_Anno { ret_type; ident; params; anno; fn_block } ->
        let new_anno = process_anno all_struct_offsets struct_field_to_ind anno in
        mark_with_span
          (Ast.Function_Def_Anno
             { ret_type
             ; ident
             ; params
             ; anno = new_anno
             ; fn_block = process all_struct_offsets struct_field_to_ind fn_block
             })
          span
      | Ast.Function_Decl _ | Ast.Typedef _ | Struct_Decl _ -> mprog
      | Ast.Struct_Def { ident; fields } ->
        let (_ : Int64.t * Int64.t) =
          process_struct_sizes all_struct_offsets struct_sizes ident fields
        in
        let curr_struct =
          match SymbolTable.find struct_field_to_ind ident with
          | Some x -> x
          | None -> failwith "curr struct does not exist in field to index mapping"
        in
        let (_ : unit) =
          List.iteri fields ~f:(fun ind (field, _) ->
            SymbolTable.set curr_struct ~key:field ~data:(Int32.of_int_trunc ind))
        in
        mprog
      | Ast.Function_Def_Intermediate _ ->
        failwith "no more function def intermediate after typecheck"
      | Ast.Function_Def_Anno_Intermediate _ ->
        failwith "no more function def anno intermediate after typecheck"
      | Ast.Struct_Def_Intermediate _ ->
        failwith "no more struct def intermediate after typecheck")
  in
  if debug then print_from_program all_struct_offsets struct_sizes elaborated_programs;
  elaborated_programs, struct_sizes
;;
