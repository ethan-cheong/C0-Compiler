(* L1 Compiler
 * Elaborated AST -> IR Translator
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 * Translates elaborated Abstract Syntax Tree into IR.
 *)
open Core
module A = Ast
module S = Symbol
module T = Tree
module SymbolTable = Type_modules.SymbolTable

(* To raise a memory exception, call raise(12) (SIGUSR1) *)
let raise_mem_exn =
  T.Function_call
    { dest = Temp.create_of_size DOUBLE (* the size of this guy doesn't matter *)
    ; ident = "raise"
    ; args = [ Const (Int (Int32.of_int_exn 12)) ]
    ; assign_res = false
    }
;;

let temp_size_of_tau : A.tau -> Temp.size = function
  | Int -> DOUBLE
  | Bool -> BYTE (* Bools now take a single byte. *)
  | Pointer _ -> QUAD
  | Array _ -> QUAD
  | Alias _ -> failwith "All aliases should have been elaborated out"
  | Void -> failwith "called size_of_tau on a void tau"
  | Any -> QUAD
  | Dummy -> failwith "Dummy should be elaborated out"
  | Struct _ -> QUAD (* I'm just leaving this as quad for now. might have to change.*)
  | String -> QUAD
  | Char -> BYTE
;;

(** [size_of_exp] returns the size of the result of evaluating [exp]. Some of 
    these are obvious; for others, like function calls, typechecking annotates
    the AST with the result types so that we know them during translation. *)
let rec size_of_exp : A.exp -> Temp.size = function
  | Var { var_type; _ } -> temp_size_of_tau var_type
  | Const { const_type; _ } -> temp_size_of_tau const_type
  | Binop_pure _ -> DOUBLE
  | Binop_impure _ -> DOUBLE
  | Unop { op; operand } ->
    (match op with
     | Not -> DOUBLE
     | _ -> size_of_exp (Mark.data operand))
  | Function_call { return_type; _ } -> temp_size_of_tau return_type
  (* All boolean expressions now give bytes. *)
  | Comparison _ -> BYTE
  | And _ -> BYTE
  | Or _ -> BYTE
  | Ternary { result_type; _ } -> temp_size_of_tau result_type
  | Alloc _ -> QUAD (* Alloc writes to an lvalue *)
  | Deref { pointer_type; _ } -> temp_size_of_tau pointer_type
  | Null_pointer -> QUAD
  | Alloc_array _ -> QUAD (* Alloc_array writes to an lvalue *)
  | Array_access { array_type; _ } -> temp_size_of_tau array_type
  | Struct_access { field_type; _ } ->
    temp_size_of_tau field_type (* idk what i'm doing.. this might be dumb*)
  | Struct_access_parse _ -> failwith "called size_of_exp on struct_access_parse"
  | Paren _ -> failwith "called size_of_exp on paren"
  | String_const _ -> QUAD (* Since they are actually pointers... *)
  | Anno_result | Anno_length _ | Cast _ -> failwith "what is the size?"
  | Anno_index | Anno_elem _ -> failwith "arr indexes not implemented yet"
  | Forall _ | Exists _ -> failwith "arr indexes not implemented yet"
;;

let trans_binop_pure = function
  | A.Plus -> T.Add
  | A.Minus -> T.Sub
  | A.Times -> T.Mul
  | A.Bitwise_or -> T.Or
  | A.Bitwise_xor -> T.Xor
  | A.Bitwise_and -> T.And
;;

let trans_binop_cmp = function
  | A.Less -> T.Lt
  | A.Less_equal -> T.Leq
  | A.Greater -> T.Gt
  | A.Greater_equal -> T.Geq
  | A.Equal -> T.Eq
  | A.Not_equal -> T.Neq
;;

let trans_binop_impure = function
  | A.Divided_by -> T.Div
  | A.Modulo -> T.Mod
  | A.Left_shift -> T.Sal
  | A.Right_shift -> T.Sar
;;

let trans_unop = function
  (* unary to binary!*)
  | A.Negative -> T.Sub
  | A.Bitwise_not -> T.Xor (* To take bitwise not, Xor with all 1 mask*)
  | A.Not -> failwith "We handle this manually this in a later stage"
;;

let func_name_of_ident ~ident ~defined_functions =
  if String.(S.name ident = "main")
  then "_c0_main"
  else if String.(S.name ident = "init")
  then "_c0_init"
  else if String.(S.name ident = "prepare")
  then "_c0_prepare"
  else if String.(S.name ident = "run")
  then "_c0_run"
  else if String.(S.name ident = "checksum")
  then "_c0_checksum"
  else if Hashtbl.mem defined_functions ident
  then "_f_" ^ S.name ident
  else S.name ident
;;

let translate_function_def
  fn_block
  params
  ident
  init_num_temps
  defined_functions
  env
  label_counter
  size_of_tau
  tau_to_tag
  anno
  ~(remove_annotations : bool)
  =
  (* Check if the mapping currently maps tau to a tag. If so, return it; if not,
     add it. 

     The tags given are just the size of the hashtbl + 1.
  
    *)
  let tagof tau =
    Hashtbl.find_or_add tau_to_tag tau ~default:(fun () ->
      Int64.of_int_exn (Hashtbl.length tau_to_tag + 1))
  in
  (* First, separate out the anno (spec list) into requires and ensures. *)
  let requires_specs, ensures_specs =
    List.partition_tf anno ~f:(fun spec ->
      match spec with
      | A.Requires _ -> true
      | Ensures _ -> false
      | _ -> failwith "function anno should only contain Requires and Ensures")
  in
  let elaborated_ast = fn_block in
  (* Add all params to the environment so they can be referenced*)
  List.iter params ~f:(fun (tau, param) ->
    let t = Temp.create_of_size (temp_size_of_tau tau) in
    Hashtbl.set env ~key:param ~data:t);
  (* Commands are appended to a doubly-linked list. *)
  let result_dll = Doubly_linked.create () in
  let append_to_dll list =
    Doubly_linked.transfer ~src:(Doubly_linked.of_list list) ~dst:result_dll
  in
  let function_args =
    List.map params ~f:(fun (_, param) -> Tree.Temp (Hashtbl.find_exn env param))
  in
  let caller_ident = ident in
  let func_name = func_name_of_ident ~ident ~defined_functions in
  (* if there are any function calls NOT in the tail recursive position, then 
       the function is not tail recursive. *)
  let tail_rec_position = ref true in
  (* Don't spill to the stack if the function isn't even recursive. *)
  let recursive = ref false in
  let check_tail_rec_mexp (mexp : Ast.mexp) =
    match Mark.data mexp with
    | Function_call _ -> tail_rec_position := false
    | _ -> ()
  in
  let next_label () =
    incr label_counter;
    !label_counter
  in
  (* Dummy result to be replaced before Anno_result translation *)
  let current_return_value = ref (T.Const (String "DUMMY RETURN VALUE")) in
  (* In the lecture notes, translation of expressions returns a (ins, res) tuple
      such that ins is a list of stms with side effects, and res is a pure expression
      with the result of the computation.
      Here, we only return res, and immediately append ins to the global DLL. 
      tail_recursive is a special flag we use only to mark tail-recursive functions.
      If address_of is true, this returns the address of the expression, similar to 
      the & operator in the lecture notes. *)
  (* Dummy result to be replaced before Anno_elem translation *)
  let current_array_index_temp = ref (T.Const (String "DUMMY ARRAY INDEX")) in
  let current_array_temp = ref (T.Const (String "DUMMY ARRAY")) in
  let rec trans_exp ?(call_as_stm = false) ?(address_of = false) (exp : A.exp) =
    match exp with
    (*
    Forall should resolve to a boolean; it requires that condition is true for 
    each element of arr.
    
    tr(forall(arr, condition)) = (
      i <- 0;
      a <- res(arr); 
      acc <- True;
      if a == 0 then mem_exn
      else address_calc:
      mem_exn:;
        exception(mem);
      address_calc:
        n <- M[-8(a)] // 32 bit
      
      goto while_loop_check;
      while_loop_body: 
      c <- res(condition)
      acc <- acc && (c) 
      i <- i + 1;
      while_loop_check: if i < n then while_loop_body else while_loop_end
      while_loop_end:  
    )
    acc
    *)
    | Forall { arr; condition } ->
      let label_id = next_label () in
      let mem_exn_label = "forall_mem_exn" ^ func_name, label_id in
      let address_calc = "forall_addr_calc" ^ func_name, label_id in
      let while_loop_check_label = "forall_while_loop_check" ^ func_name, label_id in
      let while_loop_body_label = "forall_while_loop_body" ^ func_name, label_id in
      let while_loop_end_label = "forall_while_loop_end" ^ func_name, label_id in
      let array_addr_result = trans_mexp arr in
      let a = Temp.create_of_size QUAD in
      let i = Temp.create_of_size DOUBLE in
      current_array_index_temp := Temp i;
      current_array_temp := Temp a;
      let n = Temp.create_of_size DOUBLE in
      let acc = Temp.create_of_size BYTE in
      let c = Temp.create_of_size BYTE in
      append_to_dll
        [ T.Move { src = Const (Int Int32.zero); dest = i }
        ; Move { src = array_addr_result; dest = a }
        ; Move { src = Const (Byte Int32.one); dest = acc }
        ; If
            { condition = Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
            ; lt = mem_exn_label
            ; lf = address_calc
            }
        ; Label mem_exn_label
        ; raise_mem_exn
        ; Label address_calc
        ; Memory_read
            { dest = Temp n
            ; base = Temp a
            ; disp = Int32.of_int_exn (-8)
            ; index = Const (Int Int32.zero)
            ; scale = 0
            }
        ; Goto while_loop_check_label
        ; Label while_loop_body_label
        ];
      let condition_result = trans_mexp condition in
      append_to_dll
        [ T.Move { dest = c; src = condition_result }
        ; Move { dest = acc; src = Binop_pure { lhs = Temp acc; rhs = Temp c; op = And } }
        ; Move
            { dest = i
            ; src = Binop_pure { lhs = Temp i; rhs = Const (Int Int32.one); op = Add }
            }
        ; Goto while_loop_check_label
        ; Label while_loop_check_label
        ; If
            { condition = Binop_cmp { lhs = Temp i; rhs = Temp n; op = Lt }
            ; lt = while_loop_body_label
            ; lf = while_loop_end_label
            }
        ; Label while_loop_end_label
        ];
      T.Temp acc
    (* The translation of exists follows a very similar idea to forall; we just
    change the starting state and the updates of the accumulator.
     tr(exists(arr, condition)) = (
      i <- 0;
      a <- res(arr); 
      acc <- False;
      if a == 0 then mem_exn
      else address_calc:
      mem_exn:;
        exception(mem);
      address_calc:
        n <- M[-8(a)] // 32 bit
      
      goto while_loop_check;
      while_loop_body: 
      c <- res(condition)
      acc = acc || (c) 
      i <- i + 1;
      while_loop_check: if i < n then while_loop_body else while_loop_end
      while_loop_end:  
    )
    acc
    *)
    | Exists { arr; condition } ->
      let label_id = next_label () in
      let mem_exn_label = "exists_mem_exn" ^ func_name, label_id in
      let address_calc = "exists_addr_calc" ^ func_name, label_id in
      let while_loop_check_label = "exists_while_loop_check" ^ func_name, label_id in
      let while_loop_body_label = "exists_while_loop_body" ^ func_name, label_id in
      let while_loop_end_label = "exists_while_loop_end" ^ func_name, label_id in
      let array_addr_result = trans_mexp arr in
      let a = Temp.create_of_size QUAD in
      let i = Temp.create_of_size DOUBLE in
      current_array_index_temp := Temp i;
      current_array_temp := Temp a;
      let n = Temp.create_of_size DOUBLE in
      let acc = Temp.create_of_size BYTE in
      let c = Temp.create_of_size BYTE in
      append_to_dll
        [ T.Move { src = Const (Int Int32.zero); dest = i }
        ; Move { src = array_addr_result; dest = a }
        ; Move { src = Const (Byte Int32.zero); dest = acc }
        ; If
            { condition = Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
            ; lt = mem_exn_label
            ; lf = address_calc
            }
        ; Label mem_exn_label
        ; raise_mem_exn
        ; Label address_calc
        ; Memory_read
            { dest = Temp n
            ; base = Temp a
            ; disp = Int32.of_int_exn (-8)
            ; index = Const (Int Int32.zero)
            ; scale = 0
            }
        ; Goto while_loop_check_label
        ; Label while_loop_body_label
        ];
      let condition_result = trans_mexp condition in
      append_to_dll
        [ T.Move { dest = c; src = condition_result }
        ; Move { dest = acc; src = Binop_pure { lhs = Temp acc; rhs = Temp c; op = Or } }
        ; Move
            { dest = i
            ; src = Binop_pure { lhs = Temp i; rhs = Const (Int Int32.one); op = Add }
            }
        ; Goto while_loop_check_label
        ; Label while_loop_check_label
        ; If
            { condition = Binop_cmp { lhs = Temp i; rhs = Temp n; op = Lt }
            ; lt = while_loop_body_label
            ; lf = while_loop_end_label
            }
        ; Label while_loop_end_label
        ];
      T.Temp acc
    (* Anno_index can only ever appear in a Forall/Exists condition. *)
    | Anno_index -> !current_array_index_temp
    (* Anno_result can only ever appear in an ensures spec. We mark what result
       is about to be returned so we can use that in anno_result. *)
    | Anno_result -> !current_return_value
    (*
      tr(\length(e)):
         ins(arr_exp);
          a <- res(arr_exp); 
          if a == 0 then mem_exn
          else address_calc:
          mem_exn:;
            exception(mem);
          address_calc:
            t <- M[-8(a1)] // 32 bit
          return t 
    *)
    | Anno_length array ->
      let label_id = next_label () in
      let mem_exn_label = "anno_length_mem_exn" ^ func_name, label_id in
      let address_calc = "anno_length_addr_calc" ^ func_name, label_id in
      let array_addr_result = trans_mexp array in
      let a = Temp.create_of_size QUAD in
      let t = Temp.create_of_size DOUBLE in
      append_to_dll T.[ Move { src = array_addr_result; dest = a } ];
      append_to_dll
        T.
          [ If
              { condition =
                  Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
              ; lt = mem_exn_label
              ; lf = address_calc
              }
          ; Label mem_exn_label
          ; raise_mem_exn
          ; Label address_calc
          ; Memory_read
              { dest = Temp t
              ; base = Temp a
              ; disp = Int32.of_int_exn (-8)
              ; index = Const (Int Int32.zero)
              ; scale = 0
              }
          ];
      T.Temp t
    | Cast { pointer_type; operand; orig_type } ->
      (match pointer_type with
       (*
          tr(cast(void, e)) = 
          (
        ins(e);
        a <- res(e)
        // allocate 16 bytes; one for the pointer, one for the tag 
        if a == 0 then tag_null_pointer else tag
        tag:
          t1 <- calloc(8, 2);
          M[(t1)] <- tagof(orig_type)
          t2 <- t1 + 8;
          M[(t2)] <- a
          goto tag_end
        tag_null_pointer:
          t2 <- 0
          goto tag_end
        tag_end
      )
        t2
      *)
       | A.Void ->
         check_tail_rec_mexp operand;
         let res = trans_mexp operand in
         let label_id = next_label () in
         let tag_label = "tag" ^ func_name, label_id in
         let tag_null_pointer_label = "tag_null_pointer" ^ func_name, label_id in
         let tag_end_label = "tag_label" ^ func_name, label_id in
         let a = Temp.create_of_size QUAD in
         let t0 = Temp.create_of_size QUAD in
         let t1 = Temp.create_of_size QUAD in
         let t2 = Temp.create_of_size QUAD in
         append_to_dll
           [ T.Move { src = res; dest = a }
           ; T.If
               { condition =
                   T.Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
               ; lt = tag_null_pointer_label
               ; lf = tag_label
               }
           ; Label tag_label
           ; Function_call
               { dest = t1
               ; ident = "calloc"
               ; args =
                   [ Const (Int (Int32.of_int_exn 8)); Const (Int (Int32.of_int_exn 1)) ]
               ; assign_res = true
               }
           ; Comment "Tagof orig_type located in the src of the next move"
           ; Move { src = Addr_const (tagof orig_type); dest = t0 }
           ; Memory_write
               { src = Temp t0
               ; disp = Int32.zero
               ; base = Temp t1
               ; scale = 0
               ; index = Const (Int Int32.zero)
               }
           ; Move
               { dest = t2
               ; src =
                   Binop_pure
                     { lhs = Temp t1; op = Add; rhs = Addr_const (Int64.of_int_exn 8) }
               }
           ; Memory_write
               { src = Temp a
               ; disp = Int32.zero
               ; base = Temp t2
               ; scale = 0
               ; index = Const (Int Int32.zero)
               }
           ; Goto tag_end_label
           ; Label tag_null_pointer_label
           ; Move { src = Addr_const Int64.zero; dest = t2 }
           ; Goto tag_end_label
           ; Label tag_end_label
           ];
         Temp t2
       (*
          tr(cast(pointer_type, e)) = 
          (
        ins(e);
        a <- res(e)
        if a == 0 then untag_null_pointer else untag
        untag:
          t1 <- a-8
          t2 <- M[(t1)]
          t3 <- tagof(pointer_type)
          if t2 == t3 then untag_success else untag_fail
        untag_fail: 
          exception(mem);
        untag_success:
          t4 <- M[(a)]
          goto untag_end
        untag_null_pointer:
          t4 <- 0
          goto untag_end
        untag_end:
      )
        t4 
        *)
       | _ ->
         check_tail_rec_mexp operand;
         let res = trans_mexp operand in
         let label_id = next_label () in
         let untag_label = "untag" ^ func_name, label_id in
         let untag_fail_label = "untag_fail" ^ func_name, label_id in
         let untag_success_label = "untag_success" ^ func_name, label_id in
         let untag_null_pointer_label = "untag_null_pointer" ^ func_name, label_id in
         let untag_end_label = "untag_label" ^ func_name, label_id in
         let a = Temp.create_of_size QUAD in
         let t1 = Temp.create_of_size QUAD in
         let t2 = Temp.create_of_size QUAD in
         let t3 = Temp.create_of_size QUAD in
         let t4 = Temp.create_of_size QUAD in
         append_to_dll
           [ T.Move { src = res; dest = a }
           ; T.If
               { condition =
                   T.Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
               ; lt = untag_null_pointer_label
               ; lf = untag_label
               }
           ; Label untag_label
           ; Move
               { src =
                   Binop_pure
                     { lhs = Temp a; rhs = Addr_const (Int64.of_int_exn 8); op = Sub }
               ; dest = t1
               }
           ; Memory_read
               { dest = Temp t2
               ; disp = Int32.zero
               ; base = Temp t1
               ; index = Const (Int Int32.zero)
               ; scale = 0
               }
           ; Comment "tagof pointer_type in the src of next move"
           ; Move { src = Addr_const (tagof pointer_type); dest = t3 }
           ; If
               { condition = Binop_cmp { lhs = Temp t2; rhs = Temp t3; op = Eq }
               ; lt = untag_success_label
               ; lf = untag_fail_label
               }
           ; Label untag_fail_label
           ; raise_mem_exn
           ; Label untag_success_label
           ; Memory_read
               { dest = Temp t4
               ; disp = Int32.zero
               ; base = Temp a
               ; index = Const (Int Int32.zero)
               ; scale = 0
               }
           ; Goto untag_end_label
           ; Label untag_null_pointer_label
           ; Move { src = Addr_const Int64.zero; dest = t4 }
           ; Goto untag_end_label
           ; Label untag_end_label
           ];
         Temp t4)
    | String_const s ->
      T.Const (T.String s) (* String literals are passed down for now. *)
    | A.Struct_access_parse _ ->
      failwith "struct access parse should be elaborated out before translation."
    | A.Paren _ -> failwith "parens should have been elaborated out before translation."
    | A.Var { ident; _ } -> T.Temp (Hashtbl.find_exn env ident)
    | A.Const { value; const_type } ->
      (match const_type with
       | A.Int -> T.Const (T.Int value)
       | Bool -> T.Const (T.Byte value)
       | Char -> T.Const (T.Byte value)
       | _ ->
         failwith
           (Printf.sprintf
              "%s should not be located in an AST const."
              (A.Print.pp_tau const_type)))
    (* tr(e1 + e2) = ([ins(e1); ins(e2)], e1+e2) *)
    | A.Binop_pure { lhs; op; rhs } ->
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      let lhs_res = trans_mexp lhs in
      (* because we force the evaluation of the left subtree here, this does DFS *)
      let rhs_res = trans_mexp rhs in
      (match lhs_res, rhs_res with
       (* Constant folding here *)
       | T.Const (Int a), T.(Const (Int b)) ->
         Int32.(
           (match op with
            | Plus -> T.Const (Int (a + b))
            | Minus -> T.Const (Int (a - b))
            | Times -> T.Const (Int (a * b))
            | Bitwise_or -> T.Const (Int (a lor b))
            | Bitwise_xor -> T.Const (Int (a lxor b))
            | Bitwise_and -> T.Const (Int (a land b))))
       | _ -> T.Binop_pure { lhs = lhs_res; op = trans_binop_pure op; rhs = rhs_res })
    | A.Unop { op = A.Negative; operand = e } ->
      check_tail_rec_mexp e;
      let res = trans_mexp e in
      T.Binop_pure
        { op = trans_unop A.Negative; lhs = T.Const (T.Int Int32.zero); rhs = res }
    | A.Unop { op = A.Bitwise_not; operand = e } ->
      check_tail_rec_mexp e;
      let res = trans_mexp e in
      T.Binop_pure
        { op = trans_binop_pure A.Bitwise_xor; lhs = T.Const MAX_INT; rhs = res }
    (* Expression e that happens to be boolean:
         tr (e) = (
          [cp(e,l1, l2) ;
          l1: ;
          t <- 1; 
          goto l3; 
          l2: ;
          t <- 0;
          goto l3;
          l3: ],
          t
         )
      *)
    | A.Unop { operand; op = A.Not } ->
      append_to_dll T.[ Comment "boolean unop start" ];
      check_tail_rec_mexp operand;
      let label_id = next_label () in
      let true_label = "bool_exp_true" ^ func_name, label_id in
      let false_label = "bool_exp_false" ^ func_name, label_id in
      let end_label = "bool_exp_end" ^ func_name, label_id in
      (* These can only be called on doubles *)
      let t = Temp.create_of_size BYTE in
      trans_boolean_exp exp true_label false_label;
      append_to_dll
        T.
          [ Label true_label
          ; Move { dest = t; src = Const (Byte Int32.one) }
          ; Goto end_label
          ; Label false_label
          ; Move { dest = t; src = Const (Byte Int32.zero) }
          ; Goto end_label
          ; Label end_label
          ; Comment "boolean unop end"
          ];
      T.Temp t
      (* Expression e that happens to be boolean:
         tr (e) = (
          [cp(e,l1, l2) ;
          l1: ;
          t <- 1; 
          goto l3; 
          l2: ;
          t <- 0;
          goto l3;
          l3: ],
          t
         )
      *)
    | A.Comparison { lhs; rhs; _ } | A.And { lhs; rhs } | A.Or { lhs; rhs } ->
      append_to_dll T.[ Comment "boolean binop start" ];
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      let label_id = next_label () in
      let true_label = "bool_exp_true" ^ func_name, label_id in
      let false_label = "bool_exp_false" ^ func_name, label_id in
      let end_label = "bool_exp_end" ^ func_name, label_id in
      let t = Temp.create_of_size BYTE in
      trans_boolean_exp exp true_label false_label;
      append_to_dll
        [ T.Label true_label
        ; T.Move { dest = t; src = Const (Byte Int32.one) }
        ; T.Goto end_label
        ; T.Label false_label
        ; T.Move { dest = t; src = Const (Byte Int32.zero) }
        ; T.Goto end_label
        ; T.Label end_label
        ; T.Comment "boolean binop end"
        ];
      T.Temp t
    (* tr(e1 @ e2) = ([ins(e1); ins(e2); t<- res(e1) @ res(e2)], t) *)
    | A.Binop_impure { op; lhs; rhs } ->
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      let t = Temp.create_of_size DOUBLE in
      (* Same effect as adding ins(e1) to the output *)
      let lhs_res = trans_mexp lhs in
      let rhs_res = trans_mexp rhs in
      append_to_dll
        [ T.Binop_impure
            { lhs = lhs_res; op = trans_binop_impure op; rhs = rhs_res; dest = t }
        ];
      T.Temp t
    (* tr(c ? e1 : e2) -> 
         ([
          cp(c, l1, l2);
          l1: ;
          ins(e1);
          t <- res(e1);
          goto l3;
          l2: ;
          ins(e2);
          t <- res(e2);
          l3:
         ]
         ,t
         )
      *)
    | Ternary { condition; lhs; rhs; result_type } ->
      append_to_dll [ T.Comment "Ternary expression start" ];
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      let label_id = next_label () in
      let ternary_true_label = "ternary_true" ^ func_name, label_id in
      let ternary_false_label = "ternary_false" ^ func_name, label_id in
      let ternary_end_label = "ternary_end" ^ func_name, label_id in
      let t = Temp.create_of_size (temp_size_of_tau result_type) in
      trans_boolean_exp (Mark.data condition) ternary_true_label ternary_false_label;
      append_to_dll [ T.Label ternary_true_label ];
      let lhs_res = trans_mexp lhs in
      append_to_dll
        [ T.Move { dest = t; src = lhs_res }
        ; T.Goto ternary_end_label
        ; T.Label ternary_false_label
        ];
      let rhs_res = trans_mexp rhs in
      append_to_dll
        [ T.Move { dest = t; src = rhs_res }
        ; T.Goto ternary_end_label
        ; T.Label ternary_end_label
        ; T.Comment "Ternary expression end"
        ];
      T.Temp t
      (* tr(f(e1,...,en)) = ([ins(e1);...;ins(en);t<-f(res(e1), ..., res(en))], t) *)
    | Function_call { ident; args; return_type } ->
      append_to_dll [ T.Comment ("call " ^ Symbol.name ident ^ " start") ];
      if S.(ident = caller_ident) then recursive := true;
      let t =
        match return_type with
        | Void -> Temp.create_of_size DOUBLE (* Dummy temp *)
        | _ -> Temp.create_of_size (temp_size_of_tau return_type)
      in
      let res_args =
        List.map args ~f:(fun arg ->
          check_tail_rec_mexp arg;
          trans_mexp arg)
      in
      (* translate each element of the list in order *)
      let callee_name = func_name_of_ident ~ident ~defined_functions in
      (* If you call as statement, you don't assign result *)
      append_to_dll
        [ T.Function_call
            { dest = t
            ; ident = callee_name
            ; args = res_args
            ; assign_res = not call_as_stm
            }
        ; T.Comment ("call " ^ Symbol.name ident ^ " end")
        ];
      T.Temp t
    (* The null pointer evaluates to the address 0. *)
    | Null_pointer -> Addr_const Int64.zero
    (* Call alloc, and then put the result into a temp. *)
    | Alloc tau ->
      append_to_dll [ T.Comment ("alloc " ^ A.Print.pp_tau tau ^ " start") ];
      let t = Temp.create_of_size QUAD in
      let n_items = T.Const (Int Int32.one) in
      (* This is an addr_const, in case we have to alloc a massive struct. *)
      let size = T.Addr_const (size_of_tau tau) in
      append_to_dll
        [ T.Function_call
            { dest = t; ident = "calloc"; args = [ n_items; size ]; assign_res = true }
        ; T.Comment ("alloc " ^ A.Print.pp_tau tau ^ " end")
        ];
      T.Temp t
    (* Safe pointer deref:
        tr(deref(e)) -> 
         ([
        ins(e);
        t1 <- res(e); 
        if t1 == 0 then mem_exn else deref;
        mem_exn:;
          exception(mem);
        deref:;
          t2 <- Mem_read(t1) 
         ]
         ,t2
         )
        
         If in address-of mode, just return the address.
      *)
    | Deref { address; pointer_type } ->
      (* Typechecking ensures that this is a pointer *)
      check_tail_rec_mexp address;
      if address_of
      then trans_mexp address
      else (
        append_to_dll
          [ T.Comment ("deref " ^ A.Print.pp_tau pointer_type ^ " pointer start") ];
        let label_id = next_label () in
        let deref_null_ptr_label = "deref_null_ptr" ^ func_name, label_id in
        let deref_success_label = "deref_success" ^ func_name, label_id in
        let address_result = trans_mexp address in
        let t1 = Temp.create_of_size QUAD in
        append_to_dll T.[ Move { dest = t1; src = address_result } ];
        let t2 = Temp.create_of_size (temp_size_of_tau pointer_type) in
        append_to_dll
          T.
            [ If
                { condition =
                    Binop_cmp { lhs = Temp t1; op = Eq; rhs = Addr_const Int64.zero }
                ; lt = deref_null_ptr_label
                ; lf = deref_success_label
                }
            ; Label deref_null_ptr_label
            ; raise_mem_exn
            ; Label deref_success_label
            ; Memory_read
                { dest = Temp t2
                ; base = Temp t1
                ; index = Const (Int Int32.zero)
                ; disp = Int32.zero
                ; scale = 0
                }
            ; Comment ("deref " ^ A.Print.pp_tau pointer_type ^ " pointer end")
            ];
        T.Temp t2)
    (*
        Safe Array Alloc with Bool/Chars:
        ins(size);
        n <- res(size);
        if n < 0 then mem_exn else arr_alloc
        mem_exn: 
          exception(mem);
        arr_alloc:
        t3 <-zero-ext- n
        t1 <- calloc(t3, 1)
        M[(t1)] <- n
        t2 <- t1 + 8;
        t2 

        Safe array alloc:
        tr(alloc_array(array_type; size)) ->
        ins(size);
        n <- res(size);
        if n < 0 then mem_exn else arr_alloc
        mem_exn: 
          exception(mem);
        arr_alloc:
        
        // Idea: Let num_doubles = (size_of_tau arr_type * size / 4) + 2 
        // Then calloc(num_doubles, 4)
        
        t3 <-zero-ext- n
        t4 <- t3 * (size_of_tau arr_type / 4)
        t5 <- t4 + 2

        t1 <- calloc(t5, 4)
        M[(t1)] <- n
        t2 <- t1 + 8;
        t2
      *)
    | Alloc_array { array_type; size } ->
      (match array_type with
       | Bool | Char ->
         append_to_dll
           T.[ Comment ("alloc " ^ A.Print.pp_tau array_type ^ " array start") ];
         check_tail_rec_mexp size;
         let n_items_temp = Temp.create_of_size DOUBLE in
         let label_id = next_label () in
         let neg_len_array_alloc = "neg_len_arr_alloc" ^ func_name, label_id in
         let arr_alloc = "arr_alloc" ^ func_name, label_id in
         let n_items_result = trans_mexp size in
         append_to_dll
           T.
             [ Move { src = n_items_result; dest = n_items_temp }
             ; If
                 { condition =
                     Binop_cmp
                       { lhs = Temp n_items_temp; op = Lt; rhs = Const (Int Int32.zero) }
                 ; lt = neg_len_array_alloc
                 ; lf = arr_alloc
                 }
             ; Label neg_len_array_alloc
             ; raise_mem_exn
             ; Label arr_alloc
             ];
         let t1 = Temp.create_of_size QUAD in
         let t2 = Temp.create_of_size QUAD in
         let t3 = Temp.create_of_size QUAD in
         append_to_dll
           T.
             [ Move_zero_extend { dest = t3; src = Temp n_items_temp }
             ; Function_call
                 { dest = t1
                 ; ident = "calloc"
                 ; args = [ Temp t3; Const (Int (Int32.of_int_exn 1)) ]
                 ; assign_res = true
                 }
               (* Store number of items in the first elem of array *)
             ; Memory_write
                 { base = Temp t1
                 ; src = Temp n_items_temp
                 ; disp = Int32.zero
                 ; index = Const (Int Int32.zero)
                 ; scale = 0
                 }
             ; Move
                 { src =
                     Binop_pure
                       { op = Add; lhs = Temp t1; rhs = Addr_const (Int64.of_int_exn 8) }
                 ; dest = t2
                 }
             ; Comment ("alloc " ^ A.Print.pp_tau array_type ^ " array end")
             ];
         Temp t2
       | _ ->
         append_to_dll
           T.[ Comment ("alloc " ^ A.Print.pp_tau array_type ^ " array start") ];
         check_tail_rec_mexp size;
         let n_items_temp = Temp.create_of_size DOUBLE in
         let label_id = next_label () in
         let neg_len_array_alloc = "neg_len_arr_alloc" ^ func_name, label_id in
         let arr_alloc = "arr_alloc" ^ func_name, label_id in
         let n_items_result = trans_mexp size in
         append_to_dll
           T.
             [ Move { src = n_items_result; dest = n_items_temp }
             ; If
                 { condition =
                     Binop_cmp
                       { lhs = Temp n_items_temp; op = Lt; rhs = Const (Int Int32.zero) }
                 ; lt = neg_len_array_alloc
                 ; lf = arr_alloc
                 }
             ; Label neg_len_array_alloc
             ; raise_mem_exn
             ; Label arr_alloc
             ];
         let t1 = Temp.create_of_size QUAD in
         let t2 = Temp.create_of_size QUAD in
         let t3 = Temp.create_of_size QUAD in
         let t4 = Temp.create_of_size QUAD in
         let t5 = Temp.create_of_size QUAD in
         append_to_dll
           T.
             [ Move_zero_extend { dest = t3; src = Temp n_items_temp }
             ; Move
                 { dest = t4
                 ; src =
                     Binop_pure
                       { op = Mul
                       ; lhs = Temp t3
                       ; rhs =
                           Addr_const Int64.(size_of_tau array_type / of_int_exn 4)
                           (* size_of_tau always returns a multiple of 4. *)
                       }
                 }
             ; Move
                 { dest = t5
                 ; src =
                     Binop_pure
                       { op = Add; lhs = Temp t4; rhs = Addr_const (Int64.of_int_exn 2) }
                 }
             ; Function_call
                 { dest = t1
                 ; ident = "calloc"
                 ; args = [ Temp t5; Const (Int (Int32.of_int_exn 4)) ]
                 ; assign_res = true
                 }
               (* Store number of items in the first elem of array *)
             ; Memory_write
                 { base = Temp t1
                 ; src = Temp n_items_temp
                 ; disp = Int32.zero
                 ; index = Const (Int Int32.zero)
                 ; scale = 0
                 }
             ; Move
                 { src =
                     Binop_pure
                       { op = Add; lhs = Temp t1; rhs = Addr_const (Int64.of_int_exn 8) }
                 ; dest = t2
                 }
             ; Comment ("alloc " ^ A.Print.pp_tau array_type ^ " array end")
             ];
         Temp t2)
      (* 
          Safe struct/irregular shaped array access:
          ins(arr_exp);
          a <- res(arr_exp); 
          ins (index_exp);
          i <- res (index_exp);
          if a == 0 then mem_exn
          else address_calc:
          address_calc:
            t2 <- M[-8(a1)] // 32 bit
          idx_check_neg:
            if (i < 0) then mem_exn
            else idx_check_pos
          idx_check_pos:
            if (i >= t2) then mem_exn
            else arr_access
          mem_exn:;
            exception(mem);
          arr_access:;
            i3 <-zero-ext- i .  /// 64 bit
            a4 <- i3 * sizeof(tau) // 64 bit const
            a5 = a + a4 // 64 bit
            t6 <- Mem_read(a5)
          return t6
          *)
    | Array_access { array; index; array_type } ->
      append_to_dll
        T.
          [ Comment
              ("access " ^ A.Print.pp_tau array_type ^ " array start (irregular shape)")
          ];
      check_tail_rec_mexp array;
      check_tail_rec_mexp index;
      let label_id = next_label () in
      let mem_exn_label = "arr_deref_mem_exn" ^ func_name, label_id in
      let address_calc = "arr_access_addr_calc" ^ func_name, label_id in
      let idx_check_neg = "arr_access_idx_check_neg" ^ func_name, label_id in
      let idx_check_pos = "arr_access_idx_check_pos" ^ func_name, label_id in
      let success_label = "arr_access" ^ func_name, label_id in
      let array_addr_result = trans_mexp array in
      let a = Temp.create_of_size QUAD in
      append_to_dll T.[ Move { src = array_addr_result; dest = a } ];
      let index_result = trans_mexp index in
      let i = Temp.create_of_size DOUBLE in
      append_to_dll
        T.
          [ Comment "i contained in dest of the next mov:"
          ; Move { src = index_result; dest = i }
          ; If
              { condition =
                  Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
              ; lt = mem_exn_label
              ; lf = address_calc
              }
          ; Label address_calc
          ];
      let t2 = Temp.create_of_size DOUBLE in
      append_to_dll
        T.
          [ Memory_read
              { dest = Temp t2
              ; base = Temp a
              ; disp = Int32.of_int_exn (-8)
              ; index = Const (Int Int32.zero)
              ; scale = 0
              }
          ; Goto idx_check_neg
          ; Label idx_check_neg
          ; If
              { condition =
                  Binop_cmp { lhs = Temp i; op = Lt; rhs = Const (Int Int32.zero) }
              ; lt = mem_exn_label
              ; lf = idx_check_pos
              }
          ; Label idx_check_pos
          ; If
              { condition = Binop_cmp { lhs = Temp i; op = Geq; rhs = Temp t2 }
              ; lt = mem_exn_label
              ; lf = success_label
              }
          ; Label mem_exn_label
          ; raise_mem_exn
          ; Label success_label
          ];
      let i3 = Temp.create_of_size QUAD in
      let a4 = Temp.create_of_size QUAD in
      append_to_dll
        T.
          [ Move_zero_extend { src = Temp i; dest = i3 }
          ; Move
              { src =
                  Binop_pure
                    { op = Mul; lhs = Temp i3; rhs = Addr_const (size_of_tau array_type) }
              ; dest = a4
              }
          ];
      let a5 = Temp.create_of_size QUAD in
      append_to_dll
        T.
          [ Move { dest = a5; src = Binop_pure { op = Add; lhs = Temp a; rhs = Temp a4 } }
          ];
      (* Whether we return the address depends on if we are in addr_of mode. *)
      (match address_of with
       | true ->
         append_to_dll
           T.
             [ Comment
                 ("access " ^ A.Print.pp_tau array_type ^ " array end (irregular shape)")
             ];
         Temp a5
       | false ->
         let t6 = Temp.create_of_size (temp_size_of_tau array_type) in
         append_to_dll
           T.
             [ Memory_read
                 { dest = Temp t6
                 ; disp = Int32.zero
                 ; base = Temp a5
                 ; index = Const (Int Int32.zero)
                 ; scale = 0
                 }
             ; Comment
                 ("access " ^ A.Print.pp_tau array_type ^ " array end (irregular shape)")
             ];
         Temp t6)
    (* Similar to array accesses. *)
    | Anno_elem tau ->
      let label_id = next_label () in
      let mem_exn_label = "anno_elem_deref_mem_exn" ^ func_name, label_id in
      let address_calc = "anno_elem_addr_calc" ^ func_name, label_id in
      let idx_check_neg = "anno_elem_idx_check_neg" ^ func_name, label_id in
      let idx_check_pos = "anno_elem_idx_check_pos" ^ func_name, label_id in
      let success_label = "anno_elem" ^ func_name, label_id in
      let a = !current_array_temp in
      let i = !current_array_index_temp in
      append_to_dll
        T.
          [ If
              { condition = Binop_cmp { lhs = a; rhs = Addr_const Int64.zero; op = Eq }
              ; lt = mem_exn_label
              ; lf = address_calc
              }
          ; Label address_calc
          ];
      let t2 = Temp.create_of_size DOUBLE in
      append_to_dll
        T.
          [ Memory_read
              { dest = Temp t2
              ; base = a
              ; disp = Int32.of_int_exn (-8)
              ; index = Const (Int Int32.zero)
              ; scale = 0
              }
          ; Goto idx_check_neg
          ; Label idx_check_neg
          ; If
              { condition = Binop_cmp { lhs = i; op = Lt; rhs = Const (Int Int32.zero) }
              ; lt = mem_exn_label
              ; lf = idx_check_pos
              }
          ; Label idx_check_pos
          ; If
              { condition = Binop_cmp { lhs = i; op = Geq; rhs = Temp t2 }
              ; lt = mem_exn_label
              ; lf = success_label
              }
          ; Label mem_exn_label
          ; raise_mem_exn
          ; Label success_label
          ];
      let i3 = Temp.create_of_size QUAD in
      let a4 = Temp.create_of_size QUAD in
      append_to_dll
        T.
          [ Move_zero_extend { src = i; dest = i3 }
          ; Move
              { src =
                  Binop_pure
                    { op = Mul; lhs = Temp i3; rhs = Addr_const (size_of_tau tau) }
              ; dest = a4
              }
          ];
      let a5 = Temp.create_of_size QUAD in
      append_to_dll
        T.[ Move { dest = a5; src = Binop_pure { op = Add; lhs = a; rhs = Temp a4 } } ];
      (match tau with
       | Struct _ -> Temp a5
       (* When we have a struct array, treat it like "address of mode" *)
       | _ ->
         let t6 = Temp.create_of_size (temp_size_of_tau tau) in
         append_to_dll
           T.
             [ Memory_read
                 { dest = Temp t6
                 ; disp = Int32.zero
                 ; base = Temp a5
                 ; index = Const (Int Int32.zero)
                 ; scale = 0
                 }
             ];
         Temp t6)
      (* Safe struct access when offset is less than 2^32 max value:
          a <- &s;  // quad
          if a == 0 then mem_exn else struct_access
          mem_exn:
            exception(mem)
          struct_access:
            if address of mode:
            t <- lea(offset(a, _, _))
          else:
            t <- Mem_read(offset(a, _, _))
          return t
         *)
    | Struct_access { s; offset; field_type } when Int64.(offset <= of_int_exn 2147483647)
      ->
      append_to_dll
        T.[ Comment ("access struct at offset " ^ Int64.to_string offset ^ " start") ];
      check_tail_rec_mexp s;
      let label_id = next_label () in
      let mem_exn_label = "struct_access_mem_exn" ^ func_name, label_id in
      let success_label = "struct_access" ^ func_name, label_id in
      let addr_of_struct = trans_mexp ~address_of:true s in
      let a = Temp.create_of_size QUAD in
      append_to_dll
        T.
          [ Move { src = addr_of_struct; dest = a }
          ; If
              { condition =
                  Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
              ; lt = mem_exn_label
              ; lf = success_label
              }
          ; Label mem_exn_label
          ; raise_mem_exn
          ; Label success_label
          ];
      if address_of
      then (
        let t = Temp.create_of_size QUAD in
        append_to_dll
          T.
            [ Load_effective_address
                { dest = Temp t
                ; disp = Int64.to_int32_exn offset
                ; base = Temp a
                ; index = Const (Int Int32.zero)
                ; scale = 0
                }
            ];
        Temp t)
      else (
        let t = Temp.create_of_size (temp_size_of_tau field_type) in
        append_to_dll
          T.
            [ Memory_read
                { dest = Temp t
                ; disp = Int64.to_int32_exn offset
                ; base = Temp a
                ; index = Const (Int Int32.zero)
                ; scale = 0
                }
            ];
        Temp t)
      (* Struct access with more than 64 bit offset:
        a <- &s;  // quad
        if a == 0 then mem_exn else struct_access
        mem_exn:
          exception(mem)
        struct_access:
          a1 <- a + offset 
          t2 <- Mem_read(a1) // skip this line if in addr of mode
      
        if in address of mode, return a1.
        otherwise return t2.
         *)
    | Struct_access { s; offset; field_type } ->
      append_to_dll
        T.[ Comment ("access struct at offset " ^ Int64.to_string offset ^ " start") ];
      check_tail_rec_mexp s;
      let label_id = next_label () in
      let mem_exn_label = "struct_access_mem_exn" ^ func_name, label_id in
      let success_label = "struct_access" ^ func_name, label_id in
      let addr_of_struct = trans_mexp ~address_of:true s in
      let a = Temp.create_of_size QUAD in
      let a1 = Temp.create_of_size QUAD in
      append_to_dll
        T.
          [ Move { src = addr_of_struct; dest = a }
          ; If
              { condition =
                  Binop_cmp { lhs = Temp a; rhs = Addr_const Int64.zero; op = Eq }
              ; lt = mem_exn_label
              ; lf = success_label
              }
          ; Label mem_exn_label
          ; raise_mem_exn
          ; Label success_label
          ; Move
              { src = Binop_pure { lhs = Temp a; rhs = Addr_const offset; op = Add }
              ; dest = a1
              }
          ];
      (match address_of with
       | true -> Temp a1
       | false ->
         let t2 = Temp.create_of_size (temp_size_of_tau field_type) in
         append_to_dll
           T.
             [ Memory_read
                 { base = Temp a1
                 ; dest = Temp t2
                 ; disp = Int32.zero
                 ; index = Const (Int Int32.zero)
                 ; scale = 0
                 }
             ];
         Temp t2)
  (* Wrapper for mexps *)
  and trans_mexp ?(call_as_stm = false) ?(address_of = false) mexp =
    trans_exp ~call_as_stm ~address_of (Mark.data mexp)
  (* Helper function used for translating boolean expressions. Refer to 
        Intermediate Representation lecture notes section 6. 
        Appends to DLL a sequence of commands that jumps to [if_true] if 
        [boolean_exp]; otherwise, it jumps to [if_false]. *)
  and trans_boolean_exp (boolean_exp : A.exp) (if_true : T.label) (if_false : T.label) =
    match boolean_exp with
    | Var _ | Function_call _ | Forall _ | Exists _ ->
      (* cp(e, l, l') and cp(f(...), l, l')*)
      let res = trans_exp boolean_exp in
      (* The result of this should always be a BYTE. *)
      append_to_dll
        [ T.If
            { condition = Binop_cmp { lhs = res; op = Neq; rhs = Const (Byte Int32.zero) }
            ; lt = if_true
            ; lf = if_false
            }
        ]
    | Comparison { op; lhs; rhs } ->
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      (* cp(e1?e2, l, l') *)
      let res_lhs = trans_mexp lhs in
      let res_rhs = trans_mexp rhs in
      append_to_dll
        [ T.If
            { condition =
                Binop_cmp { lhs = res_lhs; op = trans_binop_cmp op; rhs = res_rhs }
            ; lt = if_true
            ; lf = if_false
            }
        ]
    | Unop { op = Not; operand } ->
      check_tail_rec_mexp operand;
      (* cp(!e, l, l') *)
      trans_boolean_exp (Mark.data operand) if_false if_true
    | And { lhs; rhs } ->
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      (* cp(e1 && e2, l, l') *)
      let label_id = next_label () in
      let lhs_true_label = "and_lhs_true" ^ func_name, label_id in
      trans_boolean_exp (Mark.data lhs) lhs_true_label if_false;
      append_to_dll [ T.Label lhs_true_label ];
      trans_boolean_exp (Mark.data rhs) if_true if_false
    | Or { lhs; rhs } ->
      check_tail_rec_mexp lhs;
      check_tail_rec_mexp rhs;
      (* cp(e1 || e1, l, l') *)
      let label_id = next_label () in
      let lhs_false_label = "or_lhs_false" ^ func_name, label_id in
      trans_boolean_exp (Mark.data lhs) if_true lhs_false_label;
      append_to_dll [ T.Label lhs_false_label ];
      trans_boolean_exp (Mark.data rhs) if_true if_false
    | Const { value = c; const_type = A.Bool } ->
      Int32.(
        if c = zero
        then append_to_dll [ T.Goto if_false ]
        else if c = one
        then append_to_dll [ T.Goto if_true ])
    | Const { const_type = A.Int; _ } ->
      failwith
        "A non-bool const was used in a boolean expression. This should've been caught \
         in type checking"
    (* Ternary expressions can be boolean expressions as well. 
         Compute the result of the ternary, then do a conditional jump to if_true
          or if_false depending on the result.*)
    | Ternary _ | Deref _ | Struct_access _ | Array_access _ ->
      let res = trans_exp boolean_exp in
      append_to_dll
        [ T.If
            { condition =
                Binop_cmp { lhs = res; op = T.Eq; rhs = T.Const (T.Byte Int32.one) }
            ; lt = if_true
            ; lf = if_false
            }
        ]
    | _ ->
      Printf.printf "%s" (A.Print.pp_exp boolean_exp);
      failwith "A non-boolean was used in a boolean expression"
  (* Translates a statement. Env is a reference to a global symbol Hashtbl.
    The symbol table maps Symbol.t to Temp.t. Appends the result to the global 
    dll. *)
  and trans_stm (stm : A.stm) ~(remove_annotations : bool) : unit =
    match stm with
    | Declare (d, tau, sub_stm) ->
      (match d with
       | New_var id ->
         let t = Temp.create_of_size (temp_size_of_tau tau) in
         Hashtbl.set env ~key:id ~data:t;
         trans_mstm sub_stm ~remove_annotations
       | Init _ -> failwith "Declare with init should have been elaborated out")
    | A.Assign (lvalue, e) ->
      (match Mark.data lvalue with
       | Var { ident; _ } ->
         (* Assign to a variable *)
         check_tail_rec_mexp e;
         let res = trans_mexp e in
         let t = Hashtbl.find_exn env ident in
         (* An error here means we assigned a value before initializing it *)
         Hashtbl.set env ~key:ident ~data:t;
         append_to_dll [ T.Move { dest = t; src = res } ]
         (* Refer to "revisiting assignment" section of struct lecture notes.
                  tr(assign(d,e)) becomes:
                    t1 <- &(d) (* This temp is necessary for next stages *);
                    ins(e);
                    t2 <- res(e);
                    if t1 = 0 then mem_exn else assign
                  mem_exn:
                    raise(12);
                  assign:
                    t2 -> M[t1]
                    // Mem_write(src = t2, dest = t1)
                *)
       | Deref _ | Array_access _ | Struct_access _ ->
         let label_id = next_label () in
         let assign_mem_exn_label = "assign_mem_exn" ^ func_name, label_id in
         let assign_success_label = "assign_success" ^ func_name, label_id in
         let addr_temp = Temp.create_of_size QUAD in
         let address = trans_mexp ~address_of:true lvalue in
         append_to_dll [ T.Move { dest = addr_temp; src = address } ];
         let expr_result = trans_mexp e in
         let expr_temp = Temp.create_of_size (size_of_exp (Mark.data e)) in
         append_to_dll
           T.
             [ Move { dest = expr_temp; src = expr_result }
             ; If
                 { condition =
                     Binop_cmp
                       (* TEMP WILL BE A QUAD TEMP *)
                       { lhs = Temp addr_temp; op = Eq; rhs = Addr_const Int64.zero }
                 ; lt = assign_mem_exn_label
                 ; lf = assign_success_label
                 }
             ; Label assign_mem_exn_label
             ; raise_mem_exn
             ; Label assign_success_label
             ; Memory_write
                 { base = Temp addr_temp
                 ; src = Temp expr_temp
                 ; disp = Int32.zero
                 ; index = Const (Int Int32.zero)
                 ; scale = 0
                 }
             ]
       | _ -> failwith "Assign had a non-lvalue expression on the lhs")
    | Return e ->
      (* Here we have to check if a function is called that it has the same 
           ident. *)
      (match Mark.data e with
       | Function_call { ident; _ } ->
         if S.(ident <> caller_ident) then tail_rec_position := false
       | _ -> ());
      let res = trans_mexp e in
      current_return_value := res;
      (* Before each return statement, prepend all the ensures. *)
      List.iter ensures_specs ~f:(fun spec -> trans_spec spec);
      append_to_dll [ T.Return res ]
    | Return_void -> append_to_dll [ T.Return_void ]
    (*
          tr(assert(e)) : cp (e, l1, l2); 
            l2 : t = function_call abort
            l1: 
        *)
    | Assert e ->
      (* Since functions with assert must call abort(), 
             it can never be tail recursive. *)
      tail_rec_position := false;
      let label_id = next_label () in
      let fail_label = "assert_fail" ^ func_name, label_id in
      let pass_label = "assert_pass" ^ func_name, label_id in
      let t = Temp.create_of_size Temp.BYTE in
      (* Boolean expression is always a byte *)
      trans_boolean_exp (Mark.data e) pass_label fail_label;
      append_to_dll
        [ T.Label fail_label
        ; T.Function_call { dest = t; ident = "abort"; args = []; assign_res = false }
        ; T.Goto pass_label (* Add this to preserve basic blocks structure *)
        ; T.Label pass_label
        ]
    | Nop -> append_to_dll [ T.Nop ]
    | Seq (s1, s2) ->
      trans_mstm s1 ~remove_annotations;
      trans_mstm s2 ~remove_annotations
    (* Translation of while using cp:
         tr(while(b, s)) = goto cmp;
                          l1: tr(s);
                          cmp: cp(b, l1, l2);
                          l2:  

          Conversion to do-while-loop form:
          tr(while(b, s)) = 
            cp(b, l1, l2);
            l1: tr(s);
            goto l1 end
            l1_end:
            cp(b, l1, l2);
            l2: 
        *)
    | While (condition, body) ->
      check_tail_rec_mexp condition;
      let label_id = next_label () in
      let while_true_label = "while_true" ^ func_name, label_id in
      let while_true_finish_label = "while_true_finish" ^ func_name, label_id in
      let while_end_label = "while_end" ^ func_name, label_id in
      trans_boolean_exp (Mark.data condition) while_true_label while_end_label;
      (* The added labels are necessary to prevent edges to self in the cfg, so that the SSA can work *)
      append_to_dll
        [ T.Label while_true_label
        ; T.Nop
        ; T.Goto while_true_finish_label
        ; T.Nop
        ; T.Label while_true_finish_label
        ; T.Nop
        ];
      trans_mstm body ~remove_annotations;
      trans_boolean_exp (Mark.data condition) while_true_label while_end_label;
      append_to_dll [ T.Nop; T.Label while_end_label ]
    | If (condition, if_true, if_false) ->
      (match Mark.data if_false with
       | Nop ->
         check_tail_rec_mexp condition;
         let label_id = next_label () in
         let if_true_label = "if_true" ^ func_name, label_id in
         let if_end_label = "if_end" ^ func_name, label_id in
         trans_boolean_exp (Mark.data condition) if_true_label if_end_label;
         append_to_dll [ T.Label if_true_label ];
         trans_mstm if_true ~remove_annotations;
         append_to_dll [ T.Goto if_end_label; T.Label if_end_label ]
       | _ ->
         check_tail_rec_mexp condition;
         let label_id = next_label () in
         let if_true_label = "if_true" ^ func_name, label_id in
         let if_false_label = "if_false" ^ func_name, label_id in
         let if_end_label = "if_end" ^ func_name, label_id in
         trans_boolean_exp (Mark.data condition) if_true_label if_false_label;
         append_to_dll [ T.Label if_true_label ];
         trans_mstm if_true ~remove_annotations;
         append_to_dll [ T.Goto if_end_label; T.Label if_false_label ];
         trans_mstm if_false ~remove_annotations;
         append_to_dll [ T.Goto if_end_label; T.Label if_end_label ])
    | Expr_stm e ->
      (* 
            Expression statement is not appended, but the expressions are appended.
            Throw away the result and keep only the side effects *)
      check_tail_rec_mexp e;
      ignore (trans_mexp ~call_as_stm:true e : T.exp)
    | For _ -> failwith "There should not be any for loops in elaborated AST"
    | Block_intermediate _
    | Declare_intermediate _
    | Asnop_pure_mem_intermediate _
    | Asnop_impure_mem_intermediate _ ->
      failwith "Intermediates should be elaborated away"
    (* Safe Asnop with memory lvalue:
        tr(asnop(d,@,e)):
        t1 <- &(d);
        ins(e);
        t2 <- res(e); // DOUBLE
        if t1 = 0 then mem_exn else assign
        mem_exn:
        exception(mem)
        assign:
        t3 <-  Mem_read(t1) // DOUBLE
        t4 <- t3 @ t2
        Mem_store(t1) <- t4
      *)
    | Asnop_pure_mem { lhs; rhs; op } ->
      let label_id = next_label () in
      let asnop_mem_exn_label = "asnop_mem_exn" ^ func_name, label_id in
      let asnop_success_label = "asnop_success" ^ func_name, label_id in
      let t1 = Temp.create_of_size QUAD in
      let addr_d = trans_mexp ~address_of:true lhs in
      append_to_dll [ T.Move { dest = t1; src = addr_d } ];
      let res_e = trans_mexp rhs in
      let t2 = Temp.create_of_size DOUBLE in
      append_to_dll [ T.Move { dest = t2; src = res_e } ];
      let t3 = Temp.create_of_size DOUBLE in
      let t4 = Temp.create_of_size DOUBLE in
      append_to_dll
        T.
          [ If
              { condition =
                  Binop_cmp { lhs = Temp t1; op = Eq; rhs = Addr_const Int64.zero }
              ; lt = asnop_mem_exn_label
              ; lf = asnop_success_label
              }
          ; Label asnop_mem_exn_label
          ; raise_mem_exn
          ; Label asnop_success_label
          ; Memory_read
              { base = Temp t1
              ; disp = Int32.zero
              ; index = Const (Int Int32.zero)
              ; scale = 0
              ; dest = Temp t3
              }
          ; Move
              { dest = t4
              ; src =
                  Binop_pure { lhs = Temp t3; rhs = Temp t2; op = trans_binop_pure op }
              }
          ; Memory_write
              { src = Temp t4
              ; disp = Int32.zero
              ; base = Temp t1
              ; index = Const (Int Int32.zero)
              ; scale = 0
              }
          ]
    | Asnop_impure_mem { lhs; rhs; op } ->
      let label_id = next_label () in
      let asnop_mem_exn_label = "asnop_mem_exn" ^ func_name, label_id in
      let asnop_success_label = "asnop_success" ^ func_name, label_id in
      let t1 = Temp.create_of_size QUAD in
      let addr_d = trans_mexp ~address_of:true lhs in
      append_to_dll [ T.Move { dest = t1; src = addr_d } ];
      let res_e = trans_mexp rhs in
      let t2 = Temp.create_of_size DOUBLE in
      append_to_dll [ T.Move { dest = t2; src = res_e } ];
      let t3 = Temp.create_of_size DOUBLE in
      let t4 = Temp.create_of_size DOUBLE in
      append_to_dll
        T.
          [ If
              { condition =
                  Binop_cmp { lhs = Temp t1; op = Eq; rhs = Addr_const Int64.zero }
              ; lt = asnop_mem_exn_label
              ; lf = asnop_success_label
              }
          ; Label asnop_mem_exn_label
          ; raise_mem_exn
          ; Label asnop_success_label
          ; Memory_read
              { base = Temp t1
              ; disp = Int32.zero
              ; index = Const (Int Int32.zero)
              ; scale = 0
              ; dest = Temp t3
              }
          ; Binop_impure
              { dest = t4; lhs = Temp t3; rhs = Temp t2; op = trans_binop_impure op }
          ; Memory_write
              { src = Temp t4
              ; disp = Int32.zero
              ; base = Temp t1
              ; index = Const (Int Int32.zero)
              ; scale = 0
              }
          ]
    | Postop _ -> failwith "Postops should have been elaborated out before translation"
    | Annotated_stm_intermediate _ ->
      failwith "Intermediate annotated_stm should be elaborated out"
    | Annotated_stm (anno, mstm) ->
      if not remove_annotations then List.iter anno ~f:(fun spec -> trans_spec spec);
      trans_mstm mstm ~remove_annotations
  (* The translation of spec is identical to that of assert statements; the 
     only restriction really is where they can appear. We just change the labels 
     to make it easier to distinguish them. *)
  and trans_spec spec =
    let fail_label_stem, pass_label_stem =
      match spec with
      | A.Requires _ -> "requires_fail", "requires_pass"
      | Ensures _ -> "ensures_fail", "ensures_pass"
      | Loop_invariant _ -> "loop_invariant_fail", "loop_invariant_pass"
      | Assert_spec _ -> "assert_spec_fail", "assert_spec_pass"
    in
    match spec with
    | A.Requires e | Ensures e | Loop_invariant e | Assert_spec e ->
      (* Since functions with assert must call abort(), 
             it can never be tail recursive. *)
      tail_rec_position := false;
      let label_id = next_label () in
      let fail_label = fail_label_stem ^ func_name, label_id in
      let pass_label = pass_label_stem ^ func_name, label_id in
      let t = Temp.create_of_size Temp.BYTE in
      (* Boolean expression is always a byte *)
      trans_boolean_exp (Mark.data e) pass_label fail_label;
      append_to_dll
        [ T.Label fail_label
        ; T.Function_call { dest = t; ident = "abort"; args = []; assign_res = false }
        ; T.Goto pass_label (* Add this to preserve basic blocks structure *)
        ; T.Label pass_label
        ]
  and trans_mstm mstm ~(remove_annotations : bool) : unit =
    trans_stm (Mark.data mstm) ~remove_annotations
  in
  (* Before translation of the function body, 
     prepend all requires specs to the DLL *)
  List.iter requires_specs ~f:(fun spec -> trans_spec spec);
  trans_mstm elaborated_ast ~remove_annotations;
  let body = Doubly_linked.to_list result_dll in
  let tail_rec = !tail_rec_position && !recursive in
  Hashtbl.clear env;
  let num_temps = Temp.get_counter () - init_num_temps in
  (* Empty the env for the next function decl translation *)
  let signature =
    T.
      { ident = func_name
      ; args = function_args
      ; tail_rec
      ; num_temps
      ; recursive = !recursive
      }
  in
  match body with
  (* If the body is empty (void function) then add a return statement *)
  | [] -> signature, [ T.Return_void ]
  | _ -> signature, body
;;

(* Takes [elaborated_ast] and returns an IR as a T.func.
    Requires: [elaborated_ast] has been fully elaborated:
      1. There are no more asops e.g. +=, -= 
      2. For expressions have been elaborated into while expressions
      3. int x = 0 (declare with init expressions) have been elaborated into 
        a sequence of declare + assign expressions
      4. There are no more Declare_intermediate statements 
        of the form decl * tau * mstm list; these have been elaborated into 
        sequences
      5. Expr_stms are included in case they cause a runtime exception
      6. There are no Blocks; these have been elaborated into chains of sequences
        Block \[a; b; c] -> seq(a, seq(b, seq(c, nop)))
    Requires: [elaborated_ast] has passed typechecking
    Requires: Temp.counter is already in scope when this function is called, so 
    that changes to temp numbers are persistent across compiler phases
 *)
let translate_ast
  (ast : A.mprogram_block)
  defined_functions
  env
  struct_to_size
  label_counter
  tau_to_tag
  ~(remove_annotations : bool)
  : T.func
  =
  let size_of_tau : A.tau -> Int64.t = function
    | Char | Bool -> Int64.of_int_exn 1
    | Int -> Int64.of_int_exn 4
    | Pointer _ | Array _ | String -> Int64.of_int_exn 8
    | Alias _ -> failwith "All aliases should have been elaborated out"
    | Void -> failwith "called size_of_tau on a void tau"
    | Any -> failwith "Any shouldn't exist in code"
    | Dummy -> failwith "Dummy should be elaborated out"
    | Struct s -> fst (SymbolTable.find_exn struct_to_size s)
  in
  let init_num_temps = Temp.get_counter () in
  let raw_ast = Mark.data ast in
  match raw_ast with
  | Function_Decl _
  | Typedef _
  | Function_Def_Intermediate _
  | Struct_Def_Intermediate _
  | Function_Def_Anno_Intermediate _ ->
    failwith "Intermediate defs, Typedefs and Function decls should be removed."
  | Struct_Def _ | Struct_Decl _ ->
    failwith "Struct definitions and declarations should be removed before translation"
  | Function_Def { fn_block; params; ident; _ } ->
    translate_function_def
      fn_block
      params
      ident
      init_num_temps
      defined_functions
      env
      label_counter
      size_of_tau
      tau_to_tag
      []
      ~remove_annotations
  (* Idea: translate function body. Prepend any requires statements, and 
     produce a list of ensures statements. Insert the list of ensures statements
     after any return you find. *)
  | Function_Def_Anno { fn_block; params; ident; anno; _ } ->
    if remove_annotations
    then
      translate_function_def
        fn_block
        params
        ident
        init_num_temps
        defined_functions
        env
        label_counter
        size_of_tau
        tau_to_tag
        []
        ~remove_annotations
    else
      translate_function_def
        fn_block
        params
        ident
        init_num_temps
        defined_functions
        env
        label_counter
        size_of_tau
        tau_to_tag
        anno
        ~remove_annotations
;;

let get_defined_functions program_list =
  let defined_names = Hashtbl.create ~growth_allowed:true ~size:10 (module Symbol) in
  List.iter program_list ~f:(fun e ->
    match Mark.data e with
    | Ast.Function_Def { ident; _ } | Function_Def_Anno { ident; _ } ->
      Hashtbl.add_exn defined_names ~key:ident ~data:()
    | _ -> ());
  defined_names
;;

let keep_only_function_defs program_list =
  List.filter program_list ~f:(fun e ->
    match Mark.data e with
    | Ast.Function_Def _ | Ast.Function_Def_Anno _ -> true
    | _ -> false)
;;

let translate (ast_list : Ast.program) struct_to_size ~(remove_annotations : bool)
  : T.program
  =
  let defined_functions = get_defined_functions ast_list in
  (* Keep only function definitions in subsequent program *)
  let ast_list_only_defs = keep_only_function_defs ast_list in
  (* Maintain a global Hashtbl that maps each tau to its 64-bit tag. *)
  let tau_to_tag = Hashtbl.create ~growth_allowed:true ~size:10 (module A) in
  (*
    Maintain a global Hashtbl env which maps variables (Symbol.t) to Temps.
    We can do this because:
    - Type checking ensures that variables are used only after they are declared
    - According to l2 semantics, variables CANNOT shadow other variables. 
    - So if we traverse our tree using DFS, "replacing" variables in the global 
      Hashtbl is ok, since if we set a variable with the same name, 
      it means the previous variable is out of scope.  
  *)
  let env = Hashtbl.create ~growth_allowed:true ~size:10 (module Symbol) in
  (* Label counter should be shared across functions to accomodate function inlining*)
  let label_counter = ref 0 in
  List.map ast_list_only_defs ~f:(fun ast ->
    translate_ast
      ast
      defined_functions
      env
      struct_to_size
      label_counter
      tau_to_tag
      ~remove_annotations)
;;
