(* 
  Implement Strength Reduction 
  Source:
    Hacker’s Delight 2nd Edition Chapter 10
*)

open Core
module ThreeAS = Threeaddrassem

let pow_two_table =
  let int32_list =
    List.map
      [ 1, 0
      ; 2, 1
      ; 4, 2
      ; 8, 3
      ; 16, 4
      ; 32, 5
      ; 64, 6
      ; 128, 7
      ; 256, 8
      ; 512, 9
      ; 1024, 10
      ; 2048, 11
      ; 4096, 12
      ; 8192, 13
      ; 16384, 14
      ; 32768, 15
      ; 65536, 16
      ; 131072, 17
      ; 262144, 18
      ; 524288, 19
      ; 1048576, 20
      ; 2097152, 21
      ; 4194304, 22
      ; 8388608, 23
      ; 16777216, 24
      ; 33554432, 25
      ; 67108864, 26
      ; 134217728, 27
      ; 268435456, 28
      ; 536870912, 29
      ; 1073741824, 30
      ; 2147483648, 31
      ]
      ~f:(fun (a, b) -> Int32.(of_int_trunc a, of_int_trunc b))
  in
  match Hashtbl.of_alist ~growth_allowed:false ~size:32 (module Int32) int32_list with
  | `Duplicate_key _ -> failwith "lol"
  | `Ok x -> x
;;

(* Get the boolean bit array of an int32 *)
let get_bit_array i =
  let rec get_curr_bit acc curr_val ind =
    if ind = 0
    then acc
    else (
      let curr_bit = Int32.(curr_val land one = one) in
      let curr_val' = Int32.(curr_val lsr 1) in
      get_curr_bit (curr_bit :: acc) curr_val' (ind - 1))
  in
  get_curr_bit [] i 32
;;

let find_consecutive_runs bit_array =
  let rec find_helper curr_arr ind_pairs prev_one ind acc =
    match curr_arr with
    | [] -> if prev_one then ind_pairs :: acc else acc
    | h :: t when prev_one && h ->
      find_helper t (fst ind_pairs, Int32.of_int_trunc ind) h (ind - 1) acc
    | h :: t when prev_one ->
      find_helper t Int32.(zero, zero) h (ind - 1) (ind_pairs :: acc)
    | h :: t when h ->
      find_helper t Int32.(of_int_trunc ind, of_int_trunc ind) h (ind - 1) acc
    | h :: t -> find_helper t Int32.(zero, zero) h (ind - 1) acc
  in
  find_helper bit_array Int32.(zero, zero) false 31 []
;;

(* Now, use the consecutive runs to convert into shifts
  https://www.youtube.com/watch?v=7WrSaM7pcWY
  Need to think about how to generalise and find out
  whether an imul can be changed into 1 or 2 instructions
  3 instructions becomes quite questionable

  1. If there is only 1 conseuctive run of 1s, can be 2 shifts and a sub
  2. If the multiple is of 2,4,8,3,5,9, then it can be done in 1 LEA 
  (but index MUST be a register, so register allocation must prioritise lea?)
  3. If the multiple is any combination of 2,4,8,3,5,9 then it can be done in 2 LEA
  4. If the multiple is of 2^i * (3,5,9) then it can be done in 1 LEA and a shift
  5. If the multiple is any power of two, then it can be done in 1 shift
  6. Any other instruction might not reap significant gains, 
    since 3 instructions approaches the speed of a single imul

  HOWEVER, since LEAs require registers, we focus on doing 1 and 5 only
  Other optimisations might be introduced after register allocation
*)

(* If the multiplier is a power of two, then use the table and make it a leftshift *)
let mult_pow_two (dest : ThreeAS.operand) (mul_target : ThreeAS.operand) (mult : Int32.t) =
  ThreeAS.[ Binop { op = Sal; dest; lhs = mul_target; rhs = Imm mult } ]
;;

(* If the multiplier is a power of two, then use the table and make it a leftshift,
  15513 textbook problem 2.40   
*)
let one_consecutive_run
  (dest : ThreeAS.operand)
  (mul_target : ThreeAS.operand)
  (ind_one : Int32.t)
  (ind_two : Int32.t)
  =
  if Int32.(ind_one <> of_int_trunc 31)
  then (
    let first_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
    let second_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
    ThreeAS.
      [ Binop
          { op = Sal
          ; dest = first_temp
          ; lhs = mul_target
          ; rhs = Imm Int32.(ind_one + one)
          }
      ; Binop { op = Sal; dest = second_temp; lhs = mul_target; rhs = Imm ind_two }
      ; Binop { op = Sub; dest; lhs = first_temp; rhs = second_temp }
      ])
  else (
    let second_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
    ThreeAS.
      [ Binop { op = Sal; dest = second_temp; lhs = mul_target; rhs = Imm ind_two }
      ; Binop { op = Sub; dest; lhs = Imm Int32.zero; rhs = second_temp }
      ])
;;

let verify_consecutive_run multiplier =
  let bit_array = get_bit_array multiplier in
  let consecutive_runs = find_consecutive_runs bit_array in
  match consecutive_runs with
  | h :: [] -> Some h
  | _ -> None
;;

let mult_simple
  (dest : ThreeAS.operand)
  (mul_target : ThreeAS.operand)
  (multiplier : Int32.t)
  =
  match Hashtbl.find pow_two_table multiplier with
  | Some x -> mult_pow_two dest mul_target x
  | None ->
    (match verify_consecutive_run multiplier with
     | Some (x, y) -> one_consecutive_run dest mul_target x y
     | None ->
       ThreeAS.[ Binop { op = Mul; dest; lhs = mul_target; rhs = Imm multiplier } ])
;;

let unsigned_compare (a : Int32.t) (b : Int32.t) =
  if Int32.is_positive a && Int32.is_positive b
  then Int32.compare a b
  else if Int32.is_negative a && Int32.is_negative b
  then Int32.compare a b
  else if Int32.is_negative a
  then -1
  else 1
;;

let rec while_loop ~p ~q1 ~r1 ~anc ~q2 ~r2 ~ad =
  let p' = Int32.(p + of_int_trunc 1) in
  let q1' = Int32.(of_int_trunc 2 * q1) in
  let r1' = Int32.(of_int_trunc 2 * r1) in
  let r1_geq_anc = unsigned_compare r1' anc >= 0 in
  let q1'' = if r1_geq_anc then Int32.(q1' + of_int_trunc 1) else q1' in
  let r1'' = if r1_geq_anc then Int32.(r1' - anc) else r1' in
  let q2' = Int32.(of_int_trunc 2 * q2) in
  let r2' = Int32.(of_int_trunc 2 * r2) in
  let r2_geq_ad = unsigned_compare r2 ad >= 0 in
  let q2'' = if r2_geq_ad then Int32.(q2' + of_int_trunc 1) else q2' in
  let r2'' = if r2_geq_ad then Int32.(r2' - ad) else r2' in
  let delta = Int32.(ad - r2) in
  let q1_less_delta = Int32.(q1 < delta) in
  let q1_delta_r1_0 = Int32.(q1 = delta && r1 = Int32.zero) in
  if q1_less_delta || q1_delta_r1_0
  then while_loop ~p:p' ~q1:q1'' ~r1:r1'' ~anc ~q2:q2'' ~r2:r2'' ~ad
  else q2'', p
;;

(* 
Implement the magic number algorithm here
Return Magic Number + Shift amount   
*)
let find_magic_number (d : Int32.t) : Int32.t * Int32.t =
  let two31 = Int32.shift_left (Int32.of_int_trunc 2) 31 in
  let ad = Int32.abs d in
  let t = Int32.(two31 + Int32.shift_right_logical d 31) in
  let anc = Int32.(t - Int32.one - (t % ad)) in
  let p = Int32.of_int_trunc 31 in
  let q1 = Int32.(two31 / anc) in
  let r1 = Int32.(two31 - (q1 * anc)) in
  let q2 = Int32.(two31 / ad) in
  let r2 = Int32.(two31 - (q2 * ad)) in
  let q2', p' = while_loop ~p ~q1 ~r1 ~anc ~q2 ~r2 ~ad in
  let magic = Int32.(q2' + Int32.one) in
  let magic' = if Int32.is_negative d then Int32.neg magic else magic in
  let s = Int32.(p' - of_int_trunc 32) in
  magic', s
;;

(* After finding magic number, need to do some other stuff *)
(* 
  Compiler needs to generate 
  1. li + mulhs
  2. add/sub (check d and M)
  3. shrsi (check s)
  4. shri and add
  Look at the other stuff
  page 210
*)
let div_general
  (dest : ThreeAS.operand)
  (dividend : ThreeAS.operand)
  (divisor : Int32.t)
  (is_div : bool)
  =
  let magic_number, shift = find_magic_number divisor in
  let magic_number_temp = ThreeAS.Temp (Temp.create_of_size Temp.QUAD) in
  let dividend_quad_temp = ThreeAS.Temp (Temp.create_of_size Temp.QUAD) in
  let mulhs_prod = ThreeAS.Temp (Temp.create_of_size Temp.QUAD) in
  let mulhs_dest_quad = ThreeAS.Temp (Temp.create_of_size Temp.QUAD) in
  let mulhs_dest = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
  let add_sub_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
  let shrsi_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
  let shri_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
  let quotient_temp =
    if is_div then dest else ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE)
  in
  let muli_temp = ThreeAS.Temp (Temp.create_of_size Temp.DOUBLE) in
  let load_magic_number =
    (* magic_number <- `magic` *)
    Some
      ThreeAS.
        [ Mov { dest = magic_number_temp; src = Addr_imm (Int64.of_int32 magic_number) } ]
  in
  (* TODO: fix this and return the upper 32 bits of the multiplication 
    Either promote divident to quad and then store in a quad but leftshift down, or 
    Use 1address mul and introduce RAX/RDX registers in 3AS   

    Movsx into int64, then use it in imul, then downshift
  *)
  let load_quad_dividend =
    (* dividend_quad <- dividend *)
    Some ThreeAS.[ Movsx { dest = dividend_quad_temp; src = dividend } ]
  in
  let floor_mult_overflow =
    (* mulhs_prod_quad <- magic_number * dividend_quad *)
    Some
      ThreeAS.
        [ Binop
            { op = Mul
            ; dest = mulhs_prod
            ; lhs = magic_number_temp
            ; rhs = dividend_quad_temp
            }
        ]
  in
  let downshift_mult =
    (* Downshift into a destination *)
    Some
      ThreeAS.
        [ Binop
            { op = Shr
            ; dest = mulhs_dest_quad
            ; lhs = mulhs_prod
            ; rhs = Addr_imm (Int64.of_int 32)
            }
        ]
  in
  let upper_32_bits =
    (* move into the correct location *)
    Some ThreeAS.[ Mov_trunc { dest = mulhs_dest; src = mulhs_dest_quad } ]
  in
  let add_sub_option, use_add_sub =
    match divisor, magic_number with
    | _, _ when Int32.is_negative divisor && Int32.is_positive magic_number ->
      ( Some
          ThreeAS.
            [ Binop { op = Add; dest = add_sub_temp; lhs = dividend; rhs = mulhs_dest } ]
      , true (* failwith "d < 0 && M > 0 is a sub" *) )
    | _, _ when Int32.is_positive divisor && Int32.is_negative magic_number ->
      ( Some
          ThreeAS.
            [ Binop { op = Sub; dest = add_sub_temp; lhs = dividend; rhs = mulhs_dest } ]
      , true (* failwith "d > 0 && M < 0 is a sub" *) )
    | _ -> None, false
  in
  let shrsi_option, use_shrsi =
    match shift with
    | _ when Int32.(Int32.zero <> shift && use_add_sub) ->
      ( Some
          ThreeAS.
            [ Binop { op = Sar; dest = shrsi_temp; lhs = add_sub_temp; rhs = Imm shift } ]
      , true )
    | _ when Int32.(Int32.zero <> shift && not use_add_sub) ->
      ( Some
          ThreeAS.
            [ Binop { op = Sar; dest = shrsi_temp; lhs = mulhs_dest; rhs = Imm shift } ]
      , true )
    | _ -> None, false
  in
  let shri =
    Some
      ThreeAS.
        [ Binop
            { op = Shr
            ; dest = shri_temp
            ; lhs = dividend
            ; rhs = Imm (Int32.of_int_trunc 31)
            }
        ]
  in
  let add_final =
    match use_shrsi, use_add_sub with
    | true, _ ->
      Some
        ThreeAS.
          [ Binop { op = Add; dest = quotient_temp; lhs = shrsi_temp; rhs = shri_temp } ]
    | _, true ->
      Some
        ThreeAS.
          [ Binop { op = Add; dest = quotient_temp; lhs = add_sub_temp; rhs = shri_temp }
          ]
    | _, _ ->
      Some
        ThreeAS.
          [ Binop { op = Add; dest = quotient_temp; lhs = mulhs_dest; rhs = shri_temp } ]
  in
  let remainder_option =
    if is_div
    then None
    else
      Some
        ThreeAS.
          [ Binop { op = Mul; dest = muli_temp; lhs = quotient_temp; rhs = Imm divisor }
          ; Binop { op = Sub; dest; lhs = dividend; rhs = muli_temp }
          ]
  in
  (* Now, need to see whether to keep going or not by checking if it is a div or quotient *)
  let res =
    [ load_magic_number
    ; load_quad_dividend
    ; floor_mult_overflow
    ; downshift_mult
    ; upper_32_bits
    ; add_sub_option
    ; shrsi_option
    ; shri
    ; add_final
    ; remainder_option
    ]
  in
  let res' = List.filter_map res ~f:(fun x -> x) in
  List.concat res'
;;

let body_pass (body : ThreeAS.body) : ThreeAS.body =
  let passed_body =
    List.map body ~f:(fun line ->
      match line with
      | ThreeAS.Binop { op; dest; lhs; rhs } ->
        (match op, rhs with
         | ThreeAS.Div, ThreeAS.Imm rhs_imm when Int32.(rhs_imm <> Int32.zero) ->
           let res = div_general dest lhs rhs_imm true in
           Printf.printf "div: \n";
           List.iter res ~f:(fun x -> Printf.printf "%s\n" (ThreeAS.format_instr x));
           Printf.printf "end div\n"
         | ThreeAS.Mod, ThreeAS.Imm rhs_imm when Int32.(rhs_imm <> Int32.zero) ->
           let res = div_general dest lhs rhs_imm false in
           Printf.printf "mod: \n";
           List.iter res ~f:(fun x -> Printf.printf "%s\n" (ThreeAS.format_instr x));
           Printf.printf "end mod\n";
           res
         | ThreeAS.Mul, ThreeAS.Imm rhs_imm -> mult_simple dest lhs rhs_imm
         | _ -> [ line ])
      | _ -> [ line ])
  in
  List.concat passed_body
;;

let strength_pass (prog : ThreeAS.program) : ThreeAS.program =
  List.map prog ~f:(fun (signature, body) -> signature, body_pass body)
;;
