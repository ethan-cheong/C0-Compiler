open Core
module AS = Assem
(* 
Find the pattern
cmp x, y
jump if condition met lt
jmp lf
lt:

to

cmp x, y
jump if condition not met lf
*)

let neg_of_cmp cmp =
  AS.(
    match cmp with
    | L -> Ge
    | Le -> G
    | G -> Le
    | Ge -> L
    | E -> Ne
    | Ne -> E
    | Z -> Ne)
;;

let rec change_helper instrs acc =
  AS.(
    match instrs with
    | [] -> acc
    | Cmp { lhs; rhs } :: Jc lt_record :: Jmp lf_label :: Label lt_label :: t ->
      let jc_label = lt_record.label in
      if String.(jc_label = lt_label)
      then (
        let jc_cmp' = neg_of_cmp lt_record.cmp in
        change_helper
          t
          (Label lt_label
           :: Jc { cmp = jc_cmp'; label = lf_label }
           :: Cmp { lhs; rhs }
           :: acc))
      else
        change_helper
          t
          (Label lt_label :: Jmp lf_label :: Jc lt_record :: Cmp { lhs; rhs } :: acc)
    | h :: t -> change_helper t (h :: acc))
;;

let change_ordering instrs = List.rev (change_helper instrs [])
