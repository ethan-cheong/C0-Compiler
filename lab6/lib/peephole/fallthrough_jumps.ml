open Core
module AS = Assem

let is_fallthrough h1 h2 =
  AS.(
    match h1, h2 with
    | Jmp x, Label y when String.(x = y) -> true
    | _, _ -> false)
;;

let rec remove_helper curr_instrs acc =
  match curr_instrs with
  | [] -> acc
  | [ a ] -> a :: acc
  | h1 :: h2 :: t ->
    if is_fallthrough h1 h2
    then remove_helper t (h2 :: acc)
    else remove_helper (h2 :: t) (h1 :: acc)
;;

let fallthrough (instrs : AS.instr list) = List.rev (remove_helper instrs [])
