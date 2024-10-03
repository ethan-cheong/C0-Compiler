open! Core
module AS = Assem
module NodeSet = Set.Make (Node)

let assign_temps x =
  let x_int = String.sub x ~pos:2 ~len:(String.length x - 2) |> int_of_string in
  AS.Temp (Temp.make x_int)
;;

(*  *)
let assign_regs = function
  | "%eax" -> AS.Reg AS.EAX
  | "%ebx" -> AS.Reg AS.EBX
  | "%ecx" -> AS.Reg AS.ECX
  | "%edx" -> AS.Reg AS.EDX
  | "%rsp" -> AS.Reg AS.RSP
  | "%ebp" -> AS.Reg AS.EBP
  | "%esi" -> AS.Reg AS.ESI
  | "%edi" -> AS.Reg AS.EDI
  | "%r8d" -> AS.Reg AS.R8D
  | "%r9d" -> AS.Reg AS.R9D
  | "%r10d" -> AS.Reg AS.R10D
  | "%r11d" -> AS.Reg AS.R11D
  | "%r12d" -> AS.Reg AS.R12D
  | "%r13d" -> AS.Reg AS.R13D
  | "%r14d" -> AS.Reg AS.R14D
  | "%r15d" -> AS.Reg AS.R15D
  | _ -> failwith "not a register"
;;

let assign_reg_or_temp str =
  match String.sub str ~pos:0 ~len:2 with
  | "%r" | "%e" -> assign_regs str
  | "%t" -> assign_temps str
  | _ -> failwith "neither reg nor temp"
;;

let oplist_of_reglist (lst : string list) : AS.operand list =
  let rec helper lst acc =
    match lst with
    | [] -> acc
    | h :: t -> helper t (assign_reg_or_temp h :: acc)
  in
  helper lst []
;;

let parse_program_line
  ({ uses; defines; live_out; move; line_number } : Lab1_checkpoint.line)
  : Liveness.line
  =
  { uses = oplist_of_reglist uses
  ; defines = oplist_of_reglist defines
  ; live_out = oplist_of_reglist live_out
  ; move
  ; line_number = Int32.of_int_trunc line_number
  }
;;

let checkpoint_to_liveness lst =
  let rec helper lst acc =
    match lst with
    | [] -> acc
    | h :: t -> helper t (parse_program_line h :: acc)
  in
  helper (List.rev lst) []
;;
(* 
let%expect_test "test for parsing return01" =
  Temp.reset ();
  let input_json =
    Yojson.Basic.from_file "/autograder/compiler/tests/l1-basic-checkpoint/return01.l1.in"
  in
  let input = Lab1_checkpoint.program_of_json input_json in
  let line_input = liveness_of_program input in
  let intf_graph = Buildintfgraph.build_interference_graph line_input in
  let graph_list = Buildintfgraph.table_to_list intf_graph in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  List.iter ~f:output_graph_line graph_list;
  [%expect
    {|
      "%t24": ["%t27"]
      "%t27": ["%t24"]
      "%t21": []
      "%t18": []
      "%eax": []
    |}]
;;

let%expect_test "test for parsing exception" =
  Temp.reset ();
  let input_json =
    Yojson.Basic.from_file
      "/autograder/compiler/tests/l1-basic-checkpoint/exception01.l1.in"
  in
  let input = Lab1_checkpoint.program_of_json input_json in
  let line_input = liveness_of_program input in
  let intf_graph = Buildintfgraph.build_interference_graph line_input in
  let graph_list = Buildintfgraph.table_to_list intf_graph in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  List.iter ~f:output_graph_line graph_list;
  [%expect {|
      "%t6": []
      "%edx": []
      "%eax": []
    |}]
;;

let%expect_test "test for parsing exception" =
  Temp.reset ();
  let input_json =
    Yojson.Basic.from_file "/autograder/compiler/tests/l1-basic-checkpoint/return03.l1.in"
  in
  let input = Lab1_checkpoint.program_of_json input_json in
  let line_input = liveness_of_program input in
  let intf_graph = Buildintfgraph.build_interference_graph line_input in
  let graph_list = Buildintfgraph.table_to_list intf_graph in
  let output_graph_line instr = Printf.printf "\t%s\n" instr in
  List.iter ~f:output_graph_line graph_list;
  [%expect
    {|
    "%t15": ["%t18"]
    "%t21": []
    "%t18": ["%t15"]
    "%eax": []
    |}]
;; *)
