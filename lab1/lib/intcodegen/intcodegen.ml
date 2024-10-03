(* L1 Compiler
 * Assembly Code Generator for Three Address assembly
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use a linear, not quadratic, algorithm.
 *
 * Implements a "convenient munch" algorithm
 *)

open Core
module T = Tree
module AS = Assem

let munch_op = function
  | T.Add -> AS.Add
  | T.Sub -> AS.Sub
  | T.Mul -> AS.Mul
  | T.Div -> AS.Div
  | T.Mod -> AS.Mod
;;

(* munch_exp dest exp
 *
 * Generates instructions for dest <-- exp.
 *)
let munch_exp : AS.operand -> T.exp -> AS.instr list =
  (* munch_exp_acc dest exp rev_acc
   *
   * Suppose we have the statement:
   *   dest <-- exp
   *
   * If the codegened statements for this are:
   *   s1; s2; s3; s4;
   *
   * Then this function returns the result:
   *   s4 :: s3 :: s2 :: s1 :: rev_acc
   *
   * I.e., rev_acc is an accumulator argument where the codegen'ed
   * statements are built in reverse. This allows us to create the
   * statements in linear time rather than quadratic time (for highly
   * nested expressions).
   *)
  let rec munch_exp_acc (dest : AS.operand) (exp : T.exp) (rev_acc : AS.instr list)
    : AS.instr list
    =
    match exp with
    | T.Const n -> AS.Mov { dest; src = AS.Imm n } :: rev_acc
    | T.Temp t -> AS.Mov { dest; src = AS.Temp t } :: rev_acc
    | T.Binop binop -> munch_binop_acc dest (binop.op, binop.lhs, binop.rhs) rev_acc
  (* munch_binop_acc dest (binop, e1, e2) rev_acc
   *
   * generates instructions to achieve dest <- e1 binop e2
   *
   * Much like munch_exp, this returns the result of appending the
   * instructions in reverse to the accumulator argument, rev_acc.
   *)
  and munch_binop_acc
    (dest : AS.operand)
    ((binop, e1, e2) : T.binop * T.exp * T.exp)
    (rev_acc : AS.instr list)
    : AS.instr list
    =
    let op = munch_op binop in
    let t1 = AS.Temp (Temp.create ()) in
    let t2 = AS.Temp (Temp.create ()) in
    let rev_acc' = rev_acc |> munch_exp_acc t1 e1 |> munch_exp_acc t2 e2 in
    AS.Binop { op; dest; lhs = t1; rhs = t2 } :: rev_acc'
  in
  fun dest exp ->
    (* Since munch_exp_acc returns the reversed accumulator, we must
     * reverse the list before returning. *)
    List.rev (munch_exp_acc dest exp [])
;;

(* munch_stm : T.stm -> AS.instr list *)
(* munch_stm stm generates code to execute stm *)
let munch_stm = function
  | T.Move mv -> munch_exp (AS.Temp mv.dest) mv.src
  | T.Return e ->
    (* return e is implemented as %eax <- e *)
    munch_exp (AS.Reg AS.EAX) e
;;

(* To codegen a series of statements, just concatenate the results of
 * codegen-ing each statement. *)
let int_code_gen = List.concat_map ~f:munch_stm

let%expect_test "Test parsing of simple main into 3 assem" =
  let lexbuf = Lexing.from_string "int main() {int x = 3; int y = -x; return x + 3; }" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = int_code_gen ir in
  (* let assem = Threetotwo.threetotwo assem_three in *)
  let output_instr instr = Printf.printf "\t%s\n" (AS.format instr) in
  output_instr (AS.Directive ".function\tmain()");
  List.iter ~f:output_instr assem_three;
  output_instr (AS.Directive ".ident\t\"15-411 L1 reference compiler\"");
  [%expect
    {|
    .function	main()
    %t1 <-- $3
    %t3 <-- $0
    %t4 <-- %t1
    %t2 <-- %t3 - %t4
    %t5 <-- %t1
    %t6 <-- $3
    %eax <-- %t5 + %t6
    .ident	"15-411 L1 reference compiler"
  |}]
;;

let%expect_test "Test parsing of commutative and associative into 3 assem" =
  Temp.reset ();
  let lexbuf = Lexing.from_string "int main() {return (5 + 3 - 6 * 3); }" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = int_code_gen ir in
  (* let assem = Threetotwo.threetotwo assem_three in *)
  let output_instr instr = Printf.printf "\t%s\n" (AS.format instr) in
  output_instr (AS.Directive ".function\tmain()");
  List.iter ~f:output_instr assem_three;
  output_instr (AS.Directive ".ident\t\"15-411 L1 reference compiler\"");
  [%expect
    {|
    .function	main()
    %t3 <-- $5
    %t4 <-- $3
    %t1 <-- %t3 + %t4
    %t5 <-- $6
    %t6 <-- $3
    %t2 <-- %t5 * %t6
    %eax <-- %t1 - %t2
    .ident	"15-411 L1 reference compiler"
  |}]
;;

let%expect_test "Test parsing of commutative and associative into 3 assem" =
  Temp.reset ();
  let lexbuf = Lexing.from_string "int main() {return 3 * (4 + 2) / 2 - 7; }" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = int_code_gen ir in
  (* let assem = Threetotwo.threetotwo assem_three in *)
  let output_instr instr = Printf.printf "\t%s\n" (AS.format instr) in
  output_instr (AS.Directive ".function\tmain()");
  List.iter ~f:output_instr assem_three;
  output_instr (AS.Directive ".ident\t\"15-411 L1 reference compiler\"");
  [%expect
    {|
    .function	main()
    %t5 <-- $3
    %t7 <-- $4
    %t8 <-- $2
    %t6 <-- %t7 + %t8
    %t3 <-- %t5 * %t6
    %t4 <-- $2
    %t1 <-- %t3 / %t4
    %t2 <-- $7
    %eax <-- %t1 - %t2
    .ident	"15-411 L1 reference compiler"
  |}]
;;

let%expect_test "test" =
  Temp.reset ();
  let lexbuf = Lexing.from_string "int main() {return 1;}" in
  let ast = C0_parser.program C0_lexer.initial lexbuf in
  let ir = Trans.translate ast in
  let assem_three = int_code_gen ir in
  (* let assem = Threetotwo.threetotwo assem_three in *)
  let output_instr instr = Printf.printf "\t%s\n" (AS.format instr) in
  output_instr (AS.Directive ".function\tmain()");
  List.iter ~f:output_instr assem_three;
  output_instr (AS.Directive ".ident\t\"15-411 L1 reference compiler\"");
  [%expect
    {|
      .function	main()
      %eax <-- $1
      .ident	"15-411 L1 reference compiler"
    |}]
;;
