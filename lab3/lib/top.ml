(* L1 Compiler
 * Top Level Environment
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use Cmdliner instead of Getopt for command-line parsing.
 * Modified: Henry Nelson <hcnelson99@gmail.com>
 *   - Switch from ocamlbuild to dune 2.7
 *   - Update to Core v0.14
 *)

open Core
(* 
(* Constants for optimisation *)
(* Skip maximum cardinality search if the interference graph has more than
   [_skip_mcs] nodes *)
let _skip_mcs = 10000

(* Skip entire regalloc phase (including liveness analysis) if more than 
   [_skip_regalloc] temps are assigned and there's only the main function.
   As of lab3, this is induced by simeonpoisson-randomized-large.l1
   We might have to use some other indicator for l1/l2 test cases in l4.
   *)
let _skip_regalloc_l1_l2 = 0

(* Skip entire regalloc phase (including liveness analysis) if more than 
   [_skip_regalloc] temps are assigned and there are multiple functions.
   As of lab3, this is induced by voldemort-charity-burbage.l3
   *)
let _skip_regalloc_l3 = 0

(* Skip regalloc for a function (including liveness analysis) if more than 
   [_skip_regalloc_per_function] temps are assigned in that particular function
   body. As of lab3, this is induced by stan-shunpike-isles.l3
   *)
let _skip_regalloc_per_function = 0 *)

module Opt_level = struct
  type t = Opt_none

  let show = function
    | Opt_none -> "O0"
  ;;

  let parse = function
    | "0" -> Result.Ok Opt_none
    | "1" -> Result.Error (`Msg "Error: -O1 unimplemented (lab 2)")
    | "2" -> Result.Error (`Msg "Error: -O2 unimplemented (lab 5)")
    | arg -> Result.Error (`Msg ("Error: Unknown --opt arg: " ^ arg))
  ;;

  let conv =
    let print ppf opt = Format.fprintf ppf "%s" (show opt) in
    Cmdliner.Arg.conv (parse, print)
  ;;
end

module Emit = struct
  type t =
    | X86_64
    | Abstract_assem

  let show = function
    | X86_64 -> "x86-64"
    | Abstract_assem -> "abs"
  ;;

  let parse = function
    | "abs" -> Result.Ok Abstract_assem
    | "x86-64" -> Result.Ok X86_64
    | arg -> Result.Error (`Msg ("Unknown emit arg: " ^ arg))
  ;;

  let conv =
    let print ppf emit = Format.fprintf ppf "%s" (show emit) in
    Cmdliner.Arg.conv (parse, print)
  ;;
end

module IncludeHeader = struct
  let show str = sprintf "%s" str

  let parse = function
    | s -> Result.Ok s
  ;;

  let conv =
    let print ppf emit = Format.fprintf ppf "%s" (show emit) in
    Cmdliner.Arg.conv (parse, print)
  ;;
end

type cmd_line_args =
  { verbose : bool
  ; dump_all : bool
  ; dump_parsing : bool
  ; dump_ast : bool
  ; dump_ir : bool
  ; dump_abstr : bool
  ; dump_assem : bool
  ; typecheck_only : bool
  ; regalloc_only : bool
  ; no_regalloc : bool
  ; emit : Emit.t
  ; opt_level : Opt_level.t
  ; filename : string
  ; include_header : string
  ; dump_only_times : bool
  }

(* A term (using the vocabulary of the Cmdliner library) that can be used to
 * parse command-line arguments. *)
let cmd_line_term : cmd_line_args Cmdliner.Term.t =
  let open Cmdliner in
  (* See https://github.com/janestreet/ppx_let *)
  (* This allows a more convenient syntax for using the Cmdliner
   * library: If we use let%map instead of normal "let", and we
   * have a declaration of the form:
   *
   * let%map x = e1 in e2
   *
   * even if e1 is of type 'a Term.t, we can use x as having type 'a
   * in the body of e2.
   *)
  let module Let_syntax = struct
    let return = Term.const
    let map ~f a = Term.(return f $ a)
    let both a b = Term.(const Tuple2.create $ a $ b)
  end
  in
  let flag info = Arg.value (Arg.flag info) in
  let opt conv ~default info = Arg.value (Arg.opt conv default info) in
  let%map verbose =
    let doc = "If present, print verbose debug information." in
    flag (Arg.info [ "v"; "verbose" ] ~doc)
  and dump_all =
    let doc = "If present, dump all IR debug info" in
    flag (Arg.info [ "dump-all" ] ~doc)
  and dump_parsing =
    let doc = "If present, print debug informaton from parsing." in
    flag (Arg.info [ "dump-parsing" ] ~doc)
  and dump_ast =
    let doc = "If present, print the parsed ast." in
    flag (Arg.info [ "dump-ast" ] ~doc)
  and dump_ir =
    let doc = "If present, print the translated ir ast." in
    flag (Arg.info [ "dump-ir" ] ~doc)
  and dump_abstr =
    let doc = "If present, print the abstract 3-address assembly." in
    flag (Arg.info [ "dump-abstr" ] ~doc)
  and dump_assem =
    let doc = "If present, print the final assembly." in
    flag (Arg.info [ "dump-assem" ] ~doc)
  and typecheck_only =
    let doc = "If present, exit after typechecking." in
    flag (Arg.info [ "t"; "typecheck-only" ] ~doc)
  and no_regalloc =
    let doc = "If present, skip register allocation." in
    flag (Arg.info [ "no-regalloc" ] ~doc)
  and regalloc_only =
    let doc = "Regalloc only for l1 checkpoint" in
    flag (Arg.info [ "r"; "regalloc-only" ] ~doc)
  and emit =
    let doc = "[abs|x86-64] The type of assembly $(docv) to emit." in
    opt
      Emit.conv
      ~default:Emit.Abstract_assem
      (Arg.info [ "e"; "emit" ] ~doc ~docv:"TARGET")
  and opt_level =
    let doc = "[0|1|2] The optimization level $(docv)." in
    opt
      Opt_level.conv
      ~default:Opt_level.Opt_none
      (Arg.info [ "O"; "opt" ] ~doc ~docv:"OPT")
  and include_header =
    let doc = "Optional header file" in
    opt
      IncludeHeader.conv
      ~default:"../runtime/15411-l3.h0"
      (Arg.info [ "l" ] ~doc ~docv:"HEADER")
  and filename =
    let doc = "The source file $(docv) to compile." in
    Arg.(required (pos 0 (some non_dir_file) None (info [] ~doc ~docv:"FILE")))
  and dump_only_times =
    let doc = "Dump only times taken for compilation." in
    flag (Arg.info [ "dump-only-times" ] ~doc)
  in
  { verbose
  ; dump_all
  ; dump_parsing
  ; dump_ast
  ; dump_ir
  ; dump_abstr
  ; dump_assem
  ; typecheck_only
  ; no_regalloc
  ; regalloc_only
  ; emit
  ; opt_level
  ; filename
  ; include_header
  ; dump_only_times
  }
;;

let say_if (v : bool) (f : unit -> string) = if v then prerr_endline (f ())

(* The main driver for the compiler: runs each phase. *)
let compile (cmd : cmd_line_args) : unit =
  let timestamps = Timestamp.init_timestamps () in
  let header_file = cmd.include_header in
  let header_ast = Parse.parse header_file in
  let header_elab_ast = Elaborate.elaborate header_ast in
  let header_env = Typechecker.header_typecheck header_elab_ast in
  say_if cmd.verbose (fun () -> "Parsing... " ^ cmd.filename);
  if cmd.dump_parsing then ignore (Parsing.set_trace true : bool);
  (* Parse *)
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "parsing";
  let ast = Parse.parse cmd.filename in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "parsing";
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "elaboration";
  let elaborated_ast = Elaborate.elaborate ast in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "elaboration";
  say_if cmd.dump_ast (fun () -> Ast.Print.pp_program elaborated_ast);
  say_if cmd.dump_all (fun () -> "\n-----------AST before typechecking-------------\n");
  say_if cmd.dump_all (fun () -> Ast.Print.pp_program elaborated_ast);
  (* Typecheck *)
  say_if cmd.verbose (fun () -> "Checking...");
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "typechecking";
  Typechecker.typecheck elaborated_ast header_env;
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "typechecking";
  if cmd.typecheck_only then exit 0;
  (* Translate *)
  let typechecked_ast = Elaborate_decl.elaborate_decl elaborated_ast in
  say_if cmd.dump_ast (fun () -> "\n-----------POST TYPECHECK AST-------------\n");
  say_if cmd.dump_ast (fun () -> Ast.Print.pp_program typechecked_ast);
  say_if cmd.verbose (fun () -> "Translating...");
  (* Start the temp count. This ensures that Temp.counter is in scope in all the 
     subsequent compiler phases, so that temp numbers used do not conflict across
     compiler phases. *)
  ignore (Temp.create () : Temp.t);
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "translation";
  let ir = Trans.translate typechecked_ast in
  let only_main = List.length ir = 1 in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "translation";
  say_if cmd.dump_ir (fun () -> Tree.Print.pp_program ir);
  say_if cmd.dump_all (fun () -> "\n-----------IR (Tree)-------------\n");
  say_if cmd.dump_all (fun () -> Tree.Print.pp_program ir);
  say_if cmd.verbose (fun () -> "Codegen...");
  (* Intermediate Code Gen *)
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "intcodegen";
  let three_addr_assem = Intcodegen.int_code_gen ir in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "intcodegen";
  say_if cmd.dump_all (fun () -> "\n-----------3-address assembly-------------\n");
  say_if cmd.dump_abstr (fun () -> Threeaddrassem.format three_addr_assem);
  say_if cmd.dump_all (fun () -> Threeaddrassem.format three_addr_assem);
  (* Instruction Selection *)
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "instrsel";
  let abstr_assem = Instrsel.instr_sel ~only_main three_addr_assem in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "instrsel";
  say_if cmd.dump_all (fun () -> "\n-----------Assem (after instr sel)-------------\n");
  say_if cmd.dump_all (fun () ->
    List.fold (List.map abstr_assem ~f:Assem.format_func) ~init:"" ~f:(fun x y ->
      x ^ "\n" ^ y));
  say_if cmd.dump_all (fun () -> Timestamp.print_timestamps timestamps);
  let temp_counter = Temp.get_counter () in
  say_if cmd.dump_all (fun () -> sprintf "\nNum temps: %i\n" temp_counter);
  (*   
  (* Register allocation, skip if there are too many operands*)
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "regalloc";
  let abstr_assem_coloured =
    if cmd.no_regalloc
    then abstr_assem
    else (
      match only_main with
      | true when temp_counter >= _skip_regalloc_l1_l2 -> abstr_assem
      | false when temp_counter >= _skip_regalloc_l3 -> abstr_assem
      | _ ->
        Regalloc.regalloc
          abstr_assem
          ~_skip_regalloc_per_function
          ~_skip_mcs
          ~debug:(cmd.dump_all || cmd.dump_only_times)
          ~timestamps)
    (* ~debug:cmd.dump_all) *)
    (* say_if cmd.dump_all (fun () -> "\n-----------Liveness-------------\n"); *)
  in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "regalloc";
  say_if cmd.dump_all (fun () -> "\n-----------Assem (After Regalloc)----------\n");
  say_if cmd.dump_all (fun () ->
    List.fold (List.map abstr_assem_coloured ~f:Assem.format_func) ~init:"" ~f:(fun x y ->
      x ^ "\n" ^ y)); *)
  say_if cmd.dump_all (fun () -> "\n-----------Assem (After Stack Spill)----------\n");
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "stackspill";
  let abstr_assem_no_temps = Stackspill.stack_spill ~only_main abstr_assem in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "stackspill";
  say_if cmd.dump_all (fun () ->
    List.fold (List.map abstr_assem_no_temps ~f:Assem.format_func) ~init:"" ~f:(fun x y ->
      x ^ "\n" ^ y));
  (* Codegen *)
  say_if cmd.dump_all (fun () -> "\n------------------x86----------------\n");
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "codegen";
  let x86_assem = Codegen.code_gen abstr_assem_no_temps in
  if cmd.dump_all || cmd.dump_only_times
  then Timestamp.mark_timestamp timestamps "codegen";
  say_if cmd.dump_assem (fun () ->
    List.fold (List.map x86_assem ~f:Assem.format_func) ~init:"" ~f:(fun x y ->
      x ^ "\n" ^ y));
  say_if cmd.dump_all (fun () ->
    List.fold (List.map x86_assem ~f:Assem.format_func) ~init:"" ~f:(fun x y ->
      x ^ "\n" ^ y));
  say_if (cmd.dump_all || cmd.dump_only_times) (fun () ->
    Timestamp.print_timestamps timestamps);
  match cmd.emit with
  (* Output: abstract 2-address assem *)
  | Abstract_assem ->
    let file = cmd.filename ^ ".abs" in
    say_if cmd.verbose (fun () -> sprintf "Writing abstract assem to %s..." file);
    Out_channel.with_file file ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Assem.format instr) in
      output_instr (Assem.Directive (".file\t\"" ^ cmd.filename ^ "\""));
      output_instr (Assem.Directive ".function\tmain()");
      Out_channel.fprintf
        out
        "%s\n"
        (List.fold (List.map abstr_assem ~f:Assem.format_func) ~init:"" ~f:(fun x y ->
           x ^ "\n" ^ y));
      output_instr (Assem.Directive ".ident\t\"15-411 L1 reference compiler\""))
    (* Output: x86 assembly *)
  | X86_64 ->
    let file = cmd.filename ^ ".s" in
    say_if cmd.verbose (fun () -> sprintf "Writing x86 assem to %s..." file);
    Out_channel.with_file file ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "%s\n" (Assem.format instr) in
      output_instr (Assem.Directive (".file\t\"" ^ cmd.filename ^ "\""));
      output_instr (Assem.Directive ".globl \"_c0_main\"");
      List.iter x86_assem ~f:(fun assem ->
        Out_channel.fprintf out "%s\n" (Assem.format_func assem)))
;;

let run (cmd : cmd_line_args) : unit =
  try
    if cmd.regalloc_only then failwith "regalloc only supported in l1" else compile cmd
  with
  | Error_msg.Error ->
    prerr_endline "Compilation failed.";
    exit 1
;;

(* Compiler entry point
 * Use the cmd_line_term to parse the command line arguments, and pass the
 * parsed args to the run function.
 *)
let main () =
  let open Cmdliner in
  let cmd_line_info = Cmd.info "c0c" ~doc:"Compile a c0c source file." in
  let cli_parse_result : cmd_line_args Cmd.t = Cmd.v cmd_line_info cmd_line_term in
  match Cmd.eval_value cli_parse_result with
  | Ok (`Ok cmd_line) -> run cmd_line
  | Ok `Version -> Stdlib.exit Cmd.Exit.ok
  | Ok `Help -> Stdlib.exit Cmd.Exit.ok
  | Error _ -> Stdlib.exit Cmd.Exit.cli_error
;;
