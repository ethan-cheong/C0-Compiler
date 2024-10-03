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
 *   - TODO: Add support for expect tests
 *   - Update to Core v0.14
 *)

open Core

(* Constants for optimisation *)
(* Skip maximum cardinality search if the interference graph has more than
   [_skip_mcs] nodes *)
let _skip_mcs = 1000

(* Skip greedy graph colouring if the interference graph has more than 
    [_skip_regalloc] nodes*)
let _skip_regalloc = 2000

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

type cmd_line_args =
  { verbose : bool
  ; dump_parsing : bool
  ; dump_ast : bool
  ; dump_ir : bool
  ; dump_assem : bool
  ; typecheck_only : bool
  ; regalloc_only : bool
  ; emit : Emit.t
  ; opt_level : Opt_level.t
  ; filename : string
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
  and dump_parsing =
    let doc = "If present, print debug informaton from parsing." in
    flag (Arg.info [ "dump-parsing" ] ~doc)
  and dump_ast =
    let doc = "If present, print the parsed ast." in
    flag (Arg.info [ "dump-ast" ] ~doc)
  and dump_ir =
    let doc = "If present, print the translated ir ast." in
    flag (Arg.info [ "dump-ir" ] ~doc)
  and dump_assem =
    let doc = "If present, print the final assembly." in
    flag (Arg.info [ "dump-assem" ] ~doc)
  and typecheck_only =
    let doc = "If present, exit after typechecking." in
    flag (Arg.info [ "t"; "typecheck-only" ] ~doc)
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
  and filename =
    let doc = "The source file $(docv) to compile." in
    Arg.(required (pos 0 (some non_dir_file) None (info [] ~doc ~docv:"FILE")))
  in
  { verbose
  ; dump_parsing
  ; dump_ast
  ; dump_ir
  ; dump_assem
  ; typecheck_only
  ; regalloc_only
  ; emit
  ; opt_level
  ; filename
  }
;;

let say_if (v : bool) (f : unit -> string) = if v then prerr_endline (f ())

let regalloc (cmd : cmd_line_args) =
  match String.chop_suffix cmd.filename ~suffix:".in" with
  | None ->
    prerr_endline "Invalid input filename";
    exit 1
  | Some base_filename ->
    let input_json = Yojson.Basic.from_file cmd.filename in
    let input = Lab1_checkpoint.program_of_json input_json in
    let output = Regalloc.regalloc input in
    let filename = base_filename ^ ".out" in
    Out_channel.with_file filename ~f:(fun out ->
      Out_channel.output_string
        out
        (output |> Lab1_checkpoint.json_of_allocations |> Yojson.Basic.to_string))
;;

(* The main driver for the compiler: runs each phase. *)
let compile (cmd : cmd_line_args) : unit =
  (* Run the L1 checkpoint and do nothing else *)
  say_if cmd.regalloc_only (fun () -> "Regalloc checkpoint with file..." ^ cmd.filename);
  if cmd.regalloc_only
  then regalloc cmd
  else say_if cmd.verbose (fun () -> "Parsing... " ^ cmd.filename);
  if cmd.dump_parsing then ignore (Parsing.set_trace true : bool);
  (* Parse *)
  let ast = Parse.parse cmd.filename in
  say_if cmd.dump_ast (fun () -> Ast.Print.pp_program ast);
  (* Typecheck *)
  say_if cmd.verbose (fun () -> "Checking...");
  Typechecker.typecheck ast;
  if cmd.typecheck_only then exit 0;
  (* Translate *)
  say_if cmd.verbose (fun () -> "Translating...");
  let ir = Trans.translate ast in
  say_if cmd.dump_ir (fun () -> Tree.Print.pp_program ir);
  say_if cmd.verbose (fun () -> "Codegen...");
  (* Intermediate Code Gen *)
  let abstr_assem = Intcodegen.int_code_gen ir in
  (* Liveness analysis, skip if there are too many operands *)
  let liveness_info, operand_count = Liveness.liveness abstr_assem in
  let abstr_assem_coloured =
    if operand_count > _skip_regalloc
    then abstr_assem
    else (
      let intf_graph = Buildintfgraph.build_interference_graph liveness_info in
      let node_ordering =
        if operand_count > _skip_mcs
        then Hashtbl.keys intf_graph
        else Maxcardsearch.max_cardinality_search intf_graph
      in
      Replacetemps.replace_temps
        abstr_assem
        (Greedycolouring.greedy_colouring ~debug:false intf_graph node_ordering))
  in
  let abstr_assem_no_temps = Stackspill.stack_spill abstr_assem_coloured in
  let x86_assem = Instrtrans.instr_trans abstr_assem_no_temps in
  say_if cmd.dump_assem (fun () -> List.to_string ~f:Finalassem.format x86_assem);
  match cmd.emit with
  (* Output: abstract 3-address assem *)
  | Abstract_assem ->
    let file = cmd.filename ^ ".abs" in
    say_if cmd.verbose (fun () -> sprintf "Writing abstract assem to %s..." file);
    Out_channel.with_file file ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Assem.format instr) in
      output_instr (Assem.Directive (".file\t\"" ^ cmd.filename ^ "\""));
      output_instr (Assem.Directive ".function\tmain()");
      List.iter ~f:output_instr abstr_assem_coloured;
      output_instr (Assem.Directive ".ident\t\"15-411 L1 reference compiler\""))
    (* Output: x86 assembly *)
  | X86_64 ->
    let file = cmd.filename ^ ".s" in
    say_if cmd.verbose (fun () -> sprintf "Writing x86 assem to %s..." file);
    Out_channel.with_file file ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "%s\n" (Finalassem.format instr) in
      output_instr (Finalassem.Directive "_c0_main:");
      output_instr (Finalassem.Directive (".file\t\"" ^ cmd.filename ^ "\""));
      output_instr (Finalassem.Directive ".globl \"_c0_main\"");
      List.iter ~f:output_instr x86_assem)
;;

let run (cmd : cmd_line_args) : unit =
  try if cmd.regalloc_only then regalloc cmd else compile cmd with
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
