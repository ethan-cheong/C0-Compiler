(* L1 Compiler
 * Assembly
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Resembles final assembly, and allows for operands to be temps.
 *)

open Core
module ThreeAS = Threeaddrassem

(* Assem is used in instrsel, regalloc, stackspill and codegen. Some variant 
    constructors (for example, Temps as operands) are not valid in certain
    phases. We add checks in those phases to ensure this is the case. *)

(* Caller-saved registers are listed first so that they will be used by the 
   register allocator before callee-saved ones. We use the suggested ordering
   from lecture notes. *)
type reg =
  | AX
  | DI
  | SI
  | DX
  | CX
  | R8
  | R9
  | R10
  | R11
  | BX
  | BP
  | R12
  | R13
  | R14
  | R15
  | SP
[@@deriving compare, sexp, hash, equal]

type operand_size =
  | QUAD
  | DOUBLE
[@@deriving compare, sexp, hash, equal]

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Reg of
      { reg : reg
      ; size : operand_size
      }
  | Temp of Temp.t
  | Stack_ref of
      { offset : Int32.t
      ; size : operand_size
      }
[@@deriving compare, sexp, hash, equal]

type div_type =
  | Div
  | Mod
  | NotDiv

type two_addr_op =
  | Add
  | Sub
  | IMul
  | Sal
  | Sar
  | Xor
  | And
  | Or

type one_addr_op =
  | IDiv
  | Pop
  | Push

type zero_addr_op = Cltd

type comparison =
  | L
  | Le
  | G
  | Ge
  | E
  | Ne
  | Z

type instr =
  | Unop of
      { op : one_addr_op
      ; src : operand
      ; div_type : div_type
      }
  | Nullop of { op : zero_addr_op }
  | Binop of
      { op : two_addr_op
      ; src : operand
      ; dest : operand
      }
  | Mov of
      { dest : operand
      ; src : operand
      }
    (* load contents at addr into dest *)
  | Load of
      { addr : operand
      ; dest : operand
      ; offset : Int32.t
      }
  (* Store contents at src into addr *)
  | Store of
      { addr : operand
      ; src : operand
      ; offset : Int32.t
      }
  | Test of
      { lhs : operand
      ; rhs : operand
      }
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string
  | Cmp of
      { lhs : operand
      ; rhs : operand
      }
  (* j(cmp) label *)
  | Jc of
      { cmp : comparison
      ; label : string
      }
  (* goto label *)
  | Jmp of string
  | Label of string
  (* Args are implicit; they aren't output, but are used in regalloc.
     Each function declaration has a signature. *)
  | Ret
  | Call of
      { ident : string
      ; args : operand list
      }

type body = instr list

type signature =
  { label : string
  ; args : operand list
  ; tail_rec : bool
  ; regalloc : bool
  ; num_temps : int
  }
(* Args are implicit; they aren't output, but are used in regalloc. *)

type func = signature * body

let size_of_operand = function
  | Imm _ -> DOUBLE
  | MAX_INT -> DOUBLE
  | Reg { size; _ } -> size
  | Temp _ -> DOUBLE (* FOR NOW *)
  | Stack_ref { size; _ } -> size
;;

(* functions that format assembly output *)

let cmp_of_three_addr_cmp : ThreeAS.comparison -> comparison = function
  | ThreeAS.Lt -> L
  | ThreeAS.Leq -> Le
  | ThreeAS.Gt -> G
  | ThreeAS.Geq -> Ge
  | ThreeAS.Eq -> E
  | ThreeAS.Neq -> Ne
;;

let format_reg = function
  | AX -> "ax"
  | BX -> "bx"
  | CX -> "cx"
  | DX -> "dx"
  | SP -> "sp"
  | BP -> "bp"
  | SI -> "si"
  | DI -> "di"
  | R8 -> "r8"
  | R9 -> "r9"
  | R10 -> "r10"
  | R11 -> "r11"
  | R12 -> "r12"
  | R13 -> "r13"
  | R14 -> "r14"
  | R15 -> "r15"
;;

let format_reg_with_size reg size =
  match size with
  | DOUBLE ->
    (match reg with
     | AX | BX | CX | DX | SP | BP | SI | DI -> "%e" ^ format_reg reg
     | _ -> "%" ^ format_reg reg ^ "d")
  | QUAD ->
    (match reg with
     | AX | BX | CX | DX | SP | BP | SI | DI -> "%r" ^ format_reg reg
     | _ -> "%" ^ format_reg reg)
;;

let format_two_addr_op : two_addr_op -> string = function
  | Add -> "add"
  | Sub -> "sub"
  | IMul -> "imul"
  | Sal -> "sal"
  | Sar -> "sar"
  | Xor -> "xor"
  | And -> "and"
  | Or -> "or"
;;

let format_one_addr_op : one_addr_op -> string = function
  | IDiv -> "idiv"
  | Push -> "pushq"
  | Pop -> "popq"
;;

let format_zero_addr_op : zero_addr_op -> string = function
  | Cltd -> "cltd"
;;

let format_comparison : comparison -> string = function
  | L -> "l"
  | Le -> "le"
  | G -> "g"
  | Ge -> "ge"
  | E -> "e"
  | Ne -> "ne"
  | Z -> "z"
;;

let format_operand = function
  | Imm imm -> "$" ^ Int32.to_string imm
  | MAX_INT -> "$0xffffffff"
  | Temp t -> Temp.name t
  | Reg { reg; size } -> format_reg_with_size reg size
  | Stack_ref { offset; _ } -> Int32.to_string offset ^ "(%rsp)"
;;

let format_size = function
  | QUAD -> "q"
  | DOUBLE -> "l"
;;

let format_operand_with_new_size operand new_size =
  match operand with
  | Imm _ | MAX_INT | Temp _ | Stack_ref _ -> format_operand operand
  | Reg { reg; _ } -> format_reg_with_size reg new_size
;;

let format_args arg_list =
  let string_list = List.map arg_list ~f:format_operand in
  "(" ^ String.concat ~sep:", " string_list ^ ")"
;;

(* Formats assembly to the correct representation, including handling for sizes. *)
let format = function
  (* Be VERY CAREFUL when modifying this function. *)
  | Mov { src; dest } ->
    (match src, dest with
     (* If we access from memory, we should move the amount required bytes. *)
     (* | Ref _, _ ->
       sprintf
         "mov%s\t %s, %s\n"
         (format_size (size_of_operand dest))
         (format_operand_with_new_size src QUAD)
         (format_operand dest)
     | _, Ref _ ->
       sprintf
         "mov%s\t %s, %s\n"
         (format_size (size_of_operand src))
         (format_operand src)
         (format_operand_with_new_size dest QUAD) *)
     (* Immediates can only be mapped to 32 bit registers / 32 bit refs. *)
     | Imm _, _ | MAX_INT, _ ->
       sprintf
         "movl\t %s, %s\n"
         (format_operand src)
         (format_operand_with_new_size dest DOUBLE)
     (* For anything else, we use the size of the src and the dest. *)
     | _, _ ->
       let size = size_of_operand src in
       sprintf
         "mov%s\t %s, %s\n"
         (format_size size)
         (format_operand src)
         (format_operand_with_new_size dest size))
  | Load { addr; dest; offset } ->
    (match addr with
     | Reg { reg = SP; _ } ->
       sprintf (* Always format SP to RSP *)
         "mov%s\t %s(%s), %s\n"
         (format_size (size_of_operand dest))
         (Int32.to_string offset)
         (format_operand_with_new_size addr QUAD)
         (format_operand dest)
     | _ ->
       sprintf
         "mov%s\t %s(%s), %s\n" (* otherwise, just use the size of the src*)
         (format_size (size_of_operand addr))
         (Int32.to_string offset)
         (format_operand addr)
         (format_operand dest))
  | Store { addr; src; offset } ->
    (match addr with
     | Reg { reg = SP; _ } ->
       sprintf (* Always format SP to RSP *)
         "mov%s\t %s, %s(%s)\n"
         (format_size (size_of_operand src))
         (format_operand src)
         (Int32.to_string offset)
         (format_operand_with_new_size addr QUAD)
     | _ ->
       sprintf
         "mov%s\t %s, %s(%s)\n"
         (format_size (size_of_operand src))
         (format_operand src)
         (Int32.to_string offset)
         (format_operand addr))
  | Binop { op; src; dest } ->
    (* Note that for binops, we have to do things like sub $8, RSP. 
      We always want to use the destination size. (Verify whether this is true??)
       *)
    let size = size_of_operand dest in
    sprintf
      "%s%s\t%s, %s\n"
      (format_two_addr_op op)
      (format_size size)
      (format_operand src)
      (format_operand dest)
  | Unop { op; src; _ } ->
    (match op with
     (* Pop sizes don't actually matter *)
     | Pop | Push -> sprintf "%s \t%s\n" (format_one_addr_op op) (format_operand src)
     (* IDiv is only used on ints. *)
     | IDiv ->
       sprintf "idivl \t%s\n" (format_operand src)
       (* Pushing a register always puts the entire register on the stack.
        When we push an immediate, we have to be careful. *))
  | Nullop { op } -> sprintf "%s\n" (format_zero_addr_op op)
  | Directive dir -> sprintf "%s\n" dir
  | Comment comment -> sprintf "/* %s */\n" comment
  | Cmp { lhs; rhs } -> sprintf "cmp\t %s, %s\n" (format_operand lhs) (format_operand rhs)
  | Test { lhs; rhs } -> sprintf "test %s, %s\n" (format_operand lhs) (format_operand rhs)
  | Label label -> sprintf "%s:\n" label
  | Jc { cmp; label } -> sprintf "j%s %s\n" (format_comparison cmp) label
  | Jmp s -> sprintf "jmp %s\n" s
  | Ret -> "ret\n"
  | Call { ident; args } -> sprintf "call %s /* args:%s */\n" ident (format_args args)
;;

(* Use a buffer when formatting assem so we don't timeout when actually 
   outputting the file *)
let format_func (signature, body) =
  let buf = Buffer.create 16 in
  let formatted_body = List.map body ~f:format in
  Buffer.add_string
    buf
    (sprintf
       "%s: /* %s %s args: %s num_temps: %d*/\n"
       signature.label
       (if signature.tail_rec then "tr" else "")
       (if signature.regalloc then "regalloced" else "")
       (format_args signature.args)
       signature.num_temps);
  List.iter ~f:(Buffer.add_string buf) formatted_body;
  Buffer.contents buf
;;
