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

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Addr_imm of Int64.t
  | Reg of
      { reg : reg
      ; size : Temp.size
      }
  | Temp of Temp.t
  | Stack_ref of
      { offset : Int32.t
      ; size : Temp.size
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

type one_addr_op = IDiv
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
  | Movsx of
      { dest : operand
      ; src : operand
      }
  | Movzx of
      { dest : operand
      ; src : operand
      }
  (* Mov from 64 bit to 32 bit register, zeroing out top *)
  | Mov_trunc of
      { dest : operand
      ; src : operand
      }
  | Load of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
  | Store of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; src : operand
      }
  | Lea of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
  | Pop of operand
  | Push of operand
  | Test of
      { lhs : operand
      ; rhs : operand
      }
  | Directive of string
  | Comment of string
  | Cmp of
      { lhs : operand
      ; rhs : operand
      }
  | Jc of
      { cmp : comparison
      ; label : string
      }
  | Jmp of string
  | Label of string
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

type func = signature * body

let size_of_operand : operand -> Temp.size = function
  | Imm _ -> DOUBLE
  | MAX_INT -> DOUBLE
  | Reg { size; _ } -> size
  | Temp t -> Temp.size t
  | Stack_ref { size; _ } -> size
  | Addr_imm _ -> QUAD
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
  | Temp.DOUBLE ->
    (match reg with
     | AX | BX | CX | DX | SP | BP | SI | DI -> "%e" ^ format_reg reg
     | _ -> "%" ^ format_reg reg ^ "d")
  | Temp.QUAD ->
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
  | Addr_imm i -> "$" ^ Int64.to_string i
;;

let format_size = function
  | Temp.QUAD -> "q"
  | Temp.DOUBLE -> "l"
;;

let format_operand_with_new_size operand new_size =
  match operand with
  | Imm _ | MAX_INT | Temp _ | Stack_ref _ | Addr_imm _ -> format_operand operand
  | Reg { reg; _ } -> format_reg_with_size reg new_size
;;

let format_args arg_list =
  let string_list = List.map arg_list ~f:format_operand in
  "(" ^ String.concat ~sep:", " string_list ^ ")"
;;

let format_disp disp = Int32.to_string disp

(* Formats assembly to the correct representation, including handling for sizes. *)
let format = function
  (* Be VERY CAREFUL when modifying this function. *)
  | Mov { src; dest } ->
    (match src, dest with
     (* Immediates can only be mapped to 32 bit registers / 32 bit refs. *)
     | Imm _, _ | MAX_INT, _ ->
       sprintf
         "movl\t %s, %s\n"
         (format_operand src)
         (format_operand_with_new_size dest DOUBLE)
     (* If the source is a quad immediate, we have to use movabs. *)
     | Addr_imm _, Reg _ ->
       sprintf "movabsq\t %s, %s\n" (format_operand src) (format_operand dest)
       (* If we try to write a quad immediate onto the stack, 
        we have to use a workaround  https://stackoverflow.com/questions/62771323/why-we-cant-move-a-64-bit-immediate-value-to-memory 
        ... *)
       (* This might require a fix *)
     | Addr_imm _, Stack_ref { size = QUAD; _ } ->
       sprintf
         "movabsq\t %s, %%r10\nmovq\t %%r10, %s\n"
         (format_operand src)
         (format_operand dest)
     (* For anything else, we know the sizes will match, so we are fine. Always format
        RSP to QUAD, but this should be done by now. *)
     | _, _ ->
       let size = size_of_operand src in
       sprintf
         "mov%s\t %s, %s\n"
         (format_size size)
         (format_operand src)
         (format_operand dest))
  | Movsx { src; dest } ->
    sprintf "movsxd\t %s, %s\n" (format_operand src) (format_operand dest)
    (* Movsxd will move the double word in src and sign extend it to a quad
       word in dest. *)
  | Movzx { src; dest } ->
    (* By default, a 32-bit register load will zero out the top 64 bits. *)
    sprintf
      "movl\t %s, %s\n"
      (format_operand src)
      (format_operand_with_new_size dest DOUBLE)
  | Mov_trunc { src; dest } ->
    (* Get the bottom 32 bits, whether on a register or on a stack. *)
    sprintf
      "movl\t %s, %s /* truncate */ \n"
      (format_operand_with_new_size src DOUBLE)
      (format_operand dest)
  (* If scale is zero, it means that we are doing a load of the form disp(base). *)
  | Load { dest; disp; base; scale; _ } when scale = 0 ->
    sprintf
      "mov%s\t %s(%s), %s /* Load */ \n"
      (format_size (size_of_operand dest))
      (format_disp disp)
      (format_operand base)
      (format_operand dest)
  | Load { dest; disp; base; index; scale } ->
    if not (Temp.equal_size (size_of_operand base) (size_of_operand index))
    then failwith "base and index must be same size in load";
    sprintf
      "mov%s\t %s(%s, %s, %d), %s /* Load */ \n"
      (format_size (size_of_operand dest))
      (format_disp disp)
      (format_operand base)
      (format_operand index)
      scale
      (format_operand dest)
  (* If scale is zero, it means that we are doing a load of the form disp(base). *)
  | Store { src; disp; base; scale; _ } when scale = 0 ->
    sprintf
      "mov%s\t %s, %s(%s) /* Store */ \n"
      (format_size (size_of_operand src))
      (format_operand src)
      (format_disp disp)
      (format_operand base)
  | Store { src; disp; base; index; scale } ->
    if not (Temp.equal_size (size_of_operand base) (size_of_operand index))
    then failwith "base and index must be same size in load";
    sprintf
      "mov%s\t %s, %s(%s, %s, %d) /* Store */ \n"
      (format_size (size_of_operand src))
      (format_operand src)
      (format_disp disp)
      (format_operand base)
      (format_operand index)
      (* Format the index to have same size as the base. *)
      scale
  (* If scale is zero, it means that we are doing a lea of the form disp(base). *)
  | Lea { dest; disp; base; scale; _ } when scale = 0 ->
    sprintf
      "lea%s\t %s(%s), %s\n"
      (format_size (size_of_operand dest))
      (format_disp disp)
      (format_operand base)
      (format_operand dest)
  | Lea { dest; disp; base; index; scale } ->
    if not (Temp.equal_size (size_of_operand base) (size_of_operand index))
    then failwith "base and index must be same size in load";
    sprintf
      "lea%s\t %s(%s, %s, %d), %s\n"
      (format_size (size_of_operand dest))
      (format_disp disp)
      (format_operand base)
      (format_operand index)
      scale
      (format_operand dest)
  | Push op -> sprintf "push\t %s\n" (format_operand op)
  | Pop op -> sprintf "pop\t %s\n" (format_operand op)
  | Binop { op; src; dest } ->
    (* Note that for binops, we have to do things like sub $8, RSP. 
      We always want to use the destination size. (TODO: Verify whether this is true??)
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
     (* IDiv may be used on doubles or quads. *)
     | IDiv ->
       sprintf "idiv%s \t%s\n" (format_size (size_of_operand src)) (format_operand src))
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
