(* L1 Compiler
 * Assembly. 
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * Resembles final assembly, and allows for operands to be temps.
 *)

(* Representations of the 16 registers available. *)
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

(* QUAD is only necessary when we consider l4. *)
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
  (* Used for stack spilling *)
  | Stack_ref of
      { offset : Int32.t
      ; size : operand_size
      }
[@@deriving compare, sexp, hash, equal]

(* This is used to indicate to the register allocator whether the instruction
   was originally a div or a mod. *)
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
  | Ret
  | Call of
      { ident : string
      ; args :
          operand list (* This should only contain args actually used in the callee. *)
      }

type body = instr list

type signature =
  { label : string (* Function name *)
  ; args : operand list
      (* Required for backend, but omitted in final assem output. Only contains args actually used in the function. *)
  ; tail_rec : bool (* Indicates if the function is tail_rec. Required for stackspill. *)
  ; regalloc : bool
      (* Indicates if the assembly has undergone regalloc. Do not use red zone if so. *)
  ; num_temps : int
      (* Number of temps allocated in the function body before regalloc and stackspill. Used by regalloc.*)
  }

type func = signature * body

val size_of_operand : operand -> operand_size
val cmp_of_three_addr_cmp : Threeaddrassem.comparison -> comparison
val format_reg : reg -> string
val format_operand : operand -> string
val format : instr -> string
val format_func : signature * body -> string
