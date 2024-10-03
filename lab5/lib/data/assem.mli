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

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Addr_imm of Int64.t (* 64-bit immediate representing an address *)
  | Reg of
      { reg : reg
      ; size : Temp.size
      }
  | Temp of Temp.t (* Used for stack spilling *)
  | Stack_ref of
      (* RSP offsets *)
      
      { offset : Int32.t
      ; size : Temp.size
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
  | Shr
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
  (* Mov from 32 bit src to 64 bit dest, sign extending src into dest *)
  | Movsx of
      { dest : operand
      ; src : operand
      }
  (* Mov from 32 bit src to 64 bit dest, zeroing out the top 32 bits of dest *)
  | Movzx of
      { dest : operand
      ; src : operand
      }
  (* Mov from 64 bit to 32 bit register, zeroing out top 32 bits of dest. *)
  | Mov_trunc of
      { dest : operand
      ; src : operand
      }
    (* load contents of memory at disp(base, index, scale) into dest *)
  | Load of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
    (* store contents of src into of memory at disp(base, index, scale) *)
  | Store of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; src : operand
      }
    (* load effective address disp(base, index, scale) into dest *)
  | Lea of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
  (* We only use push and pop to solve the mem read/load codegen problem; it
     only appears in final outputted assembly. *)
  | Pop of operand
  | Push of operand
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

val size_of_operand : operand -> Temp.size
val cmp_of_three_addr_cmp : Threeaddrassem.comparison -> comparison
val format_reg : reg -> string
val format_operand : operand -> string
val format : instr -> string
val format_func : signature * body -> string
