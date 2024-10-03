(* L1 Compiler
 * SSA
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 * 
 * SSA is similar to ThreeAssem. 
 *)

type operand =
  | Imm of Int32.t
  | MAX_INT
  | Addr_imm of Int64.t
  | Temp of Temp.t
[@@deriving compare, sexp, hash, equal]

(* Unary operations (negation, bitwise not) have been converted to their binop
  equivalents after codegen. *)
type operation =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Or
  | Xor
  | And
  | Sal
  | Sar
  | Shr
[@@deriving compare, sexp, hash, equal]

type comparison =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq
[@@deriving compare, sexp, hash, equal]

type instr =
  (* dest <- lhs op rhs *)
  | Binop of
      { op : operation
      ; dest : operand
      ; lhs : operand
      ; rhs : operand
      }
  | Mov of
      { dest : operand
      ; src : operand
      }
  | Movsx of
      (* Mov with sign extend*)
      
      { dest : operand
      ; src : operand
      }
  | Movzx of
      (* Mov with zero extend*)
      
      { dest : operand
      ; src : operand
      }
  | Mov_trunc of
      (* Mov from 64 to 32 bit *)
      
      { dest : operand
      ; src : operand
      }
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string
  | Cmp of
      { lhs : operand
      ; rhs : operand
      }
  | If of
      { lhs : operand
      ; rhs : operand
      ; condition : comparison
      ; lt : string
      ; lf : string
      }
  (* goto label *)
  | Jump of string
  | Label of string
  | Ret of { src : operand }
  | Ret_void
  | CallF of
      { dest : operand
      ; ident : string (* These are the actual function labels.*)
      ; args : operand list
      ; assign_res : bool
      }
  (* Store contents of src into memory at dist(base, index, scale) *)
  | Store of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; src : operand
      }
  (* Load contents at dist(base, index, scale) into dest *)
  | Load of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
    (* Load effective address of dist(base, index, scale) into dest *)
  | Lea of
      { disp : Int32.t
      ; base : operand
      ; index : operand
      ; scale : int
      ; dest : operand
      }
  | Nop
  | Phi of
      { args : operand list
      ; dest : operand
      }
(* Phi function! *)
[@@deriving compare, sexp, hash, equal]

type body = instr list

type header =
  { ident : string (* Name of basic block *)
  ; args : operand list (* args (temps) that are in scope in the function. *)
  ; from_func : bool (* Whether the basic block comes from a function. *)
  ; tail_rec : bool (* Whether the function is tail recursive. *)
  ; num_temps : int (* Number of temps used in the function body *)
  ; recursive : bool (* Whether the function is recursive *)
  }

type basic_block = header * body
type t = basic_block list

val format_binop : operation -> string
val format_operand : operand -> string
val format_instr : instr -> string
val format_header : header -> string
val format : basic_block list -> string
val format_comparison : comparison -> string
