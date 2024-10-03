(* L1 Compiler
 * IR Trees
 * Author: Ethan Cheong <echeong@andrew.cmu.edu>, Wu Meng Hui <menghuiw@andrew.cmu.edu>
 *)

(* At this point, our program is represented by a list of function declarations 
   (func). These contain the function signature (including the function name and 
   all temps) and the function body (list of cmds)*)

(* pure binary operations. Or, Xor and And are bitwise operations. *)
type binop_pure =
  | Add
  | Sub
  | Mul
  | Or
  | Xor
  | And

(* These are also pure, but we treat them differently in translation *)
type binop_cmp =
  | Lt
  | Leq
  | Gt
  | Geq
  | Eq
  | Neq

(* Operations that are impure because they may throw an exception. *)
type binop_impure =
  | Div
  | Mod
  | Sal
  | Sar

(* MAX_INT is added to represent 0xFFFFFFFF. At this stage, all booleans are 
   represented as Int(0) or Int(1). *)
type const =
  | Int of Int32.t
  | MAX_INT

(* Expressions should be pure; they should have no side effects! *)
type exp =
  | Const of const
  | Temp of Temp.t
  | Binop_pure of
      { lhs : exp
      ; op : binop_pure
      ; rhs : exp
      }
  | Binop_cmp of
      { lhs : exp
      ; op : binop_cmp
      ; rhs : exp
      }
  | Addr_const of Int64.t (* 64-bit const used in address arithmetic. *)

(* descr * label_id. Each label needs an id since we can multiple labels of the 
   same type in a function. *)
type label = string * int

type cmd =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Move_truncate of
      { dest : Temp.t
      ; src : exp
      }
  | Move_sign_extend of
      { dest : Temp.t
      ; src : exp
      }
  | Move_zero_extend of
      { dest : Temp.t
      ; src : exp
      }
  | Binop_impure of
      { lhs : exp
      ; op : binop_impure
      ; rhs : exp
      ; dest : Temp.t
      }
  | Function_call of
      { dest : Temp.t
      ; ident : string (* function name *)
      ; args : exp list
      ; assign_res : bool
      }
  | If of
      { condition : exp
      ; lt : label
      ; lf : label
      }
  | Goto of label
  | Label of label
  | Return of exp
  | Return_void
  (* Access heap memory at disp(base, index, scale) and write result to dest.*)
  | Memory_read of
      { dest : exp
      ; disp : Int32.t
      ; base : exp
      ; index : exp
      ; scale : int
      }
  (* Write contents of src to heap at disp(base, index, scale). *)
  | Memory_write of
      { src : exp
      ; disp : Int32.t
      ; base : exp
      ; index : exp
      ; scale : int
      }
  (* Load effective address of disp(base, index, scale) into dest. *)
  | Load_effective_address of
      { dest : exp
      ; disp : Int32.t
      ; base : exp
      ; index : exp
      ; scale : int
      }
  | Comment of string (* Comment to be passed down to assembly *)
  | Nop (* No-op *)

type body = cmd list

type signature =
  { ident : string (* function name *)
  ; args : exp list (* function args *)
  ; tail_rec : bool (* whether the function is tail-recursive *)
  ; num_temps : int (* the number of temps assigned in that function body *)
  ; recursive : bool (* whether the function is recursive *)
  }

type func = signature * body
type program = func list

module Print : sig
  val pp_exp : exp -> string
  val pp_cmd : cmd -> string
  val pp_program : program -> string
end
