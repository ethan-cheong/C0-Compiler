open Core
module SymbolTable = Type_modules.SymbolTable

let typedefs =
  match
    SymbolTable.of_alist
      ~growth_allowed:true
      ~size:500
      [ Symbol.symbol "int", (); Symbol.symbol "bool", () ]
  with
  | `Ok x -> x
  | `Duplicate_key _ -> failwith "wtf?"
;;

let add_typedef x =
  match SymbolTable.add typedefs ~key:x ~data:() with
  | `Ok -> ()
  | `Duplicate -> failwith "variable has already been used as typedef"
;;

let check_typedef x =
  match SymbolTable.find typedefs x with
  | Some _ -> true
  | None -> false
;;
