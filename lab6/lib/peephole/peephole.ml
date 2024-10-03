let peephole instrs ~_peephole_invert =
  let instrs = Fallthrough_jumps.fallthrough instrs in
  let instrs =
    if _peephole_invert then Change_ordering.change_ordering instrs else instrs
  in
  instrs
;;
