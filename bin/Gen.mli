type gen
val make_gen : unit -> gen
val sample_gen : gen -> int

type var
val make_param : gen -> var
val make_exist : gen -> var
val sample_var : var -> string
