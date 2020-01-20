type gen
val make_gen : unit -> gen
val sample : gen -> int

type ctx
val make_ctx : unit -> ctx
val sample_label : ctx -> (string -> 'a) -> 'a
val sample_exist : ctx -> (string -> 'a) -> 'a
