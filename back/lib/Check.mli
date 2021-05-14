open Syntax
open Context
type 'r fail = Typeset.eDSL -> 'r
type ('a, 'r) return = ('a -> 'r) -> 'r
val subtype : poly -> poly -> tctx -> 'a fail -> (unit, 'a) return
val synth_expr : expr -> tctx -> 'a fail -> (poly, 'a) return
val synth_stmt : stmt -> tctx -> 'a fail -> (poly, 'a) return
val check_expr : expr -> poly -> tctx -> 'a fail -> (unit, 'a) return
val check_stmt : stmt -> poly -> tctx -> 'a fail -> (unit, 'a) return
val check_prog : prog -> tctx -> 'a fail -> (tctx, 'a) return
val generalize : poly -> (poly, 'a) return
