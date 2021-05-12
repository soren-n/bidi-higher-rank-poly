open Syntax
open Context
val check_mono : mono -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_poly : poly -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_expr : expr -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_stmt : stmt -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_prog : prog -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
