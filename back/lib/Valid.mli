open Util
open Typeset
open Syntax
open Context
val check_mono : mono -> tctx -> (eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_poly : poly -> tctx -> (eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_expr : expr -> tctx -> (eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_stmt : stmt -> tctx -> (eDSL -> 'a) -> (unit -> 'a) -> 'a
val check_prog : prog -> tctx -> (eDSL -> 'a) -> (unit -> 'a) -> 'a
