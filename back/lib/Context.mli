open Util
open Syntax
open Naming
type tctx
val empty : tctx
val make : (label, poly) Env.env -> (label, poly) Env.env -> tctx
val get_venv : tctx -> ((label, poly) Env.env -> 'a) -> 'a
val get_tenv : tctx -> ((label, poly) Env.env -> 'a) -> 'a
val bind_v : label -> poly -> tctx -> (tctx -> 'a) -> 'a
val bind_t : label -> poly -> tctx -> (tctx -> 'a) -> 'a
val lookup_v : label -> tctx -> (Typeset.eDSL -> 'a) -> (poly -> 'a) -> 'a
val lookup_t : label -> tctx -> (Typeset.eDSL -> 'a) -> (poly -> 'a) -> 'a
val bound_v : label -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
val bound_t : label -> tctx -> (Typeset.eDSL -> 'a) -> (unit -> 'a) -> 'a
val print : ctx -> tctx -> (string -> 'a) -> 'a
