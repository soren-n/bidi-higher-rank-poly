open Util
open Syntax
type ctx
val empty : ctx
val make : (label, poly) Env.env -> (label, poly) Env.env -> ctx
val get_venv : ctx -> ((label, poly) Env.env -> 'a) -> 'a
val get_tenv : ctx -> ((label, poly) Env.env -> 'a) -> 'a
val bind_v : label -> poly -> ctx -> (ctx -> 'a) -> 'a
val bind_t : label -> poly -> ctx -> (ctx -> 'a) -> 'a
val lookup_v : label -> ctx -> (string -> 'a) -> (poly -> 'a) -> 'a
val lookup_t : label -> ctx -> (string -> 'a) -> (poly -> 'a) -> 'a
val bound_v : label -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
val bound_t : label -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
val print : Naming.ctx -> ctx -> (string -> 'a) -> 'a
