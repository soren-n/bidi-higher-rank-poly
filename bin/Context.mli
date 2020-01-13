open Util
open Syntax
type ctx
val empty : ctx
val make : (label, poly) Env.env -> label Set.set -> ctx
val get_venv : ctx -> ((label, poly) Env.env -> 'a) -> 'a
val get_tenv : ctx -> (label Set.set -> 'a) -> 'a
val update : label -> poly -> ctx -> (ctx -> 'a) -> 'a
val extend : label -> ctx -> (ctx -> 'a) -> 'a
val lookup : label -> ctx -> (string -> 'a) -> (poly -> 'a) -> 'a
val bound : label -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
val print : ctx -> (string -> 'a) -> 'a
