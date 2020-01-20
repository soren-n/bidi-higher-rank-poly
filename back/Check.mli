open Syntax
open Context
val subtype : poly -> poly -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
val synth : expr -> ctx -> (string -> 'a) -> (poly -> 'a) -> 'a
val check : expr -> poly -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
