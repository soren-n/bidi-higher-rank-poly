open Syntax
open Context
val check_mono : mono -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
val check_poly : poly -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
val check_expr : expr -> ctx -> (string -> 'a) -> (unit -> 'a) -> 'a
