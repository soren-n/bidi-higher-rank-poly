open Syntax
open Naming
val print_mono : ctx -> mono -> (string -> 'a) -> 'a
val print_poly : ctx -> poly -> (string -> 'a) -> 'a
val print_expr : ctx -> expr -> (string -> 'a) -> 'a
