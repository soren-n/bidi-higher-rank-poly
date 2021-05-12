open Syntax
open Naming
val layout_mono : ctx -> mono -> (Typeset.eDSL -> 'a) -> 'a
val layout_poly : ctx -> poly -> (Typeset.eDSL -> 'a) -> 'a
val layout_expr : ctx -> expr -> (Typeset.eDSL -> 'a) -> 'a
val layout_stmt : ctx -> stmt -> (Typeset.eDSL -> 'a) -> 'a
val layout_prog : ctx -> prog -> (Typeset.eDSL -> 'a) -> 'a
val print_mono : ctx -> mono -> (string -> 'a) -> 'a
val print_poly : ctx -> poly -> (string -> 'a) -> 'a
val print_expr : ctx -> expr -> (string -> 'a) -> 'a
val print_stmt : ctx -> stmt -> (string -> 'a) -> 'a
val print_prog : ctx -> prog -> (string -> 'a) -> 'a
