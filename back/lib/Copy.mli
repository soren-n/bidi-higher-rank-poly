open Syntax
val copy_mono : mono -> (mono -> 'a) -> 'a
val copy_poly : poly -> (poly -> 'a) -> 'a
val copy_expr : expr -> (expr -> 'a) -> 'a
val copy_stmt : stmt -> (stmt -> 'a) -> 'a
