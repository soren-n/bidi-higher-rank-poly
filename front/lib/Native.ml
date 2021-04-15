open Util
open Back
open Syntax

let venv =
  Env.empty

let tenv =
  Context.make
    (Env.from_list
    [ "main", poly_arrow poly_unit poly_unit
    ])
    Env.empty
