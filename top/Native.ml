open Util
open Bin

let venv =
  Env.empty

let tenv =
  Set.empty

let ctx =
  Context.make venv tenv
