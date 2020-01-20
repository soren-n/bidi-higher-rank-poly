open Back
open Front
open Poly
open Expr

let (<:) left right =
  Check.subtype left right Native.tenv
    (fun msg -> print_endline msg; false)
    (fun () -> true)

let (==>) expr return =
  Check.synth expr Native.tenv
    (fun msg -> print_endline msg; assert false)
    return

let (<==) expr poly =
  Check.check expr poly Native.tenv
    (fun msg -> print_endline msg; false)
    (fun () -> true)

let interp expr =
  Interp.eval expr Native.venv @@ fun value ->
  Interp.value_expr value @@ fun expr1 ->
  expr1

(* Tests *)
let subtype_id_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:50
    ~name:"subtype_identity_sound"
    (arbitrary_poly ctx)
    (fun poly ->
      poly <: poly)

let synth_expr_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:50
    ~name:"synth_expr_sound"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      simple_mono_poly simple_mono @@ fun expr_t ->
      expr <== expr_t)

let synth_type_sound_l =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:50
    ~name:"synth_type_sound_l"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      simple_mono_poly simple_mono @@ fun left ->
      expr ==> fun right ->
      left <: right)

let synth_type_sound_r =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:50
    ~name:"synth_type_sound_r"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      simple_mono_poly simple_mono @@ fun right ->
      expr ==> fun left ->
      left <: right)

let check_type_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:50
    ~name:"check_type_sound"
    (arbitrary_typed_expr ctx)
    (fun (expr, _simple_mono) ->
      expr ==> fun expr_t ->
      expr <== expr_t)

let interp_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:50
    ~name:"interp_sound"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      simple_mono_poly simple_mono @@ fun expr_t ->
      (interp expr) <== expr_t)

let suite =
  [ subtype_id_sound
  ; synth_expr_sound
  ; synth_type_sound_l
  ; synth_type_sound_r
  ; check_type_sound
  ; interp_sound
  ]
