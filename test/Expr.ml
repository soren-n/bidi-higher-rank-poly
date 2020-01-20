open Back
open Syntax
open Mono
open Poly

(* Expr *)
let rec _gen_expr n ctx ps =
  let open QCheck.Gen in
  let _gen_expr_term =
    if (List.length ps) <= 0 then
      frequency
      [ 1, return expr_bot
      ; 2, return expr_unit
      ]
    else
      frequency
      [ 1, return expr_bot
      ; 2, return expr_unit
      ; 2, map expr_var (oneofl ps)
      ]
  in
  let _gen_expr_abs st =
    Naming.sample_label ctx @@ fun param ->
    map (expr_abs param)
      (_gen_expr (n - 1) ctx (param :: ps)) st
  in
  if n = 0 then _gen_expr_term else
  frequency
  [ 1, _gen_expr_term
  ; 1, _gen_expr_abs
  ; 2, map2 expr_app
    (_gen_expr (n / 2) ctx ps)
    (_gen_expr (n / 2) ctx ps)
  ]

let gen_expr ctx =
  let open QCheck.Gen in
  let ps = [] in
  nat >>= fun n ->
  _gen_expr n ctx ps

let print_expr ctx expr =
  Print.print_expr ctx expr (fun x -> x)

let rec shrink_expr expr =
  let open QCheck.Iter in
  match expr with
  | EBot -> empty
  | EUnit -> empty
  | EVar _name -> empty
  | EAbs (param, body) ->
    shrink_expr body >|= fun body1 -> expr_abs param body1
  | EApp (func, arg) ->
    of_list [func; arg]
    <+> (shrink_expr func >|= fun func1 -> expr_app func1 arg)
    <+> (shrink_expr arg >|= fun arg1 -> expr_app func arg1)
  | EAnno (expr1, poly) ->
    return expr1
    <+> (shrink_expr expr1 >|= fun expr2 -> expr_anno expr2 poly)
    <+> (shrink_poly poly >|= fun poly1 -> expr_anno expr poly1)

let arbitrary_expr ctx =
  QCheck.make (gen_expr ctx)
    ~print: (print_expr ctx)
    ~shrink: shrink_expr

(* Typed Expr *)
let _synth_expr_empty = []

let _synth_expr_bind simple expr env return =
  return ((simple, expr) :: env)

let _synth_expr_lookup simple env fail return =
  let rec _visit env result =
    match env with
    | [] ->
      if (List.length result) <= 0
      then fail ()
      else return result
    | (key, expr) :: env1 ->
      if proper_simple_mono_equal simple key
      then _visit env1 (expr :: result)
      else _visit env1 result
  in
  _visit env []

let rec _synth_expr n ctx env simple_mono =
  let open QCheck.Gen in
  match simple_mono with
  | SMBot -> return expr_bot
  | SMProper proper_simple_mono ->
    _synth_expr_proper n ctx env proper_simple_mono
and _synth_expr_proper n ctx env proper_simple_mono =
  match proper_simple_mono with
  | SMUnit -> _synth_expr_unit n ctx env
  | SMVar exist -> _synth_expr_var n ctx env exist
  | SMArrow (dom, codom) -> _synth_expr_arrow n ctx env dom codom
and _synth_expr_unit n ctx env =
  let open QCheck.Gen in
  if n = 0 then _synth_expr_unit_term env else
  frequency
  [ 1, _synth_expr_unit_term env
  ; 2, _synth_expr_redex (n / 2) ctx env proper_simple_mono_unit
  ]
and _synth_expr_var n ctx env exist =
  let open QCheck.Gen in
  _synth_expr_lookup (proper_simple_mono_var exist) env
    (fun () ->
      match !exist with
      | None -> assert false
      | Some proper_simple_mono ->
        _synth_expr_proper n ctx env proper_simple_mono)
    (fun instances ->
      match instances with
      | [] -> assert false
      | var :: _ ->
        return var)
and _synth_expr_unit_term env =
  let open QCheck.Gen in
  _synth_expr_lookup proper_simple_mono_unit env
    (fun () -> return expr_unit)
    (fun instances ->
      let m = List.length instances in
      frequency
      [ 1, return expr_unit
      ; m, oneofl instances
      ])
and _synth_expr_arrow n ctx env dom codom =
  let open QCheck.Gen in
  Naming.sample_label ctx @@ fun param ->
  _synth_expr_bind dom (expr_var param) env @@ fun env1 ->
  _synth_expr_proper n ctx env1 codom >>= fun body ->
  return (expr_abs param body)
and _synth_expr_redex n ctx env codom =
  let open QCheck.Gen in
  Naming.sample_label ctx @@ fun param ->
  gen_proper_simple_mono >>= fun dom ->
  _synth_expr_proper n ctx env dom >>= fun arg ->
  _synth_expr_bind dom (expr_var param) env @@ fun env1 ->
  _synth_expr_proper n ctx env1 codom >>= fun body ->
  return (expr_app (expr_abs param body) arg)

let synth_expr ctx simple_mono =
  let open QCheck.Gen in
  nat >>= fun n ->
  _synth_expr n ctx _synth_expr_empty simple_mono

let gen_typed_expr ctx =
  let open QCheck.Gen in
  gen_simple_mono >>= fun simple_mono ->
  synth_expr ctx simple_mono >>= fun expr ->
  return (expr, simple_mono)

let print_typed_expr ctx (expr, simple_mono) =
  let open Printf in
  sprintf "%s : %s"
    (print_expr ctx expr)
    (print_simple_mono ctx simple_mono)

let shrink_typed_expr ctx (_expr, simple_mono) =
  let open QCheck.Iter in
  shrink_simple_mono simple_mono >>= fun simple_mono1 ->
  let expr1 = QCheck.Gen.generate1 (synth_expr ctx simple_mono1) in
  return (expr1, simple_mono1)

let arbitrary_typed_expr ctx =
  QCheck.make (gen_typed_expr ctx)
    ~print: (print_typed_expr ctx)
    ~shrink: (shrink_typed_expr ctx)
