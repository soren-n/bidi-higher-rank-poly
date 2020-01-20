open Util
open Back
open Syntax

type value =
  | VUndefined
  | VUnit
  | VClo of (label, value) Env.env * label * expr

let value_expr value return =
  let rec _visit value return =
    match value with
    | VUndefined -> return expr_undefined
    | VUnit -> return expr_unit
    | VClo (env, param, body) ->
      _normalize body env @@ fun body1 ->
      return (expr_abs param body1)
  and _normalize expr env return =
    match expr with
    | EUndefined -> return expr_undefined
    | EUnit -> return expr_unit
    | EVar label ->
      Env.lookup label_equal label env
        (fun () -> return (expr_var label))
        (fun value -> _visit value return)
    | EAbs (param, body) ->
      _normalize body env @@ fun body1 ->
      return (expr_abs param body1)
    | EApp (func, arg) ->
      _normalize func env @@ fun func1 ->
      _normalize arg env @@ fun arg1 ->
      return (expr_app func1 arg1)
    | EAnno (expr1, poly) ->
      _normalize expr1 env @@ fun expr2 ->
      return (expr_anno expr2 poly)
  in
  _visit value return

let print_value value return =
  match value with
  | VUndefined -> return "undefined"
  | VUnit -> return "unit"
  | VClo _ -> return "<closure>"

let prepare env return =
  let _convert expr return =
    match expr with
    | EUndefined -> return VUndefined
    | EUnit -> return VUnit
    | EAbs (param, body) -> return (VClo (Env.empty, param, body))
    | _ -> assert false (* Typing invariant *)
  in
  Env.fold
    (fun return -> return Env.empty)
    (fun label expr visit_env return ->
      _convert expr @@ fun value ->
      visit_env @@ fun env1 ->
      Env.bind label value env1 return)
    env return

let eval expr env return =
  let rec _visit expr env return =
    match expr with
    | EUndefined -> return VUndefined
    | EUnit -> return VUnit
    | EVar name ->
      Env.lookup label_equal name env
        (fun () -> assert false (* Syntax invariant *))
        return
    | EAbs (param, body) ->
      return (VClo (env, param, body))
    | EApp (func, arg) ->
      _visit func env @@ fun func1 ->
      begin match func1 with
      | VClo (env1, param, body) ->
        _visit arg env @@ fun arg1 ->
        Env.bind param arg1 env1 @@ fun env2 ->
        _visit body env2 return
      | _ -> assert false (* Type invariant *)
      end
    | EAnno (expr, _poly) ->
      _visit expr env return
  in
  prepare env @@ fun env1 ->
  _visit expr env1 return
