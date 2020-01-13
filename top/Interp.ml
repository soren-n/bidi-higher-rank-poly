open Util
open Bin
open Syntax

let eval expr env return =
  let _equal l r = l = r in
  let rec _visit expr env return =
    match expr with
    | EVar name ->
      Env.lookup _equal name env
        (fun () -> assert false (* Syntax invariant *))
        return
    | EApp (func, arg) ->
      _visit func env @@ fun func1 ->
      begin match func1 with
      | EAbs (param, body) ->
        _visit arg env @@ fun arg1 ->
        Env.update param arg1 env @@ fun env1 ->
        _visit body env1 return
      | _ -> assert false (* Type invariant *)
      end
    | EAnno (expr, _poly) -> _visit expr env return
    | EUnit | EAbs _ -> return expr
  in
  _visit expr env return
