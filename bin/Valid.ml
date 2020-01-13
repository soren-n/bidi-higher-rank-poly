open Printf
open Util
open Syntax

let valid expr fail return =
  let _equal l r = l = r in
  let rec _visit expr ctx return =
    match expr with
    | EUnit -> return ()
    | EVar name ->
      Set.member _equal name ctx
        (fun () -> fail (sprintf "Unknown variable %s" name))
        return
    | EAbs (param, body) ->
      Set.add param ctx @@ fun ctx1 ->
      _visit body ctx1 return
    | EApp (func, arg) ->
      _visit func ctx @@ fun () ->
      _visit arg ctx return
    | EAnno (expr1, _poly) ->
      _visit expr1 ctx return
  in
  _visit expr Set.empty return
