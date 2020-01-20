open Printf
open Util
open Syntax

let _check_mono mono tenv fail return =
  let _fail name () =
    fail (sprintf "Unknown type parameter \"%s\"" name)
  in
  let rec _visit mono return =
    match mono with
    | MBot -> return ()
    | MUnit -> return ()
    | MParam name ->
      Set.member label_equal name tenv (_fail name) return
    | MVar exist ->
      begin match !exist with
      | None -> return ()
      | Some mono1 -> _visit mono1 return
      end
    | MArrow (dom, codom) ->
      _visit dom @@ fun () ->
      _visit codom return
  in
  _visit mono return

let check_mono mono ctx fail return =
  Context.get_tenv ctx @@ fun tenv ->
  Env.keys tenv @@ fun tenv1 ->
  _check_mono mono tenv1 fail return

let _check_poly poly tenv fail return =
  let _fail name () =
    fail (sprintf "Unknown type parameter \"%s\"" name)
  in
  let rec _visit poly tenv return =
    match poly with
    | PBot -> return ()
    | PUnit -> return ()
    | PParam name ->
      Set.member label_equal name tenv (_fail name) return
    | PVar exist ->
      begin match !exist with
      | None -> return ()
      | Some mono -> _check_mono mono tenv fail return
      end
    | PArrow (dom, codom) ->
      _visit dom tenv @@ fun () ->
      _visit codom tenv return
    | PForall (param, poly1) ->
      Set.add param tenv @@ fun tenv1 ->
      _visit poly1 tenv1 return
    | PMono mono ->
      _check_mono mono tenv fail return
  in
  _visit poly tenv return

let check_poly poly ctx fail return =
  Context.get_tenv ctx @@ fun tenv ->
  Env.keys tenv @@ fun tenv1 ->
  _check_poly poly tenv1 fail return

let _check_expr expr tenv venv fail return =
  let _fail name () =
    fail (sprintf "Unknown program parameter \"%s\"" name)
  in
  let rec _visit expr venv return =
    match expr with
    | EUndefined -> return ()
    | EUnit -> return ()
    | EVar name ->
      Set.member label_equal name venv (_fail name) return
    | EAbs (param, body) ->
      Set.add param venv @@ fun venv1 ->
      _visit body venv1 return
    | EApp (func, arg) ->
      _visit func venv @@ fun () ->
      _visit arg venv return
    | EAnno (expr1, poly) ->
      _visit expr1 venv @@ fun () ->
      _check_poly poly tenv fail return
  in
  _visit expr venv return

let check_expr expr ctx fail return =
  Context.get_tenv ctx @@ fun tenv ->
  Context.get_venv ctx @@ fun venv ->
  Env.keys tenv @@ fun tenv1 ->
  Env.keys venv @@ fun venv1 ->
  _check_expr expr tenv1 venv1 fail return
