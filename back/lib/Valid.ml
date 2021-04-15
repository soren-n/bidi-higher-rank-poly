open Util
open Typeset
open Syntax

let _check_mono mono tenv fail return =
  let _fail name =
    fail (~$"Unknown type parameter" <+> ~$"\"" <!&> ~$name <!&> ~$"\"")
  in
  let rec _visit mono return =
    match mono with
    | MNothing -> return ()
    | MUnit -> return ()
    | MParam name ->
      if Set.is_member label_order name tenv
      then return ()
      else _fail name
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
  Env.keys label_order tenv @@ fun tenv1 ->
  _check_mono mono tenv1 fail return

let _check_poly poly tenv fail return =
  let _fail name =
    fail (~$"Unknown type parameter" <+> ~$"\"" <!&> ~$name <!&> ~$"\"")
  in
  let rec _visit poly tenv return =
    match poly with
    | PNothing -> return ()
    | PUnit -> return ()
    | PParam name ->
      if Set.is_member label_order name tenv
      then return ()
      else _fail name
    | PVar exist ->
      begin match !exist with
      | None -> return ()
      | Some mono -> _check_mono mono tenv fail return
      end
    | PArrow (dom, codom) ->
      _visit dom tenv @@ fun () ->
      _visit codom tenv return
    | PForall (param, poly1) ->
      let tenv1 = Set.add label_order param tenv in
      _visit poly1 tenv1 return
    | PMono mono ->
      _check_mono mono tenv fail return
  in
  _visit poly tenv return

let check_poly poly ctx fail return =
  Context.get_tenv ctx @@ fun tenv ->
  Env.keys label_order tenv @@ fun tenv1 ->
  _check_poly poly tenv1 fail return

let rec _check_expr expr tenv venv fail return =
  let _fail name =
    fail (~$"Unknown program parameter" <+> ~$"\"" <!&> ~$name <!&> ~$"\"")
  in
  match expr with
  | EUndefined | EUnit -> return ()
  | EVar name ->
    if Set.is_member label_order name venv
    then return ()
    else _fail name
  | EAbs (param, body) ->
    let venv1 = Set.add label_order param venv in
    _check_stmt body tenv venv1 Env.empty fail return
  | EApp (func, arg) ->
    _check_expr func tenv venv fail @@ fun () ->
    _check_expr arg tenv venv fail return
  | EAnno (expr1, poly) ->
    _check_expr expr1 tenv venv fail @@ fun () ->
    _check_poly poly tenv fail return
and _check_stmt stmt tenv venv decls fail return =
  match stmt with
  | SDecl (name, poly, stmt1) ->
    if Set.is_member label_order name venv
    then fail (~$name <+> ~$"was redeclared") else
    _check_poly poly tenv fail @@ fun () ->
    let decl = ref false in
    Env.bind name decl decls @@ fun decls1 ->
    let venv1 = Set.add label_order name venv in
    _check_stmt stmt1 tenv venv1 decls1 fail @@ fun () ->
    if !decl then return () else
    fail (~$name <+> ~$"was declared but not defined")
  | SDefn (name, expr, stmt1) ->
    _check_expr expr tenv venv fail @@ fun () ->
    let venv1 = Set.add label_order name venv in
    Env.lookup label_equal name decls ignore (fun decl -> decl := true);
    _check_stmt stmt1 tenv venv1 decls fail return
  | SExpr expr ->
    _check_expr expr tenv venv fail return

let check_expr expr tctx fail return =
  Context.get_tenv tctx @@ fun tenv ->
  Context.get_venv tctx @@ fun venv ->
  Env.keys label_order tenv @@ fun tenv1 ->
  Env.keys label_order venv @@ fun venv1 ->
  _check_expr expr tenv1 venv1 fail return

let check_stmt stmt tctx fail return =
  Context.get_tenv tctx @@ fun tenv ->
  Context.get_venv tctx @@ fun venv ->
  Env.keys label_order tenv @@ fun tenv1 ->
  Env.keys label_order venv @@ fun venv1 ->
  _check_stmt stmt tenv1 venv1 Env.empty fail return

let rec _check_prog prog tenv venv decls fail return =
  match prog with
  | PDecl (name, poly, prog1) ->
    if Set.is_member label_order name venv
    then fail (~$name <+> ~$"was redeclared") else
    _check_poly poly tenv fail @@ fun () ->
    let decl = ref false in
    Env.bind name decl decls @@ fun decls1 ->
    let venv1 = Set.add label_order name venv in
    _check_prog prog1 tenv venv1 decls1 fail @@ fun () ->
    if !decl then return () else
    fail (~$name <+> ~$"was declared but not defined")
  | PDefn (name, expr, prog1) ->
    _check_expr expr tenv venv fail @@ fun () ->
    let venv1 = Set.add label_order name venv in
    Env.lookup label_equal name decls ignore (fun decl -> decl := true);
    _check_prog prog1 tenv venv1 decls fail return
  | PEnd -> return ()

let check_prog prog tctx fail return =
  Context.get_tenv tctx @@ fun tenv ->
  Context.get_venv tctx @@ fun venv ->
  Env.keys label_order tenv @@ fun tenv1 ->
  Env.keys label_order venv @@ fun venv1 ->
  _check_prog prog tenv1 venv1 Env.empty fail return
