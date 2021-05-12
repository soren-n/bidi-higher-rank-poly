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
    | MBit _size -> return ()
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
    fail (~$"Unbound type parameter" <+> ~$"\"" <!&> ~$name <!&> ~$"\"")
  in
  let rec _visit poly tenv return =
    match poly with
    | PNothing -> return ()
    | PUnit -> return ()
    | PBit _size -> return ()
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

let _poly_arity poly return =
  let rec _visit_poly poly return =
    match poly with
    | PVar exist ->
      begin match !exist with
      | None -> return 0
      | Some mono -> _visit_mono mono return
      end
    | PArrow (_dom, codom) ->
      _visit_poly codom @@ fun arity ->
      return (arity + 1)
    | PForall (_param, poly1) ->
      _visit_poly poly1 return
    | PMono mono ->
      _visit_mono mono return
    | _ -> return 0
  and _visit_mono mono return =
    match mono with
    | MVar exist ->
      begin match !exist with
      | None -> return 0
      | Some mono -> _visit_mono mono return
      end
    | MArrow (_dom, codom) ->
      _visit_mono codom @@ fun arity ->
      return (arity + 1)
    | _ -> return 0
  in
  _visit_poly poly return

let rec _check_expr expr tnames vnames venv fail return =
  let _fail name =
    fail (~$"Unbound program parameter" <+> ~$"\"" <!&> ~$name <!&> ~$"\"")
  in
  let _lookup = Env.lookup label_equal in
  match expr with
  | EUndefined | EUnit -> return ()
  | EBit _value -> return ()
  | EVar name ->
    if Set.is_member label_order name vnames
    then return ()
    else _fail name
  | EAbs (param, body) ->
    let vnames1 = Set.add label_order param vnames in
    _check_stmt body tnames vnames1 venv Env.empty fail return
  | EApp (func, arg) ->
    _check_expr func tnames vnames venv fail @@ fun () ->
    _check_expr arg tnames vnames venv fail return
  | EAnno (expr1, poly) ->
    _check_expr expr1 tnames vnames venv fail @@ fun () ->
    _check_poly poly tnames fail return
  | EProc (name, expected_arity, _proc) ->
    _lookup name venv
      (fun () -> _fail name)
      (fun poly ->
        _poly_arity poly @@ fun actual_arity ->
        if expected_arity = actual_arity
        then return ()
        else _fail name)
and _check_stmt stmt tnames vnames venv decls fail return =
  match stmt with
  | SDecl (name, poly, stmt1) ->
    if Set.is_member label_order name vnames
    then fail (~$name <+> ~$"was redeclared") else
    _check_poly poly tnames fail @@ fun () ->
    let decl = ref false in
    Env.bind name decl decls @@ fun decls1 ->
    let vnames1 = Set.add label_order name vnames in
    _check_stmt stmt1 tnames vnames1 venv decls1 fail @@ fun () ->
    if !decl then return () else
    fail (~$name <+> ~$"was declared but not defined")
  | SDefn (name, expr, stmt1) ->
    _check_expr expr tnames vnames venv fail @@ fun () ->
    let vnames1 = Set.add label_order name vnames in
    Env.lookup label_equal name decls ignore (fun decl -> decl := true);
    _check_stmt stmt1 tnames vnames1 venv decls fail return
  | SExpr expr ->
    _check_expr expr tnames vnames venv fail return

let check_expr expr tctx fail return =
  Context.get_tenv tctx @@ fun tenv ->
  Context.get_venv tctx @@ fun venv ->
  Env.keys label_order tenv @@ fun tnames ->
  Env.keys label_order venv @@ fun vnames ->
  _check_expr expr tnames vnames venv fail return

let check_stmt stmt tctx fail return =
  Context.get_tenv tctx @@ fun tenv ->
  Context.get_venv tctx @@ fun venv ->
  Env.keys label_order tenv @@ fun tenv1 ->
  Env.keys label_order venv @@ fun venv1 ->
  _check_stmt stmt tenv1 venv1 venv Env.empty fail return

let rec _check_prog prog tnames vnames venv decls fail return =
  match prog with
  | PDecl (name, poly, prog1) ->
    if Set.is_member label_order name vnames
    then fail (~$name <+> ~$"was redeclared") else
    _check_poly poly tnames fail @@ fun () ->
    let decl = ref false in
    Env.bind name decl decls @@ fun decls1 ->
    let vnames1 = Set.add label_order name vnames in
    _check_prog prog1 tnames vnames1 venv decls1 fail @@ fun () ->
    if !decl then return () else
    fail (~$name <+> ~$"was declared but not defined")
  | PDefn (name, expr, prog1) ->
    _check_expr expr tnames vnames venv fail @@ fun () ->
    let vnames1 = Set.add label_order name vnames in
    Env.lookup label_equal name decls ignore (fun decl -> decl := true);
    _check_prog prog1 tnames vnames1 venv decls fail return
  | PEnd -> return ()

let check_prog prog tctx fail return =
  Context.get_tenv tctx @@ fun tenv ->
  Context.get_venv tctx @@ fun venv ->
  Env.keys label_order tenv @@ fun tenv1 ->
  Env.keys label_order venv @@ fun venv1 ->
  _check_prog prog tenv1 venv1 venv Env.empty fail return
