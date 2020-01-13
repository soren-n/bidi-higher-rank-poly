open Printf
open Syntax
open Copy

let _print_mono mono group ctx return =
  let rec _visit mono group return =
    match mono with
    | MUnit -> return "unit"
    | MParam name -> return name
    | MVar exist ->
      begin match !exist with
      | Some mono1 -> _visit mono1 group return
      | None ->
        let name_gen = Gen.make_exist ctx in
        let name = Gen.sample_var name_gen in
        exist := Some (mono_param name);
        return name
      end
    | MArrow (dom, codom) ->
      _visit dom true @@ fun dom1 ->
      _visit codom false @@ fun codom1 ->
      if group
      then return (sprintf "(%s → %s)" dom1 codom1)
      else return (sprintf "%s → %s" dom1 codom1)
  in
  _visit mono group return

let print_mono mono return =
  let ctx = Gen.make_gen () in
  copy_mono mono @@ fun mono1 ->
  _print_mono mono1 false ctx return

let _print_poly poly group ctx return =
  let rec _visit poly group return =
    match poly with
    | PUnit -> return "unit"
    | PParam name -> return name
    | PVar exist ->
      begin match !exist with
      | Some mono1 -> _print_mono mono1 group ctx return
      | None ->
        let name_gen = Gen.make_exist ctx in
        let name = Gen.sample_var name_gen in
        exist := Some (mono_param name);
        return name
      end
    | PArrow (dom, codom) ->
      _visit dom true @@ fun dom1 ->
      _visit codom false @@ fun codom1 ->
      if group
      then return (sprintf "(%s → %s)" dom1 codom1)
      else return (sprintf "%s → %s" dom1 codom1)
    | PForall (param, poly1) ->
      _visit poly1 false @@ fun poly2 ->
      if group
      then return (sprintf "(∀%s.%s)" param poly2)
      else return (sprintf "∀%s.%s" param poly2)
    | PMono mono ->
      _print_mono mono group ctx return
  in
  _visit poly group return

let print_poly poly return =
  let ctx = Gen.make_gen () in
  copy_poly poly @@ fun poly1 ->
  _print_poly poly1 false ctx return

let rec _print_expr expr group return =
  match expr with
  | EUnit -> return "unit"
  | EVar name -> return name
  | EAbs (param, body) ->
    _print_expr body false @@ fun body1 ->
    if group
    then return (sprintf "(%s => %s)" param body1)
    else return (sprintf "%s => %s" param body1)
  | EApp (func, arg) ->
    _print_expr func true @@ fun func1 ->
    _print_expr arg false @@ fun arg1 ->
    if group
    then return (sprintf "(%s %s)" func1 arg1)
    else return (sprintf "%s %s" func1 arg1)
  | EAnno (expr1, poly) ->
    _print_expr expr1 true @@ fun expr2 ->
    print_poly poly @@ fun poly1 ->
    if group
    then return (sprintf "(%s : %s)" expr2 poly1)
    else return (sprintf "%s : %s" expr2 poly1)

let print_expr expr return =
  _print_expr expr false return
