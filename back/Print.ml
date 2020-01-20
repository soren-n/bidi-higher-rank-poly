open Printf
open Syntax
open Copy

let _print_mono ctx mono group return =
  let rec _visit mono group return =
    match mono with
    | MNothing -> return "⊥"
    | MUnit -> return "unit"
    | MParam name -> return name
    | MVar exist ->
      begin match !exist with
      | Some mono1 -> _visit mono1 group return
      | None ->
        Naming.sample_exist ctx @@ fun name ->
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

let print_mono ctx mono return =
  copy_mono mono @@ fun mono1 ->
  _print_mono ctx mono1 false return

let _print_poly ctx poly group return =
  let rec _visit poly group return =
    match poly with
    | PNothing -> return "⊥"
    | PUnit -> return "unit"
    | PParam name -> return name
    | PVar exist ->
      begin match !exist with
      | Some mono1 -> _print_mono ctx mono1 group return
      | None ->
        Naming.sample_exist ctx @@ fun name ->
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
      _print_mono ctx mono group return
  in
  _visit poly group return

let print_poly ctx poly return =
  copy_poly poly @@ fun poly1 ->
  _print_poly ctx poly1 false return

let _print_expr ctx expr group return =
  let rec _print expr group return =
    match expr with
    | EUndefined -> return "undefined"
    | EUnit -> return "unit"
    | EVar name -> return name
    | EAbs (param, body) ->
      _print body false @@ fun body1 ->
      if group
      then return (sprintf "(%s => %s)" param body1)
      else return (sprintf "%s => %s" param body1)
    | EApp (func, arg) ->
      _print func true @@ fun func1 ->
      _print arg false @@ fun arg1 ->
      if group
      then return (sprintf "(%s %s)" func1 arg1)
      else return (sprintf "%s %s" func1 arg1)
    | EAnno (expr1, poly) ->
      _print expr1 true @@ fun expr2 ->
      print_poly ctx poly @@ fun poly1 ->
      if group
      then return (sprintf "(%s : %s)" expr2 poly1)
      else return (sprintf "%s : %s" expr2 poly1)
  in
  _print expr group return

let print_expr ctx expr return =
  _print_expr ctx expr false return
