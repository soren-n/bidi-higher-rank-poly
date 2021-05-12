open Util
open Extra
open Typeset
open Syntax

let _pass layout = layout

let _group layout =
  ~$"(" <!&> layout <!&> ~$")"

let _wrap layout =
  grp (~$"(" <!&> layout <!&> ~$")")

let _layout_mono ctx env mono wrap return =
  let rec _visit mono wrap return =
    match mono with
    | MNothing -> return ~$"nothing"
    | MUnit -> return ~$"unit"
    | MBit size ->
      begin match size with
      | Bit8 -> return ~$"bit8"
      | Bit16 -> return ~$"bit16"
      | Bit32 -> return ~$"bit32"
      | Bit64 -> return ~$"bit64"
      end
    | MParam label -> return ~$label
    | MVar exist ->
      begin match !exist with
      | Some mono1 -> _visit mono1 wrap return
      | None ->
        let _env = !env in
        Env.lookup exist_equal exist _env
          (fun () ->
            Naming.sample_exist ctx @@ fun label ->
            Env.bind exist label _env @@ fun env1 ->
            env := env1;
            return ~$label)
          (fun label -> return ~$label)
      end
    | MArrow (dom, codom) ->
      _visit dom _wrap @@ fun dom1 ->
      _visit codom _pass @@ fun codom1 ->
      return (wrap (seq (dom1 <+> ~$"->" <!+> codom1)))
  in
  _visit mono wrap return

let layout_mono ctx mono return =
  let env = ref Env.empty in
  _layout_mono ctx env mono _pass return

let print_mono ctx mono return =
  layout_mono ctx mono @@ fun layout ->
  Typeset.compile layout @@ fun document ->
  Typeset.render document 2 80 return

let _layout_poly ctx env poly wrap return =
  let rec _visit poly wrap return =
    match poly with
    | PNothing -> return ~$"nothing"
    | PUnit -> return ~$"unit"
    | PBit size ->
      begin match size with
      | Bit8 -> return ~$"bit8"
      | Bit16 -> return ~$"bit16"
      | Bit32 -> return ~$"bit32"
      | Bit64 -> return ~$"bit64"
      end
    | PParam label -> return ~$label
    | PVar exist ->
      begin match !exist with
      | Some mono -> _layout_mono ctx env mono wrap return
      | None ->
        let _env = !env in
        Env.lookup exist_equal exist _env
          (fun () ->
            Naming.sample_exist ctx @@ fun label ->
            Env.bind exist label _env @@ fun env1 ->
            env := env1;
            return ~$label)
          (fun label -> return ~$label)
      end
    | PArrow (dom, codom) ->
      _visit dom _wrap @@ fun dom1 ->
      _visit codom _pass @@ fun codom1 ->
      return (wrap (seq (dom1 <+> ~$"->" <!+> codom1)))
    | PForall (param, poly1) ->
      _visit poly1 _pass @@ fun poly2 ->
      return (wrap (~$param <!+> ~$"=>" <+> nest (seq poly2)))
    | PMono mono ->
      _layout_mono ctx env mono wrap return
  in
  _visit poly wrap return

let layout_poly ctx poly return =
  let env = ref Env.empty in
  _layout_poly ctx env poly _pass return

let print_poly ctx poly return =
  layout_poly ctx poly @@ fun layout ->
  Typeset.compile layout @@ fun document ->
  Typeset.render document 2 80 return

let rec _layout_expr ctx expr wrap return =
  match expr with
  | EUndefined -> return ~$"undefined"
  | EUnit -> return ~$"unit"
  | EBit value -> return ~$(bytes_2_binary value)
  | EVar label -> return ~$label
  | EAbs (param, body) ->
    _layout_stmt ctx body @@ fun body1 ->
    return (wrap (~$param <!+> seq (~$"=>" <+> nest body1)))
  | EApp (func, arg) ->
    _layout_expr ctx func _group @@ fun func1 ->
    _layout_expr ctx arg _group @@ fun arg1 ->
    return (wrap (func1 <!&> seq (null <+> nest arg1)))
  | EAnno (expr1, poly) ->
    _layout_expr ctx expr1 _group @@ fun expr2 ->
    let env = ref Env.empty in
    _layout_poly ctx env poly _pass @@ fun poly1 ->
    return (wrap (expr2 <!+> seq (~$":" <+> nest poly1)))
  | EProc (name, _arity, _proc) ->
    return (wrap (~$"<proc \"" <!&> ~$name <!&> ~$"\">"))
and _layout_stmt ctx stmt return =
  match stmt with
  | SDecl (label, poly, stmt1) ->
    let env = ref Env.empty in
    _layout_poly ctx env poly _pass @@ fun poly1 ->
    _layout_stmt ctx stmt1 @@ fun stmt2 ->
    return ((seq (~$label <!+> ~$":" <+> nest poly1 <!&> ~$".")) </>
      stmt2)
  | SDefn (label, expr, stmt1) ->
    _layout_expr ctx expr _group @@ fun expr1 ->
    _layout_stmt ctx stmt1 @@ fun stmt2 ->
    return ((seq (~$label <!+> ~$"=" <+> nest expr1 <!&> ~$".")) </>
      stmt2)
  | SExpr expr ->
    _layout_expr ctx expr _pass @@ fun expr1 ->
    return (grp expr1)

let layout_expr ctx expr return =
  _layout_expr ctx expr _pass return

let print_expr ctx expr return =
  layout_expr ctx expr @@ fun layout ->
  Typeset.compile layout @@ fun document ->
  Typeset.render document 2 80 return

let layout_stmt ctx stmt return =
  _layout_stmt ctx stmt return

let print_stmt ctx stmt return =
  layout_stmt ctx stmt @@ fun layout ->
  Typeset.compile layout @@ fun document ->
  Typeset.render document 2 80 return

let rec _layout_prog ctx prog return =
  match prog with
  | PDecl (name, poly, prog1) ->
    let env = ref Env.empty in
    _layout_poly ctx env poly _pass @@ fun poly1 ->
    _layout_prog ctx prog1 @@ fun prog1 ->
    return ((nest (~$name <!+> ~$":" <+> poly1) <!&> ~$".") </> prog1)
  | PDefn (name, expr, prog1) ->
    _layout_expr ctx expr _pass @@ fun expr1 ->
    _layout_prog ctx prog1 @@ fun prog1 ->
    return ((nest (~$name <!+> ~$"=" <+> expr1) <!&> ~$".") </> prog1)
  | PEnd -> return null

let layout_prog ctx prog return =
  _layout_prog ctx prog return

let print_prog ctx prog return =
  layout_prog ctx prog @@ fun layout ->
  Typeset.compile layout @@ fun document ->
  Typeset.render document 2 80 return
