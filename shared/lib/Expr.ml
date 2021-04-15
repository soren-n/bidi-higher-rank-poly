open Util
open Extra
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
      [ 1, return expr_undefined
      ; 2, return expr_unit
      ]
    else
      frequency
      [ 1, return expr_undefined
      ; 2, return expr_unit
      ; 2, map expr_var (oneofl ps)
      ]
  in
  let _gen_expr_abs st =
    Naming.sample_label ctx @@ fun param ->
    map (expr_abs param)
      (_gen_stmt (n - 1) ctx (param :: ps)) st
  in
  let _gen_expr_app st =
    map2 expr_app
      (_gen_expr (n / 2) ctx ps)
      (_gen_expr (n / 2) ctx ps)
      st
  in
  if n = 0 then _gen_expr_term else
  frequency
  [ 1, _gen_expr_term
  ; 1, _gen_expr_abs
  ; 2, _gen_expr_app
  ]
and _gen_stmt n ctx ps =
  let open QCheck.Gen in
  let _gen_stmt_defn_name name =
    map2 (stmt_defn name)
      (_gen_expr (n / 2) ctx ps)
      (_gen_stmt (n / 2) ctx (name :: ps))
  in
  let _gen_stmt_defn st =
    Naming.sample_label ctx @@ fun name ->
    _gen_stmt_defn_name name st
  in
  let _gen_stmt_decl st =
    let vs = ref [] in
    Naming.sample_label ctx @@ fun name ->
    map2 (stmt_decl name)
      (_gen_poly (n / 2) ctx ps vs)
      (_gen_stmt_defn_name name)
      st
  in
  let _gen_stmt_expr = map (stmt_expr) (_gen_expr n ctx ps) in
  if n = 0 then _gen_stmt_expr else
  frequency
  [ 1, _gen_stmt_expr
  ; 2, _gen_stmt_decl
  ; 2, _gen_stmt_defn
  ]

let gen_expr ctx =
  let open QCheck.Gen in
  let ps = [] in
  nat >>= fun n ->
  _gen_expr n ctx ps

let gen_stmt ctx =
  let open QCheck.Gen in
  let ps = [] in
  nat >>= fun n ->
  _gen_stmt n ctx ps

let print_expr ctx expr =
  Print.print_expr ctx expr (fun x -> x)

let print_stmt ctx stmt =
  Print.print_stmt ctx stmt (fun x -> x)

let rec shrink_expr expr =
  let open QCheck.Iter in
  match expr with
  | EUndefined -> empty
  | EUnit -> empty
  | EVar _name -> empty
  | EAbs (param, body) ->
    shrink_stmt body >|= fun body1 -> expr_abs param body1
  | EApp (func, arg) ->
    of_list [func; arg]
    <+> (shrink_expr func >|= fun func1 -> expr_app func1 arg)
    <+> (shrink_expr arg >|= fun arg1 -> expr_app func arg1)
  | EAnno (expr1, poly) ->
    return expr1
    <+> (shrink_expr expr1 >|= fun expr2 -> expr_anno expr2 poly)
    <+> (shrink_poly poly >|= fun poly1 -> expr_anno expr poly1)
and shrink_stmt stmt =
  let open QCheck.Iter in
  match stmt with
  | SDecl (name, poly, stmt1) ->
    return stmt1
    <+> (shrink_stmt stmt1 >|= fun stmt2 -> stmt_decl name poly stmt2)
    <+> (shrink_poly poly >|= fun poly1 -> stmt_decl name poly1 stmt1)
  | SDefn (name, expr, stmt1) ->
    return stmt1
    <+> (shrink_stmt stmt1 >|= fun stmt2 -> stmt_defn name expr stmt2)
    <+> (shrink_expr expr >|= fun expr1 -> stmt_defn name expr1 stmt1)
  | SExpr expr ->
    shrink_expr expr >|= fun expr1 -> stmt_expr expr1

let arbitrary_expr ctx =
  QCheck.make (gen_expr ctx)
    ~print: (print_expr ctx)
    ~shrink: shrink_expr

let arbitrary_stmt ctx =
  QCheck.make (gen_stmt ctx)
    ~print: (print_stmt ctx)
    ~shrink: shrink_stmt

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
  | SMNothing -> return expr_undefined
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
      | None -> assert false (* Invariant *)
      | Some proper_simple_mono ->
        _synth_expr_proper n ctx env proper_simple_mono)
    (fun instances ->
      match instances with
      | [] -> assert false (* Invariant *)
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
  _synth_stmt_proper n ctx env1 codom >>= fun body ->
  return (expr_abs param body)
and _synth_expr_redex n ctx env codom =
  let open QCheck.Gen in
  Naming.sample_label ctx @@ fun param ->
  gen_proper_simple_mono >>= fun dom ->
  _synth_expr_proper n ctx env dom >>= fun arg ->
  _synth_expr_bind dom (expr_var param) env @@ fun env1 ->
  _synth_stmt_proper n ctx env1 codom >>= fun body ->
  return (expr_app (expr_abs param body) arg)
and _synth_stmt n ctx env simple_mono =
  let open QCheck.Gen in
  match simple_mono with
  | SMNothing ->
    return (stmt_expr expr_undefined)
  | SMProper proper_simple_mono ->
    _synth_stmt_proper n ctx env proper_simple_mono
and _synth_stmt_proper n ctx env proper_simple_mono =
  let open QCheck.Gen in
  if n = 0 then _synth_stmt_expr n ctx env proper_simple_mono else
  frequency
  [ 1, _synth_stmt_expr n ctx env proper_simple_mono
  ; 2, _synth_stmt_decl n ctx env proper_simple_mono
  ; 2, _synth_stmt_defn n ctx env proper_simple_mono
  ]
and _synth_stmt_expr n ctx env proper_simple_mono =
  let open QCheck.Gen in
  _synth_expr_proper n ctx env proper_simple_mono >>= fun expr ->
  return (stmt_expr expr)
and _synth_stmt_decl n ctx env proper_simple_mono st =
  let open QCheck.Gen in
  (Naming.sample_label ctx @@ fun name ->
  gen_proper_simple_mono >>= fun proto ->
  let env2 =
    match proto with
    | SMArrow _ ->
      _synth_expr_bind proto (expr_var name) env @@ fun env1 ->
      env1
    | _ -> env
  in
  proper_simple_mono_2_proper_simple_poly proto @@ fun poly ->
  map (stmt_decl name poly)
    (_synth_stmt_defn_name name proto n ctx env2 proper_simple_mono))
    st
and _synth_stmt_defn n ctx env proper_simple_mono st =
  let open QCheck.Gen in
  Naming.sample_label ctx @@ fun name ->
  (gen_proper_simple_mono >>= fun proto ->
  _synth_stmt_defn_name name proto n ctx env proper_simple_mono) st
and _synth_stmt_defn_name name proto n ctx env proper_simple_mono =
  let open QCheck.Gen in
  map2 (stmt_defn name)
    (_synth_expr_proper (n / 2) ctx env proto)
    (_synth_stmt_proper (n / 2) ctx env proper_simple_mono)

let synth_expr ctx simple_mono =
  let open QCheck.Gen in
  nat >>= fun n ->
  _synth_expr n ctx _synth_expr_empty simple_mono

let synth_stmt ctx simple_mono =
  let open QCheck.Gen in
  nat >>= fun n ->
  _synth_stmt n ctx _synth_expr_empty simple_mono

let gen_typed_expr ctx =
  let open QCheck.Gen in
  gen_simple_mono >>= fun simple_mono ->
  synth_expr ctx simple_mono >>= fun expr ->
  return (expr, simple_mono)

let gen_typed_stmt ctx =
  let open QCheck.Gen in
  gen_simple_mono >>= fun simple_mono ->
  synth_stmt ctx simple_mono >>= fun stmt ->
  return (stmt, simple_mono)

let print_typed_expr ctx (expr, simple_mono) =
  let open Printf in
  sprintf "%s : %s"
    (print_expr ctx expr)
    (print_simple_mono ctx simple_mono)

let print_typed_stmt ctx (stmt, simple_mono) =
  let open Printf in
  sprintf "%s : %s"
    (print_stmt ctx stmt)
    (print_simple_mono ctx simple_mono)

let stmt_2_expr env stmt return =
  let rec _visit_stmt_drop env stmt return =
    match stmt with
    | SDecl (_name, _poly, stmt1) ->
      _visit_stmt_drop env stmt1 return
    | SDefn (name, expr, stmt1) ->
      _visit_expr env expr @@ fun expr1 ->
      Env.bind name expr1 env @@ fun env1 ->
      _visit_stmt_drop env1 stmt1 return
    | SExpr expr ->
      _visit_expr env expr return
  and _visit_stmt_remain env stmt return =
    match stmt with
    | SDecl (name, poly, stmt1) ->
      _visit_stmt_remain env stmt1 @@ fun stmt2 ->
      return (stmt_decl name poly stmt2)
    | SDefn (name, expr, stmt1) ->
      _visit_expr env expr @@ fun expr1 ->
      _visit_stmt_remain env stmt1 @@ fun stmt2 ->
      return (stmt_defn name expr1 stmt2)
    | SExpr expr ->
      _visit_expr env expr @@ fun expr1 ->
      return (stmt_expr expr1)
  and _visit_expr env expr return =
    match expr with
    | EUndefined -> return expr_undefined
    | EUnit -> return expr_unit
    | EVar name ->
      Env.lookup label_equal name env
        (fun () -> return (expr_var name))
        (fun expr -> return expr)
    | EAbs (param, body) ->
      _visit_stmt_remain env body @@ fun body1 ->
      return (expr_abs param body1)
    | EApp (func, arg) ->
      _visit_expr env func @@ fun func1 ->
      _visit_expr env arg @@ fun arg1 ->
      return (expr_app func1 arg1)
    | EAnno (expr1, poly) ->
      _visit_expr env expr1 @@ fun expr2 ->
      return (expr_anno expr2 poly)
  in
  _visit_stmt_drop env stmt return

let rec label_ref_count_stmt label stmt return =
  match stmt with
  | SDecl (name, _poly, stmt1) ->
    if label_equal label name then return 0 else
    label_ref_count_stmt label stmt1 return
  | SDefn (name, expr, stmt1) ->
    label_ref_count_expr label expr @@ fun expr_count ->
    if label_equal label name then return expr_count else
    label_ref_count_stmt label stmt1 @@ fun stmt1_count ->
    return (expr_count + stmt1_count)
  | SExpr expr ->
    label_ref_count_expr label expr return
and label_ref_count_expr label expr return =
  match expr with
  | EUndefined -> return 0
  | EUnit -> return 0
  | EVar name ->
    if label_equal label name
    then return 1
    else return 0
  | EAbs (param, body) ->
    if label_equal label param then return 0 else
    label_ref_count_stmt label body return
  | EApp (func, arg) ->
    label_ref_count_expr label func @@ fun func_count ->
    label_ref_count_expr label arg @@ fun arg_count ->
    return (func_count + arg_count)
  | EAnno (expr1, _poly) ->
    label_ref_count_expr label expr1 return

let rec subst_stmt label subst stmt return =
  match stmt with
  | SDecl (name, poly, stmt1) ->
    if label_equal label name then return stmt else
    subst_stmt label subst stmt1 @@ fun stmt2 ->
    return (stmt_decl name poly stmt2)
  | SDefn (name, expr, stmt1) ->
    if label_equal label name then return stmt else
    subst_expr label subst expr @@ fun expr1 ->
    subst_stmt label subst stmt1 @@ fun stmt2 ->
    return (stmt_defn name expr1 stmt2)
  | SExpr expr ->
    subst_expr label subst expr @@ fun expr1 ->
    return (stmt_expr expr1)
and subst_expr label subst expr return =
  match expr with
  | EUndefined | EUnit -> return expr
  | EVar name ->
    if label_equal label name
    then return subst
    else return expr
  | EAbs (param, body) ->
    if label_equal label param then return expr else
    subst_stmt label subst body @@ fun body1 ->
    return (expr_abs param body1)
  | EApp (func, arg) ->
    subst_expr label subst func @@ fun func1 ->
    subst_expr label subst arg @@ fun arg1 ->
    return (expr_app func1 arg1)
  | EAnno (expr1, poly) ->
    subst_expr label subst expr1 @@ fun expr2 ->
    return (expr_anno expr2 poly)

let rec type_directed_shrink_stmt env stmt yield =
  match stmt with
  | SDecl (name, poly, stmt1) ->
    type_directed_shrink_stmt env stmt1
      (fun stmt2 -> yield (stmt_decl name poly stmt2));
    label_ref_count_stmt name stmt1 @@ fun stmt_count ->
    begin match stmt_count with
    | 0 -> yield stmt1
    | _ -> ()
    end
  | SDefn (name, expr, stmt1) ->
    let scope = Env.empty in
    Env.bind name () scope @@ fun scope1 ->
    type_directed_shrink_expr env scope1 expr
      (fun expr1 -> yield (stmt_defn name expr1 stmt1));
    type_directed_shrink_stmt env stmt1
      (fun stmt2 -> yield (stmt_defn name expr stmt2));
    label_ref_count_expr name expr @@ fun expr_count ->
    label_ref_count_stmt name stmt1 @@ fun stmt_count ->
    begin match expr_count, stmt_count with
    | 0, 1 -> subst_stmt name expr stmt1 yield
    | _, 0 -> yield stmt1
    | _, _ -> ()
    end
  | SExpr expr ->
    let scope = Env.empty in
    type_directed_shrink_expr env scope expr @@ fun expr1 ->
    yield (stmt_expr expr1)
and type_directed_shrink_expr env scope expr yield =
  match expr with
  | EUndefined -> ()
  | EUnit -> ()
  | EVar name ->
    Env.lookup label_equal name scope
      (fun () ->
        Env.lookup label_equal name env identity @@ fun expr1 ->
        Env.bind name () scope @@ fun scope1 ->
        type_directed_shrink_expr env scope1 expr1 yield)
      (fun () -> ())
  | EAbs (param, body) ->
    type_directed_shrink_stmt env body
      (fun body1 -> yield (expr_abs param body1))
  | EApp (func, arg) ->
    type_directed_shrink_expr env scope func
      (fun func1 -> yield (expr_app func1 arg));
    type_directed_shrink_expr env scope arg
      (fun arg1 -> yield (expr_app func arg1));
    begin match func, arg with
    | EAbs (param, SExpr (EVar arg)), _ ->
      if label_equal param arg then () else
      yield (expr_var arg)
    | EAbs (_param, SExpr EUndefined), _ -> yield expr_undefined
    | EAbs (_param, SExpr EUnit), _ -> yield expr_unit
    | EAbs _, EUndefined -> yield expr_undefined
    | EAbs (param, body), EUnit
    | EAbs (param, body), EAbs _ ->
      Env.bind param arg env @@ fun env1 ->
      type_directed_shrink_stmt env1 body
        (fun body1 -> stmt_2_expr env1 body1 yield)
    | _, _ -> ()
    end
  | EAnno (expr1, poly) ->
    type_directed_shrink_expr env scope expr1
      (fun expr2 -> yield (expr_anno expr2 poly));
    yield expr1

let shrink_typed_expr (expr, simple_mono) =
  let open QCheck.Iter in
  let env = Env.empty in
  let scope = Env.empty in
  type_directed_shrink_expr env scope expr >>= fun expr1 ->
  return (expr1, simple_mono)

let shrink_typed_stmt (stmt, simple_mono) =
  let open QCheck.Iter in
  let env = Env.empty in
  type_directed_shrink_stmt env stmt >>= fun stmt1 ->
  return (stmt1, simple_mono)

let arbitrary_typed_expr ctx =
  QCheck.make (gen_typed_expr ctx)
    ~print: (print_typed_expr ctx)
    ~shrink: shrink_typed_expr

let arbitrary_typed_stmt ctx =
  QCheck.make (gen_typed_stmt ctx)
    ~print: (print_typed_stmt ctx)
    ~shrink: shrink_typed_stmt
