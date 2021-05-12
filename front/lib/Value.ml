open Util
open Extra
open Back
open Syntax

type value =
  | VUndefined
  | VUnit
  | VBit of bytes
  | VClo of (label, value) Env.env * label * stmt
  | VProc of label * int * proc * expr list

let value_2_expr value return =
  let rec _eval value return =
    match value with
    | VUndefined -> return expr_undefined
    | VUnit -> return expr_unit
    | VBit value -> return (expr_bit value)
    | VClo (env, param, body) ->
      _normalize_stmt body env @@ fun body1 ->
      return (expr_abs param body1)
    | VProc (name, arity, proc, args) ->
      List.fold
        (fun return ->
          return (expr_proc name arity proc))
        (fun arg visit_args return ->
          visit_args @@ fun func ->
          return (expr_app func arg))
        args return
  and _normalize_expr expr env return =
    match expr with
    | EUndefined -> return expr_undefined
    | EUnit -> return expr_unit
    | EBit value -> return (expr_bit value)
    | EVar label ->
      Env.lookup label_equal label env
        (fun () -> return (expr_var label))
        (fun value -> _eval value return)
    | EAbs (param, body) ->
      _normalize_stmt body env @@ fun body1 ->
      return (expr_abs param body1)
    | EApp (func, arg) ->
      _normalize_expr func env @@ fun func1 ->
      _normalize_expr arg env @@ fun arg1 ->
      return (expr_app func1 arg1)
    | EAnno (expr1, poly) ->
      _normalize_expr expr1 env @@ fun expr2 ->
      return (expr_anno expr2 poly)
    | EProc (name, arity, proc) ->
      return (expr_proc name arity proc)
  and _normalize_stmt stmt env return =
    match stmt with
    | SDecl (name, poly, stmt1) ->
      _normalize_stmt stmt1 env @@ fun stmt2 ->
      return (stmt_decl name poly stmt2)
    | SDefn (name, expr, stmt1) ->
      _normalize_expr expr env @@ fun expr1 ->
      _normalize_stmt stmt1 env @@ fun stmt2 ->
      return (stmt_defn name expr1 stmt2)
    | SExpr expr ->
      _normalize_expr expr env @@ fun expr1 ->
      return (stmt_expr expr1)
  in
  _eval value return

let print_value value return =
  match value with
  | VUndefined -> return "undefined"
  | VUnit -> return "unit"
  | VBit value -> return (bytes_2_binary value)
  | VClo _ -> return "<closure>"
  | VProc (name, _arity, _proc, _args) ->
    return ("<procedure \"" ^ name ^ "\">")

let prepare env return =
  let _undefined = VUndefined in
  let _unit = VUnit in
  let _bit value = VBit value in
  let _closure env param body = VClo (env, param, body) in
  let _procedure name arity proc = VProc (name, arity, proc, []) in
  let _convert expr return =
    match expr with
    | EUndefined -> return _undefined
    | EUnit -> return _unit
    | EBit value -> return (_bit value)
    | EAbs (param, body) -> return (_closure Env.empty param body)
    | EProc (name, arity, proc) -> return (_procedure name arity proc)
    | _ -> assert false (* Typing invariant *)
  in
  Env.fold
    (fun return -> return Env.empty)
    (fun label expr visit_env return ->
      _convert expr @@ fun value ->
      visit_env @@ fun env1 ->
      Env.bind label value env1 return)
    env return
