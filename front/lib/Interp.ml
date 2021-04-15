open Util
open Back
open Syntax
open Value

let _fail () = assert false (* Syntax invariant *)

let rec eval_expr expr env return =
  let _undefined = VUndefined in
  let _unit = VUnit in
  let _closure env param body = VClo (env, param, body) in
  match expr with
  | EUndefined -> return _undefined
  | EUnit -> return _unit
  | EVar name ->
    Env.lookup label_equal name env _fail return
  | EAbs (param, body) ->
    return (_closure env param body)
  | EApp (func, arg) ->
    eval_expr func env @@ fun func1 ->
    begin match func1 with
    | VClo (env1, param, body) ->
      eval_expr arg env @@ fun arg1 ->
      Env.bind param arg1 env1 @@ fun env2 ->
      eval_stmt body env2 return
    | _ -> assert false (* Typing invariant *)
    end
  | EAnno (expr, _poly) ->
    eval_expr expr env return
and eval_stmt stmt env return =
  match stmt with
  | SDecl (_, _, stmt1) -> eval_stmt stmt1 env return
  | SDefn (name, expr, stmt1) ->
    eval_expr expr env @@ fun expr1 ->
    Env.bind name expr1 env @@ fun env1 ->
    eval_stmt stmt1 env1 return
  | SExpr expr ->
    eval_expr expr env return

let rec _eval_prog prog env return =
  match prog with
  | PDecl (_, _, prog1) -> _eval_prog prog1 env return
  | PDefn (name, expr, prog1) ->
    eval_expr expr env @@ fun expr1 ->
    Env.bind name expr1 env @@ fun env1 ->
    _eval_prog prog1 env1 return
  | PEnd -> return env

let eval_prog prog env return =
  _eval_prog prog env @@ fun env1 ->
  eval_expr (expr_app (expr_var "main") expr_unit) env1 @@ fun _result ->
  return ()
