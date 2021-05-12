open Constants
open Util
open Order

type label = string
type binary = string

let label_equal l r = l = r
let label_order l r =
  if l < r then LT else
  if l = r then EQ else
  GT

type mono =
  | MNothing
  | MUnit
  | MBit of bit_size
  | MParam of label
  | MVar of exist
  | MArrow of mono * mono
and exist = mono option ref

let exist_equal l r = l == r

let mono_nothing = MNothing
let mono_unit = MUnit
let mono_bit size = MBit size
let mono_param label = MParam label
let mono_var exist = MVar exist
let mono_arrow dom codom = MArrow (dom, codom)

type poly =
  | PNothing
  | PUnit
  | PBit of bit_size
  | PParam of label
  | PVar of exist
  | PArrow of poly * poly
  | PForall of label * poly
  | PMono of mono

let poly_nothing = PNothing
let poly_unit = PUnit
let poly_bit size = PBit size
let poly_param name = PParam name
let poly_var exist = PVar exist
let poly_arrow dom codom = PArrow (dom, codom)
let poly_forall param poly = PForall (param, poly)
let poly_mono mono = PMono mono

type expr =
  | EUndefined
  | EUnit
  | EBit of bytes
  | EVar of label
  | EAbs of label * stmt
  | EApp of expr * expr
  | EAnno of expr * poly
  | EProc of label * int * proc
and stmt =
  | SDecl of label * poly * stmt
  | SDefn of label * expr * stmt
  | SExpr of expr
and proc = expr list -> expr

let expr_undefined = EUndefined
let expr_unit = EUnit
let expr_bit value = EBit value
let expr_var name = EVar name
let expr_abs param body = EAbs (param, body)
let expr_app func arg = EApp (func, arg)
let expr_anno expr poly = EAnno (expr, poly)
let expr_proc name arity proc = EProc (name, arity, proc)

let stmt_decl name poly stmt = SDecl (name, poly, stmt)
let stmt_defn name expr stmt = SDefn (name, expr, stmt)
let stmt_expr expr = SExpr expr

type prog =
  | PDecl of label * poly * prog
  | PDefn of label * expr * prog
  | PEnd

let prog_decl name poly prog = PDecl (name, poly, prog)
let prog_defn name expr prog = PDefn (name, expr, prog)
let prog_end = PEnd

let rec _equal_expr left right env fail return =
  match left, right with
  | EUndefined, EUndefined -> return ()
  | EUnit, EUnit -> return ()
  | EBit l_value, EBit r_value ->
    if Bytes.equal l_value r_value then return () else fail ()
  | EVar label, EVar r_label ->
    Env.lookup label_equal label env fail @@ fun l_label ->
    if label_equal l_label r_label then return () else fail ()
  | EAbs (l_param, l_body), EAbs (r_param, r_body) ->
    Env.bind l_param r_param env @@ fun env1 ->
    _equal_stmt l_body r_body env1 fail return
  | EApp (l_func, l_arg), EApp (r_func, r_arg) ->
    _equal_expr l_func r_func env fail @@ fun () ->
    _equal_expr l_arg r_arg env fail return
  | EProc (l_name, l_arity, _l_proc), EProc (r_name, r_arity, _r_proc) ->
    if l_arity <> r_arity then fail () else
    if label_equal l_name r_name
    then return ()
    else fail ()
  | EAnno (left1, _), _ -> _equal_expr left1 right env fail return
  | _, EAnno (right1, _) -> _equal_expr left right1 env fail return
  | _, _ -> fail ()
and _equal_stmt left right env fail return =
  match left, right with
  | SDecl (l_label, _, left1), SDecl (r_label, _, right1) ->
    Env.bind l_label r_label env @@ fun env1 ->
    _equal_stmt left1 right1 env1 fail return
  | SDefn (l_label, l_expr, left1), SDefn (r_label, r_expr, right1) ->
    _equal_expr l_expr r_expr env fail @@ fun () ->
    Env.bind l_label r_label env @@ fun env1 ->
    _equal_stmt left1 right1 env1 fail return
  | SExpr l_expr, SExpr r_expr ->
    _equal_expr l_expr r_expr env fail return
  | _, _ -> fail ()

let expr_equal left right =
  _equal_expr left right Env.empty
    (fun () -> false)
    (fun () -> true)

let stmt_equal left right =
  _equal_stmt left right Env.empty
    (fun () -> false)
    (fun () -> true)

let rec _equal_prog left right env fail return =
  match left, right with
  | PDecl (l_label, _, left1), PDecl (r_label, _, right1) ->
    Env.bind l_label r_label env @@ fun env1 ->
    _equal_prog left1 right1 env1 fail return
  | PDefn (l_label, l_expr, left1), PDefn (r_label, r_expr, right1) ->
    _equal_expr l_expr r_expr env fail @@ fun () ->
    Env.bind l_label r_label env @@ fun env1 ->
    _equal_prog left1 right1 env1 fail return
  | PEnd, PEnd -> return ()
  | _, _ -> fail ()

let equal_prog left right =
  _equal_prog left right Env.empty
    (fun () -> false)
    (fun () -> true)
