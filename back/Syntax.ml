type label = string

let label_equal l r = l = r

type mono =
  | MBot
  | MUnit
  | MParam of label
  | MVar of exist
  | MArrow of mono * mono
and exist = mono option ref

let exist_equal l r = l == r

let mono_bot = MBot
let mono_unit = MUnit
let mono_param label = MParam label
let mono_var exist = MVar exist
let mono_arrow dom codom = MArrow (dom, codom)

type poly =
  | PBot
  | PUnit
  | PParam of label
  | PVar of exist
  | PArrow of poly * poly
  | PForall of label * poly
  | PMono of mono

let poly_bot = PBot
let poly_unit = PUnit
let poly_param name = PParam name
let poly_var exist = PVar exist
let poly_arrow dom codom = PArrow (dom, codom)
let poly_forall param poly = PForall (param, poly)
let poly_mono mono = PMono mono

type expr =
  | EBot
  | EUnit
  | EVar of label
  | EAbs of label * expr
  | EApp of expr * expr
  | EAnno of expr * poly

let expr_bot = EBot
let expr_unit = EUnit
let expr_var name = EVar name
let expr_abs param body = EAbs (param, body)
let expr_app func arg = EApp (func, arg)
let expr_anno expr poly = EAnno (expr, poly)
