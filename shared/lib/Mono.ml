open Util
open Back
open Syntax
open Simple

(* Mono *)
let rec _gen_mono n ps vs =
  let open QCheck.Gen in
  let _gen_mono_var_fresh _st =
    let exist = ref None in
    vs := exist :: !vs;
    mono_var exist
  in
  let _gen_mono_var =
    let _vs = !vs in
    let m = List.length _vs in
    if m <= 0 then _gen_mono_var_fresh else
    frequency
    [ 1, _gen_mono_var_fresh
    ; m, map mono_var (oneofl _vs)
    ]
  in
  let _gen_mono_term =
    if (List.length ps) <= 0 then
      frequency
      [ 1, return mono_unit
      ; 1, _gen_mono_var
      ]
    else
      frequency
      [ 1, return mono_unit
      ; 1, map mono_param (oneofl ps)
      ; 1, _gen_mono_var
      ]
  in
  if n = 0 then _gen_mono_term else
  frequency
  [ 1, _gen_mono_term
  ; 2, map2 mono_arrow
    (_gen_mono (n / 2) ps vs)
    (_gen_mono (n / 2) ps vs)
  ]

let gen_mono =
  let open QCheck.Gen in
  let ps = [] in
  let vs = ref [] in
  nat >>= fun n ->
  _gen_mono n ps vs

let print_mono ctx mono =
  Print.print_mono ctx mono (fun x -> x)

let rec shrink_mono mono =
  let open QCheck.Iter in
  match mono with
  | MNothing -> empty
  | MUnit -> empty
  | MParam _name -> empty
  | MVar exist ->
    begin match !exist with
    | None -> empty
    | Some mono -> shrink_mono mono >|= fun mono1 -> mono1
    end
  | MArrow (dom, codom) ->
    of_list [dom; codom]
    <+> (shrink_mono dom >|= fun dom1 -> mono_arrow dom1 codom)
    <+> (shrink_mono codom >|= fun codom1 -> mono_arrow dom codom1)

let arbitrary_mono ctx =
  QCheck.make gen_mono
    ~print: (print_mono ctx)
    ~shrink: shrink_mono

(* Simple mono *)
type simple_mono =
  | SMNothing
  | SMProper of proper_simple_mono
and proper_simple_mono =
  | SMUnit
  | SMVar of exist
  | SMArrow of proper_simple_mono * proper_simple_mono
and exist =
  proper_simple_mono option ref

let simple_mono_nothing = SMNothing
let simple_mono_proper proper_simple_mono = SMProper proper_simple_mono
let proper_simple_mono_unit = SMUnit
let proper_simple_mono_var exist = SMVar exist
let proper_simple_mono_arrow dom codom = SMArrow (dom, codom)

let exist_equal left right = left == right

let proper_simple_mono_equal left right =
  let rec _equal left right env fail return =
    match left, right with
    | SMUnit, SMUnit -> return env
    | SMVar left1, SMVar right1 ->
      Env.lookup exist_equal left1 env
        (fun () ->
          Env.bind left1 right1 env return)
        (fun left2 ->
          if exist_equal left2 right1
          then return env
          else fail ())
    | SMArrow (l_dom, l_codom), SMArrow (r_dom, r_codom) ->
      _equal l_dom r_dom env fail @@ fun env1 ->
      _equal l_codom r_codom env1 fail return
    | _, _ -> fail ()
  in
  _equal left right Env.empty
    (fun () -> false)
    (fun _env -> true)

let simple_mono_equal left right =
  match left, right with
  | SMNothing, SMNothing -> true
  | SMProper left1, SMProper right1 ->
    proper_simple_mono_equal left1 right1
  | _, _ -> false

let _bind proper_simple exist vs =
  vs := (proper_simple, exist) :: !vs

let _lookup proper_simple vs return =
  let rec _visit vs exists =
    match vs with
    | [] -> return exists
    | (proper_simple1, exist) :: vs1 ->
      if proper_simple_equal proper_simple proper_simple1
      then _visit vs1 (exist :: exists)
      else _visit vs1 exists
  in
  _visit !vs []

let _proper_simple_convert proper_simple return =
  let rec _convert proper_simple return =
    match proper_simple with
    | SUnit -> return proper_simple_mono_unit
    | SArrow (dom, codom) ->
      _convert dom @@ fun dom1 ->
      _convert codom @@ fun codom1 ->
      return (proper_simple_mono_arrow dom1 codom1)
  in
  _convert proper_simple return

let rec _gen_simple_mono simple vs =
  let open QCheck.Gen in
  match simple with
  | SNothing -> return simple_mono_nothing
  | SProper proper_simple ->
    _gen_proper_simple_mono proper_simple vs >|= fun proper_simple_mono ->
    simple_mono_proper proper_simple_mono
and _gen_proper_simple_mono proper_simple vs =
  let open QCheck.Gen in
  match proper_simple with
  | SUnit ->
    frequency
    [ 1, _gen_proper_simple_mono_exist proper_simple vs
    ; 10, return proper_simple_mono_unit
    ]
  | SArrow (dom, codom) ->
    frequency
    [ 1, _gen_proper_simple_mono_exist proper_simple vs
    ; 10, map2 proper_simple_mono_arrow
      (_gen_proper_simple_mono dom vs)
      (_gen_proper_simple_mono codom vs)
    ]
and _gen_proper_simple_mono_exist proper_simple vs =
  let open QCheck.Gen in
  _lookup proper_simple vs @@ fun vars ->
  let m = List.length vars in
  if m = 0 then _gen_proper_simple_mono_exist_fresh proper_simple vs else
  frequency
  [ 1, _gen_proper_simple_mono_exist_fresh proper_simple vs
  ; m, oneofl vars
  ]
and _gen_proper_simple_mono_exist_fresh proper_simple vs _st =
  _proper_simple_convert proper_simple @@ fun proper_simple_mono ->
  let exist = ref (Some proper_simple_mono) in
  let var = proper_simple_mono_var exist in
  _bind proper_simple var vs;
  var

let gen_proper_simple_mono =
  let open QCheck.Gen in
  let vs = ref [] in
  gen_proper_simple >>= fun proper_simple ->
  _gen_proper_simple_mono proper_simple vs

let gen_simple_mono =
  let open QCheck.Gen in
  let vs = ref [] in
  gen_simple >>= fun simple ->
  _gen_simple_mono simple vs

let rec _print_simple_mono ctx env simple_mono return =
  match simple_mono with
  | SMNothing -> return "⊥"
  | SMProper proper_simple_mono ->
    _print_proper_simple_mono ctx env proper_simple_mono false return
and _print_proper_simple_mono ctx env proper_simple_mono group return =
  let open Printf in
  match proper_simple_mono with
  | SMUnit -> return "unit"
  | SMVar exist ->
    let _env = !env in
    Env.lookup exist_equal exist _env
      (fun () ->
        Naming.sample_exist ctx @@ fun label ->
        Env.bind exist label _env @@ fun env1 ->
        env := env1;
        return label)
      (fun label -> return label)
  | SMArrow (dom, codom) ->
    _print_proper_simple_mono ctx env dom true @@ fun dom1 ->
    _print_proper_simple_mono ctx env codom false @@ fun codom1 ->
    if group
    then return (sprintf "(%s -> %s)" dom1 codom1)
    else return (sprintf "%s -> %s" dom1 codom1)

let print_simple_mono ctx simple_mono =
  let env = ref Env.empty in
  _print_simple_mono ctx env simple_mono (fun x -> x)

let print_proper_simple_mono ctx proper_simple_mono =
  let env = ref Env.empty in
  _print_proper_simple_mono ctx env
    proper_simple_mono false (fun x -> x)

let rec shrink_simple_mono simple_mono =
  let open QCheck.Iter in
  match simple_mono with
  | SMNothing -> empty
  | SMProper proper_simple_mono ->
    shrink_proper_simple_mono proper_simple_mono >|= simple_mono_proper
and shrink_proper_simple_mono proper_simple_mono =
  let open QCheck.Iter in
  match proper_simple_mono with
  | SMUnit -> empty
  | SMVar _exist -> empty
  | SMArrow (dom, codom) ->
    of_list [dom; codom]
    <+> (shrink_proper_simple_mono dom >|= fun dom1 ->
      proper_simple_mono_arrow dom1 codom)
    <+> (shrink_proper_simple_mono codom >|= fun codom1 ->
      proper_simple_mono_arrow dom codom1)

let arbitrary_simple_mono =
  let ctx = Naming.make_ctx () in
  QCheck.make gen_simple_mono
    ~print: (print_simple_mono ctx)
    ~shrink: shrink_simple_mono

(* Convert *)
let simple_2_simple_mono simple return =
  let vs = ref [] in
  return (QCheck.Gen.generate1 (_gen_simple_mono simple vs))
