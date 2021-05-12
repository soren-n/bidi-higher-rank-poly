open Util
open Back
open Syntax
open Mono
open Simple

(* Poly *)
let rec _gen_poly n ctx ps vs =
  let open QCheck.Gen in
  let _gen_poly_var_fresh _st =
    let exist = ref None in
    vs := exist :: !vs;
    poly_var exist
  in
  let _gen_poly_var =
    let _vs = !vs in
    let m = List.length _vs in
    if m <= 0 then _gen_poly_var_fresh else
    frequency
    [ 1, _gen_poly_var_fresh
    ; m, map poly_var (oneofl _vs)
    ]
  in
  let _gen_poly_bit =
    frequency
    [ 1, return (poly_bit Bit8)
    ; 1, return (poly_bit Bit16)
    ; 1, return (poly_bit Bit32)
    ; 1, return (poly_bit Bit64)
    ]
  in
  let _gen_poly_term =
    if (List.length ps) <= 0 then
      frequency
      [ 1, return poly_unit
      ; 1, _gen_poly_var
      ; 1, _gen_poly_bit
      ]
    else
      frequency
      [ 1, return poly_unit
      ; 1, map poly_param (oneofl ps)
      ; 1, _gen_poly_var
      ; 1, _gen_poly_bit
      ]
  in
  let _gen_poly_forall st =
    Naming.sample_label ctx @@ fun param ->
    map (poly_forall param)
      (_gen_poly (n / 2) ctx (param :: ps) vs) st
  in
  if n = 0 then _gen_poly_term else
  frequency
  [ 1, _gen_poly_term
  ; 1, _gen_poly_forall
  ; 1, map poly_mono (_gen_mono n ps vs)
  ; 2, map2 poly_arrow
    (_gen_poly (n / 2) ctx ps vs)
    (_gen_poly (n / 2) ctx ps vs)
  ]

let gen_poly ctx =
  let open QCheck.Gen in
  let ps = [] in
  let vs = ref [] in
  nat >>= fun n ->
  _gen_poly n ctx ps vs

let print_poly ctx poly =
  Print.print_poly ctx poly (fun x -> x)

let rec shrink_poly poly =
  let open QCheck.Iter in
  match poly with
  | PNothing -> empty
  | PUnit -> empty
  | PBit _size -> empty
  | PParam _name -> empty
  | PVar exist ->
    begin match !exist with
    | None -> empty
    | Some mono -> shrink_mono mono >|= fun mono1 -> poly_mono mono1
    end
  | PArrow (dom, codom) ->
    of_list [dom; codom]
    <+> (shrink_poly dom >|= fun dom1 -> poly_arrow dom1 codom)
    <+> (shrink_poly codom >|= fun codom1 -> poly_arrow dom codom1)
  | PForall (param, poly1) ->
    shrink_poly poly1 >|= fun poly2 -> poly_forall param poly2
  | PMono mono ->
    shrink_mono mono >|= fun mono1 -> poly_mono mono1

let arbitrary_poly ctx =
  QCheck.make (gen_poly ctx)
    ~print: (print_poly ctx)
    ~shrink: shrink_poly

(* Convert *)
let rec simple_2_simple_poly simple return =
  match simple with
  | SNothing -> return poly_nothing
  | SProper proper_simple ->
    _proper_simple_2_simple_poly proper_simple return
and _proper_simple_2_simple_poly proper_simple return =
  match proper_simple with
  | SUnit -> return poly_unit
  | SBit size -> return (poly_bit size)
  | SArrow (dom, codom) ->
    _proper_simple_2_simple_poly dom @@ fun dom1 ->
    _proper_simple_2_simple_poly codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)

let rec simple_mono_2_simple_poly simple_mono return =
  match simple_mono with
  | SMNothing -> return poly_nothing
  | SMProper proper_simple_mono ->
    let env = ref Env.empty in
    _proper_simple_mono_2_simple_poly env proper_simple_mono return
and _proper_simple_mono_2_simple_poly env proper_simple_mono return =
  match proper_simple_mono with
  | SMUnit -> return poly_unit
  | SMBit size -> return (poly_bit size)
  | SMVar from_exist ->
    let _env = !env in
    Env.lookup exist_equal from_exist _env
      (fun () ->
        let to_exist = ref None in
        Env.bind from_exist to_exist _env @@ fun env1 ->
        env := env1;
        return (poly_var to_exist))
      (fun to_exist ->
        return (poly_var to_exist))
  | SMArrow (dom, codom) ->
    _proper_simple_mono_2_simple_poly env dom @@ fun dom1 ->
    _proper_simple_mono_2_simple_poly env codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)

let proper_simple_mono_2_proper_simple_poly proper_simple_mono return =
  let env = ref Env.empty in
  _proper_simple_mono_2_simple_poly env proper_simple_mono return
