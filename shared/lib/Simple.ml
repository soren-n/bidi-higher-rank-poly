open Back
open Constants

type simple =
  | SNothing
  | SProper of proper_simple
and proper_simple =
  | SUnit
  | SBit of bit_size
  | SArrow of proper_simple * proper_simple

let simple_nothing = SNothing
let simple_proper simple = SProper simple
let proper_simple_unit = SUnit
let proper_simple_bit size = SBit size
let proper_simple_arrow dom codom = SArrow (dom, codom)

let proper_simple_equal left right =
  let rec _equal left right =
    match left, right with
    | SUnit, SUnit -> true
    | SBit l_size, SBit r_size -> l_size = r_size
    | SArrow (l_dom, l_codom), SArrow (r_dom, r_codom) ->
      if not (_equal l_dom r_dom) then false else
      if not (_equal l_codom r_codom) then false else
      true
    | _, _ -> false
  in
  _equal left right

let simple_equal left right =
  match left, right with
  | SNothing, SNothing -> true
  | SProper left1, SProper right1 ->
    proper_simple_equal left1 right1
  | _, _ -> false

let _gen_simple_bit =
  let open QCheck.Gen in
  frequency
  [ 1, return (proper_simple_bit Bit8)
  ; 1, return (proper_simple_bit Bit16)
  ; 1, return (proper_simple_bit Bit32)
  ; 1, return (proper_simple_bit Bit64)
  ]

let rec _gen_proper_simple n =
  let open QCheck.Gen in
  match n with
  | 0 -> return proper_simple_unit
  | _ ->
    frequency
    [ 1, return proper_simple_unit
    ; 1, _gen_simple_bit
    ; 2, map2 proper_simple_arrow
      (_gen_proper_simple (n / 2))
      (_gen_proper_simple (n / 2))
    ]

let gen_proper_simple =
  let open QCheck.Gen in
  nat >>= fun n ->
  _gen_proper_simple n

exception Nothing

let rec _gen_simple n =
  let open QCheck.Gen in
  let _gen_simple_nothing _st = raise Nothing in
  let _gen_simple_term =
    frequency
    [ 1, _gen_simple_nothing
    ; 100, return proper_simple_unit
    ; 100, _gen_simple_bit
    ]
  in
  match n with
  | 0 -> _gen_simple_term
  | _ ->
    frequency
    [ 1, _gen_simple_term
    ; 2, map2 proper_simple_arrow
      (_gen_simple (n / 2))
      (_gen_simple (n / 2))
    ]

let _gen_simple_wrap n st =
  try simple_proper (_gen_simple n st)
  with Nothing -> simple_nothing

let gen_simple =
  let open QCheck.Gen in
  nat >>= fun n ->
  _gen_simple_wrap n

let rec _print_simple simple return =
  match simple with
  | SNothing -> return "nothing"
  | SProper proper_simple ->
    _print_proper_simple proper_simple false return
and _print_proper_simple proper_simple group return =
  let open Printf in
  match proper_simple with
  | SUnit -> return "unit"
  | SBit size ->
    begin match size with
    | Bit8 -> return "bit8"
    | Bit16 -> return "bit16"
    | Bit32 -> return "bit32"
    | Bit64 -> return "bit64"
    end
  | SArrow (dom, codom) ->
    _print_proper_simple dom true @@ fun dom1 ->
    _print_proper_simple codom false @@ fun codom1 ->
    if group
    then return (sprintf "(%s -> %s)" dom1 codom1)
    else return (sprintf "%s -> %s" dom1 codom1)

let print_simple simple =
  _print_simple simple (fun x -> x)

let print_proper_simple proper_simple =
  _print_proper_simple proper_simple false (fun x -> x)

let rec shrink_simple simple =
  let open QCheck.Iter in
  match simple with
  | SNothing -> empty
  | SProper proper_simple ->
    shrink_proper_simple proper_simple >|= simple_proper
and shrink_proper_simple proper_simple =
  let open QCheck.Iter in
  match proper_simple with
  | SUnit -> empty
  | SBit _size -> empty
  | SArrow (dom, codom) ->
    of_list [dom; codom]
    <+> (shrink_proper_simple dom >|= fun dom1 ->
      proper_simple_arrow dom1 codom)
    <+> (shrink_proper_simple codom >|= fun codom1 ->
      proper_simple_arrow dom codom1)

let arbitrary_simple =
  QCheck.make gen_simple
    ~print: print_simple
    ~shrink: shrink_simple

let arbitrary_proper_simple =
  QCheck.make gen_proper_simple
    ~print: print_proper_simple
    ~shrink: shrink_proper_simple
