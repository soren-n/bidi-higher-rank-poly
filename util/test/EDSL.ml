open Util
open Typeset
open Word

let _null = UNull
let _text data = UText data
let _fix eDSL = UFix eDSL
let _seq eDSL = USeq eDSL
let _grp eDSL = UGrp eDSL
let _nest eDSL = UNest eDSL
let _pack eDSL = UPack eDSL
let _line left right = ULine (left, right)
let _comp left right attr = UComp (left, right, attr)

let rec _gen_eDSL n =
  let open QCheck.Gen in
  let _gen_eDSL_term =
    oneof
    [ return _null
    ; map _text gen_word
    ]
  in
  if n <= 0 then _gen_eDSL_term else
  let _gen_eDSL_unary =
    oneof
    [ (fun st -> map _fix (_gen_eDSL (n / 2)) st)
    ; (fun st -> map _seq (_gen_eDSL (n / 2)) st)
    ; (fun st -> map _grp (_gen_eDSL (n / 2)) st)
    ; (fun st -> map _nest (_gen_eDSL (n / 2)) st)
    ; (fun st -> map _pack (_gen_eDSL (n / 2)) st)
    ]
  in
  let _gen_eDSL_line st =
    map2 _line
      (_gen_eDSL (n / 2))
      (_gen_eDSL (n / 2))
      st
  in
  let _gen_attr =
    bool >>= fun pad ->
    bool >>= fun fix ->
    return { pad = pad; fix = fix }
  in
  let _gen_eDSL_comp =
    _gen_attr >>= fun attr ->
    map2 (fun left right -> _comp left right attr)
      (_gen_eDSL (n / 2))
      (_gen_eDSL (n / 2))
  in
  let _gen_eDSL_binary =
    frequency
    [ 1, _gen_eDSL_line
    ; 2, _gen_eDSL_comp
    ]
  in
  frequency
  [ 1, _gen_eDSL_unary
  ; 2, _gen_eDSL_binary
  ]

let gen_eDSL =
  let open QCheck.Gen in
  nat >>= _gen_eDSL

let shrink_eDSL eDSL =
  let open QCheck.Iter in
  let rec _shrink eDSL =
    match eDSL with
    | UNull -> empty
    | UText data ->
      empty <+> (shrink_word data >|= _text)
    | UFix eDSL1 ->
      return eDSL1
      <+> (_shrink eDSL1 >|= _fix)
    | USeq eDSL1 ->
      return eDSL1
      <+> (_shrink eDSL1 >|= _seq)
    | UGrp eDSL1 ->
      return eDSL1
      <+> (_shrink eDSL1 >|= _grp)
    | UNest eDSL1 ->
      return eDSL1
      <+> (_shrink eDSL1 >|= _nest)
    | UPack eDSL1 ->
      return eDSL1
      <+> (_shrink eDSL1 >|= _pack)
    | ULine (left, right) ->
      of_list [left; right]
      <+> (_shrink left >|= fun left1 -> _line left1 right)
      <+> (_shrink right >|= fun right1 -> _line left right1)
    | UComp (left, right, attr) ->
      _shrink_attr attr >>= fun attr1 ->
      of_list [left; right]
      <+> (_shrink left >>= fun left1 ->
        (return (_comp left1 right attr1)))
      <+> (_shrink right >>= fun right1 ->
        (return (_comp left right1 attr1)))
  and _shrink_attr attr =
    return attr <+>
    return { attr with pad = not attr.pad } <+>
    return { attr with fix = not attr.fix } <+>
    return { pad = not attr.pad; fix = not attr.fix }
  in
  _shrink eDSL

let print_eDSL eDSL =
  let open Printf in
  let _pass msg = msg in
  let _wrap = sprintf "(%s)" in
  let rec _print eDSL wrap return =
    match eDSL with
    | UNull -> return "null"
    | UText data -> return (sprintf "~$\"%s\"" data)
    | UFix eDSL1 ->
      _print eDSL1 _wrap @@ fun layout2 ->
      return (wrap (sprintf "fix %s" layout2))
    | UGrp eDSL1 ->
      _print eDSL1 _wrap @@ fun layout2 ->
      return (wrap (sprintf "grp %s" layout2))
    | USeq eDSL1 ->
      _print eDSL1 _wrap @@ fun layout2 ->
      return (wrap (sprintf "seq %s" layout2))
    | UNest eDSL1 ->
      _print eDSL1 _wrap @@ fun layout2 ->
      return (wrap (sprintf "nest %s" layout2))
    | UPack eDSL1 ->
      _print eDSL1 _wrap @@ fun layout2 ->
      return (wrap (sprintf "pack %s" layout2))
    | ULine (left, right) ->
      _print left _wrap @@ fun left1 ->
      _print right _pass @@ fun right1 ->
      return (wrap (sprintf "%s </>\n%s" left1 right1))
    | UComp (left, right, attr) ->
      _print left _wrap @@ fun left1 ->
      _print right _pass @@ fun right1 ->
      let _opr =
        match attr.fix, attr.pad with
        | true, true -> "<!+>"
        | true, false -> "<!&>"
        | false, true -> "<+>"
        | false, false -> "<&>"
      in
      return (wrap (sprintf "%s %s %s" left1 _opr right1))
  in
  _print eDSL _pass (fun x -> x)

let arbitrary_eDSL =
  QCheck.make gen_eDSL
    ~print: print_eDSL
    ~shrink: shrink_eDSL
