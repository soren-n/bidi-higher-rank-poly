open Util
open Extra
open Infix
open Typeset

(*
  Specification implementation of the typeset layout algorithm.
  Achieved via fixpoint algorithms that do local transformations;
    i.e. not efficient, but easy to argue for correctness.
*)

type layout =
  | Null
  | Text of string
  | Fix of layout
  | Grp of layout
  | Seq of layout
  | Nest of layout
  | Pack of int * layout
  | Line of layout * layout
  | Comp of layout * layout * bool * bool

let print_layout layout return =
  let open Printf in
  let rec _visit layout return =
    match layout with
    | Null -> return "Null"
    | Text data -> return (sprintf "(Text %s)" data)
    | Fix layout1 -> _visit layout1 (return <== (sprintf "(Fix %s)"))
    | Grp layout1 -> _visit layout1 (return <== (sprintf "(Grp %s)"))
    | Seq layout1 -> _visit layout1 (return <== (sprintf "(Seq %s)"))
    | Nest layout1 -> _visit layout1 (return <== (sprintf "(Nest %s)"))
    | Pack (index, layout1) ->
      _visit layout1 (return <== (sprintf "(Pack %d %s)" index))
    | Line (left, right) ->
      _visit left @@ fun left1 ->
      _visit right @@ fun right1 ->
      return (sprintf "(Line %s\n%s)" left1 right1)
    | Comp (left, right, pad, fix) ->
      _visit left @@ fun left1 ->
      _visit right @@ fun right1 ->
      return (sprintf "(Comp %s %s %b %b)" left1 right1 pad fix)
  in
  _visit layout return

let convert layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit layout index return =
    match layout with
    | UNull -> return index _null
    | UText data -> return index (_text data)
    | UFix layout1 ->
      _visit layout1 index @@ fun index1 layout ->
      return index1 (_fix layout)
    | UGrp layout1 ->
      _visit layout1 index @@ fun index1 layout ->
      return index1 (_grp layout)
    | USeq layout1 ->
      _visit layout1 index @@ fun index1 layout ->
      return index1 (_seq layout)
    | UNest layout1 ->
      _visit layout1 index @@ fun index1 layout ->
      return index1 (_nest layout)
    | UPack layout1 ->
      _visit layout1 (index + 1) @@ fun index1 layout ->
      return index1 (_pack index layout)
    | ULine (left, right) ->
      _visit left index @@ fun index1 left1 ->
      _visit right index1 @@ fun index2 right1 ->
      return index2 (_line left1 right1)
    | UComp (left, right, attr) ->
      _visit left index @@ fun index1 left1 ->
      _visit right index1 @@ fun index2 right1 ->
      return index2 (_comp left1 right1 attr.pad attr.fix)
  in
  _visit layout 0 @@ fun _index layout1 ->
  return layout1

let undoc doc return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit_doc doc return =
    match doc with
    | REOD -> return _null
    | REmpty doc1 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_line _null doc2)
    | RBreak (obj, doc1) ->
      _visit_obj obj @@ fun obj1 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_line obj1 doc2)
    | RLine obj ->
      _visit_obj obj return
  and _visit_obj obj return =
    match obj with
    | RText data -> return (_text data)
    | RFix fix -> _visit_fix fix (return <== _fix)
    | RGrp obj1 -> _visit_obj obj1 (return <== _grp)
    | RSeq obj1 -> _visit_obj obj1 (return <== _seq)
    | RNest obj1 -> _visit_obj obj1 (return <== _nest)
    | RPack (index, obj1) -> _visit_obj obj1 (return <== (_pack index))
    | RComp (left, right, pad) ->
      _visit_obj left @@ fun left1 ->
      _visit_obj right @@ fun right1 ->
      return (_comp left1 right1 pad false)
  and _visit_fix fix return =
    match fix with
    | RFText data -> return (_text data)
    | RFComp (left, right, pad) ->
      _visit_fix left @@ fun left1 ->
      _visit_fix right @@ fun right1 ->
      return (_comp left1 right1 pad false)
  in
  _visit_doc doc return

type broken =
  | BNull
  | BText of string
  | BFix of broken
  | BGrp of broken
  | BSeq of bool * broken
  | BNest of broken
  | BPack of int * broken
  | BLine of broken * broken
  | BComp of broken * broken * bool * bool

let _elim_broken layout return =
  let _mark layout return =
    let _null = BNull in
    let _text data = BText data in
    let _fix layout = BFix layout in
    let _grp layout = BGrp layout in
    let _seq break layout = BSeq (break, layout) in
    let _nest layout = BNest layout in
    let _pack index layout = BPack (index, layout) in
    let _line left right = BLine (left, right) in
    let _comp left right pad fix = BComp (left, right, pad, fix) in
    let rec _visit layout return =
      match layout with
      | Null -> return false _null
      | Text data -> return false (_text data)
      | Fix layout1 ->
        _visit layout1 @@ fun break layout2 ->
        return break (_fix layout2)
      | Grp layout1 ->
        _visit layout1 @@ fun break layout2 ->
        return break (_grp layout2)
      | Seq layout1 ->
        _visit layout1 @@ fun break layout2 ->
        return break (_seq break layout2)
      | Nest layout1 ->
        _visit layout1 @@ fun break layout2 ->
        return break (_nest layout2)
      | Pack (index, layout1) ->
        _visit layout1 @@ fun break layout2 ->
        return break (_pack index layout2)
      | Line (left, right) ->
        _visit left @@ fun _l_break left1 ->
        _visit right @@ fun _r_break right1 ->
        return true (_line left1 right1)
      | Comp (left, right, pad, fix) ->
        _visit left @@ fun l_break left1 ->
        _visit right @@ fun r_break right1 ->
        let break = l_break || r_break in
        return break (_comp left1 right1 pad fix)
    in
    _visit layout @@ fun _break layout1 ->
    return layout1
  in
  let _remove layout return =
    let _null = Null in
    let _text data = Text data in
    let _fix layout = Fix layout in
    let _grp layout = Grp layout in
    let _seq layout = Seq layout in
    let _nest layout = Nest layout in
    let _pack index layout = Pack (index, layout) in
    let _line left right = Line (left, right) in
    let _comp left right pad fix = Comp (left, right, pad, fix) in
    let rec _visit layout break return =
      match layout with
      | BNull -> return _null
      | BText data -> return (_text data)
      | BFix layout1 -> _visit layout1 false (return <== _fix)
      | BGrp layout1 -> _visit layout1 false (return <== _grp)
      | BSeq (broken, layout1) ->
        if broken
        then _visit layout1 true return
        else _visit layout1 false (return <== _seq)
      | BNest layout1 ->
        _visit layout1 break (return <== _nest)
      | BPack (index, layout1) ->
        _visit layout1 break (return <== (_pack index))
      | BLine (left, right) ->
        _visit left break @@ fun left1 ->
        _visit right break @@ fun right1 ->
        return (_line left1 right1)
      | BComp (left, right, pad, fix) ->
        _visit left break @@ fun left1 ->
        _visit right break @@ fun right1 ->
        if break && not fix
        then return (_line left1 right1)
        else return (_comp left1 right1 pad fix)
    in
    _visit layout false return
  in
  _mark layout @@ fun layout1 ->
  _remove layout1 return

let _lift_lines layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit layout return =
    match layout with
    | Fix (Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_fix l1) (_fix r1))
    | Grp (Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_grp l1) (_grp r1))
    | Seq (Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_seq l1) (_seq r1))
    | Nest (Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_nest l1) (_nest r1))
    | Pack (index, Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_pack index l1) (_pack index r1))
    | Comp (Line (ll, lr), r, pad, fix) ->
      _visit ll @@ fun _ll_change ll1 ->
      _visit lr @@ fun _lr_change lr1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line ll1 (_comp lr1 r1 pad fix))
    | Comp (l, Line (rl, rr), pad, fix) ->
      _visit l @@ fun _l_change l1 ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_line (_comp l1 rl1 pad fix) rr1)
    | Line (Line (ll, lr), r) ->
      _visit ll @@ fun _ll_change ll1 ->
      _visit lr @@ fun _lr_change lr1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line ll1 (_line lr1 r1))
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_seq layout2)
    | Nest layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_nest layout2)
    | Pack (index, layout1) ->
      _visit layout1 @@ fun change layout2 ->
      return change (_pack index layout2)
    | Line (left, right) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (left, right, pad, fix) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad fix)
  in
  let rec _loop layout =
    _visit layout @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _drop_nest_pack layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit layout return =
    match layout with
    (* Nest casss *)
    | Nest (Fix layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_fix (_nest layout2))
    | Nest (Grp layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_grp (_nest layout2))
    | Nest (Seq layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_seq (_nest layout2))
    | Nest (Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_nest l1) (_nest r1))
    | Nest (Comp (l, r, pad, fix)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_comp (_nest l1) (_nest r1) pad fix)
    (* Pack cases *)
    | Pack (index, Fix layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_fix (_pack index layout2))
    | Pack (index, Grp layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_grp (_pack index layout2))
    | Pack (index, Seq layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_seq (_pack index layout2))
    | Pack (index, Line (l, r)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_line (_pack index l1) (_pack index r1))
    | Pack (index, Comp (l, r, pad, fix)) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_comp (_pack index l1) (_pack index r1) pad fix)
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_seq layout2)
    | Nest layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_nest layout2)
    | Pack (index, layout1) ->
      _visit layout1 @@ fun change layout2 ->
      return change (_pack index layout2)
    | Line (left, right) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (left, right, pad, fix) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad fix)
  in
  let rec _loop layout =
    _visit layout @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _drop_infix_fix layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit layout return =
    match layout with
    | Comp (Comp (ll, lr, l_pad, false), r, r_pad, r_fix) ->
      _visit ll @@ fun _ll_change ll1 ->
      _visit lr @@ fun _lr_change lr1 ->
      _visit r @@ fun _ll_change r1 ->
      return true (_comp ll1 (_comp lr1 r1 r_pad r_fix) l_pad false)
    (* Null *)
    | Comp (Null, Null, pad, true) ->
      return true (_fix (_comp _null _null pad false))
    | Comp (Null, Text r_data, pad, true) ->
      return true (_fix (_comp _null (_text r_data) pad false))
    | Comp (Null, Fix r, pad, true) ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_fix (_comp _null r1 pad false))
    | Comp (Null, Nest r, pad, true) ->
      return true (_fix (_comp _null (_nest r) pad false))
    | Comp (Null, Pack (index, r), pad, true) ->
      return true (_fix (_comp _null (_pack index r) pad false))
    | Comp (Null, Grp r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_grp (_comp _null r1 pad true))
    | Comp (Null, Seq r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp _null r1 pad true))
    | Comp (Null, Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp _null rl1 l_pad true) rr1 r_pad false)
    (* Text *)
    | Comp (Text l_data, Null, pad, true) ->
      return true (_fix (_comp (_text l_data) _null pad false))
    | Comp (Text l_data, Text r_data, pad, true) ->
      return true (_fix (_comp (_text l_data) (_text r_data) pad false))
    | Comp (Text l_data, Fix r, pad, true) ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_fix (_comp (_text l_data) r1 pad false))
    | Comp (Text l_data, Nest r, pad, true) ->
      return true (_fix (_comp (_text l_data) (_nest r) pad false))
    | Comp (Text l_data, Pack (index, r), pad, true) ->
      return true (_fix (_comp (_text l_data) (_pack index r) pad false))
    | Comp (Text l_data, Grp r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_grp (_comp (_text l_data) r1 pad true))
    | Comp (Text l_data, Seq r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp (_text l_data) r1 pad true))
    | Comp (Text l_data, Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp (_text l_data) rl1 l_pad true) rr1 r_pad false)
    (* Fix *)
    | Comp (Fix l, Null, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      return true (_fix (_comp l1 _null pad false))
    | Comp (Fix l, Text r_data, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      return true (_fix (_comp l1 (_text r_data) pad false))
    | Comp (Fix l, Fix r, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_fix (_comp l1 r1 pad false))
    | Comp (Fix l, Nest r, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      return true (_fix (_comp l1 (_nest r) pad false))
    | Comp (Fix l, Pack (index, r), pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      return true (_fix (_comp l1 (_pack index r) pad false))
    | Comp (Fix l, Grp r, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_grp (_comp (_fix l1) r1 pad true))
    | Comp (Fix l, Seq r, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp (_fix l1) r1 pad true))
    | Comp (Fix l, Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp (_fix l1) rl1 l_pad true) rr1 r_pad false)
    (* Nest *)
    | Comp (Nest l, Null, pad, true) ->
      return true (_fix (_comp (_nest l) _null pad false))
    | Comp (Nest l, Text r_data, pad, true) ->
      return true (_fix (_comp (_nest l) (_text r_data) pad false))
    | Comp (Nest l, Fix r, pad, true) ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_fix (_comp (_nest l) r1 pad false))
    | Comp (Nest l, Nest r, pad, true) ->
      return true (_fix (_comp (_nest l) (_nest r) pad false))
    | Comp (Nest l, Pack (index, r), pad, true) ->
      return true (_fix (_comp (_nest l) (_pack index r) pad false))
    | Comp (Nest l, Grp r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_grp (_comp (_nest l) r1 pad true))
    | Comp (Nest l, Seq r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp (_nest l) r1 pad true))
    | Comp (Nest l, Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp (_nest l) rl1 l_pad true) rr1 r_pad false)
    (* Pack *)
    | Comp (Pack (index, l), Null, pad, true) ->
      return true (_fix (_comp (_pack index l) _null pad false))
    | Comp (Pack (index, l), Text r_data, pad, true) ->
      return true (_fix (_comp (_pack index l) (_text r_data) pad false))
    | Comp (Pack (index, l), Fix r, pad, true) ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_fix (_comp (_pack index l) r1 pad false))
    | Comp (Pack (index, l), Nest r, pad, true) ->
      return true (_fix (_comp (_pack index l) (_nest r) pad false))
    | Comp (Pack (l_index, l), Pack (r_index, r), pad, true) ->
      return true (_fix (_comp (_pack l_index l) (_pack r_index r) pad false))
    | Comp (Pack (index, l), Grp r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_grp (_comp (_pack index l) r1 pad true))
    | Comp (Pack (index, l), Seq r, pad, true) ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp (_pack index l) r1 pad true))
    | Comp (Pack (index, l), Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp (_pack index l) rl1 l_pad true) rr1 r_pad false)
    (* Grp *)
    | Comp (Grp l, Null, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_grp (_comp l1 _null pad true))
    | Comp (Grp l, Text r_data, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_grp (_comp l1 (_text r_data) pad true))
    | Comp (Grp l, Fix r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_grp (_comp l1 (_fix r1) pad true))
    | Comp (Grp l, Nest r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_grp (_comp l1 (_nest r) pad true))
    | Comp (Grp l, Pack (index, r), pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_grp (_comp l1 (_pack index r) pad true))
    | Comp (Grp l, Grp r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_grp (_comp l1 (_grp r1) pad true))
    | Comp (Grp l, Seq r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp (_grp l1) r1 pad true))
    | Comp (Grp l, Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp (_grp l1) rl1 l_pad true) rr1 r_pad false)
    (* Seq *)
    | Comp (Seq l, Null, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_seq (_comp l1 _null pad true))
    | Comp (Seq l, Text r_data, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_seq (_comp l1 (_text r_data) pad true))
    | Comp (Seq l, Fix r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_seq (_comp l1 (_fix r1) pad true))
    | Comp (Seq l, Nest r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_seq (_comp l1 (_nest r) pad true))
    | Comp (Seq l, Pack (index, r), pad, true) ->
      _visit l @@ fun _l_change l1 ->
      return true (_seq (_comp l1 (_pack index r) pad true))
    | Comp (Seq l, Grp r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp l1 (_grp r1) pad true))
    | Comp (Seq l, Seq r, pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_seq (_comp (_seq l1) r1 pad true))
    | Comp (Seq l, Comp (rl, rr, r_pad, false), l_pad, true) ->
      _visit l @@ fun _l_change l1 ->
      _visit rl @@ fun _rl_change rl1 ->
      _visit rr @@ fun _rr_change rr1 ->
      return true (_comp (_comp (_seq l1) rl1 l_pad true) rr1 r_pad false)
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Nest layout1 -> return false (_nest layout1)
    | Pack (index, layout1) -> return false (_pack index layout1)
    | Fix layout1 ->
      _visit_fix layout1 @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_seq layout2)
    | Line (left, right) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (left, right, pad, fix) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad fix)
  and _visit_fix layout return =
    match layout with
    | Comp (Comp (ll, lr, l_pad, false), r, r_pad, false) ->
      _visit ll @@ fun _ll_change ll1 ->
      _visit lr @@ fun _lr_change lr1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_comp ll1 (_comp lr1 r1 r_pad false) l_pad false)
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Nest layout1 -> return false (_nest layout1)
    | Pack (index, layout1) -> return false (_pack index layout1)
    | Fix layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Grp layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Seq layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Line _ -> assert false (* Invariant *)
    | Comp (l, r, pad, true) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit_fix r @@ fun _r_change r1 ->
      return true (_comp l1 r1 pad false)
    | Comp (l, r, pad, false) ->
      _visit_fix l @@ fun l_change l1 ->
      _visit_fix r @@ fun r_change r1 ->
      let change = l_change || r_change in
      return change (_comp l1 r1 pad false)
  in
  let rec _loop layout =
    _visit layout @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _reassociate layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit layout return =
    match layout with
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_seq layout2)
    | Nest layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_nest layout2)
    | Pack (index, layout1) ->
      _visit layout1 @@ fun change layout2 ->
      return change (_pack index layout2)
    | Line (left, right) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (Comp (ll, lr, l_pad, false), r, r_pad, false) ->
      _visit ll @@ fun _ll_change ll1 ->
      _visit lr @@ fun _lr_change lr1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_comp ll1 (_comp lr1 r1 r_pad false) l_pad false)
    | Comp (left, right, pad, false) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad false)
  in
  let rec _loop layout =
    _visit layout @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _denull layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad fix = Comp (left, right, pad, fix) in
  let rec _visit layout return =
    match layout with
    | Text "" -> return true _null
    | Fix Null -> return true _null
    | Grp Null -> return true _null
    | Seq Null -> return true _null
    | Nest Null -> return true _null
    | Pack (_index, Null) -> return true _null
    | Comp (Null, r, _pad, false) -> return true r
    | Comp (l, Null, _pad, false) -> return true l
    | Comp (l, Comp (Null, r, r_pad, false), l_pad, false) ->
      return true (_comp l r (l_pad || r_pad) false)
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_seq layout2)
    | Nest layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_nest layout2)
    | Pack (index, layout1) ->
      _visit layout1 @@ fun change layout2 ->
      return change (_pack index layout2)
    | Line (left, right) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (left, right, pad, false) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad false)
    (* Invalid cases *)
    | _ -> assert false (* Invariant *)
  in
  let rec _loop layout =
    _visit layout @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _identities layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad = Comp (left, right, pad, false) in
  let rec _visit layout is_head is_seq return =
    match layout with
    (* Fix specific *)
    | Fix Null -> return true _null
    | Fix (Text data) -> return true (_text data)
    | Fix (Nest layout1) -> return true (_nest layout1)
    | Fix (Pack (index, layout1)) -> return true (_pack index layout1)
    (* Grp specific *)
    | Grp Null -> return true _null
    | Grp (Text data) -> return true (_text data)
    | Grp (Nest layout1) -> return true (_nest layout1)
    | Grp (Pack (index, layout1)) -> return true (_pack index layout1)
    | Grp (Fix layout1) ->
      _visit layout1 false is_seq @@ fun _change layout2 ->
      return true (_fix layout2)
    | Grp (Grp layout1) ->
      _visit layout1 false false @@ fun _change layout2 ->
      return true (_grp layout2)
    (* Seq specific *)
    | Seq Null -> return true _null
    | Seq (Text data) -> return true (_text data)
    | Seq (Nest layout1) -> return true (_nest layout1)
    | Seq (Pack (index, layout1)) -> return true (_pack index layout1)
    | Seq (Fix layout1) ->
      _visit layout1 false is_seq @@ fun _change layout2 ->
      return true (_fix layout2)
    | Seq (Grp layout1) ->
      _visit layout1 false false @@ fun _change layout2 ->
      return true (_grp layout2)
    | Seq (Seq layout1) ->
      _visit layout1 false true @@ fun _change layout2 ->
      return true (_seq layout2)
    | Seq (Comp (Null, Null, pad, false)) ->
      return true (_comp _null _null pad)
    | Seq (Comp (Null, Text r_data, pad, false)) ->
      return true (_comp _null (_text r_data) pad)
    | Seq (Comp (Null, Nest right, pad, false)) ->
      return true (_comp _null (_nest right) pad)
    | Seq (Comp (Null, Pack (r_index, right), pad, false)) ->
      return true (_comp _null (_pack r_index right) pad)
    | Seq (Comp (Null, Fix right, pad, false)) ->
      return true (_comp _null (_fix right) pad)
    | Seq (Comp (Null, Grp right, pad, false)) ->
      return true (_comp _null (_grp right) pad)
    | Seq (Comp (Text l_data, Null, pad, false)) ->
      return true (_comp (_text l_data) _null pad)
    | Seq (Comp (Text l_data, Text r_data, pad, false)) ->
      return true (_comp (_text l_data) (_text r_data) pad)
    | Seq (Comp (Text l_data, Nest right, pad, false)) ->
      return true (_comp (_text l_data) (_nest right) pad)
    | Seq (Comp (Text l_data, Pack (r_index, right), pad, false)) ->
      return true (_comp (_text l_data) (_pack r_index right) pad)
    | Seq (Comp (Text l_data, Fix right, pad, false)) ->
      return true (_comp (_text l_data) (_fix right) pad)
    | Seq (Comp (Text l_data, Grp right, pad, false)) ->
      return true (_comp (_text l_data) (_grp right) pad)
    | Seq (Comp (Nest left, Null, pad, false)) ->
      return true (_comp (_nest left) _null pad)
    | Seq (Comp (Nest left, Text r_data, pad, false)) ->
      return true (_comp (_nest left) (_text r_data) pad)
    | Seq (Comp (Nest left, Nest right, pad, false)) ->
      return true (_comp (_nest left) (_nest right) pad)
    | Seq (Comp (Nest left, Pack (r_index, right), pad, false)) ->
      return true (_comp (_nest left) (_pack r_index right) pad)
    | Seq (Comp (Nest left, Fix right, pad, false)) ->
      return true (_comp (_nest left) (_fix right) pad)
    | Seq (Comp (Nest left, Grp right, pad, false)) ->
      return true (_comp (_nest left) (_grp right) pad)
    | Seq (Comp (Pack (l_index, left), Null, pad, false)) ->
      return true (_comp (_pack l_index left) _null pad)
    | Seq (Comp (Pack (l_index, left), Text r_data, pad, false)) ->
      return true (_comp (_pack l_index left) (_text r_data) pad)
    | Seq (Comp (Pack (l_index, left), Nest right, pad, false)) ->
      return true (_comp (_pack l_index left) (_nest right) pad)
    | Seq (Comp (Pack (l_index, left), Pack (r_index, right), pad, false)) ->
      return true (_comp (_pack l_index left) (_pack r_index right) pad)
    | Seq (Comp (Pack (l_index, left), Fix right, pad, false)) ->
      return true (_comp (_pack l_index left) (_fix right) pad)
    | Seq (Comp (Pack (l_index, left), Grp right, pad, false)) ->
      return true (_comp (_pack l_index left) (_grp right) pad)
    | Seq (Comp (Fix left, Null, pad, false)) ->
      return true (_comp (_fix left) _null pad)
    | Seq (Comp (Fix left, Text r_data, pad, false)) ->
      return true (_comp (_fix left) (_text r_data) pad)
    | Seq (Comp (Fix left, Nest right, pad, false)) ->
      return true (_comp (_fix left) (_nest right) pad)
    | Seq (Comp (Fix left, Pack (r_index, right), pad, false)) ->
      return true (_comp (_fix left) (_pack r_index right) pad)
    | Seq (Comp (Fix left, Fix right, pad, false)) ->
      return true (_comp (_fix left) (_fix right) pad)
    | Seq (Comp (Fix left, Grp right, pad, false)) ->
      return true (_comp (_fix left) (_grp right) pad)
    | Seq (Comp (Grp left, Null, pad, false)) ->
      return true (_comp (_grp left) _null pad)
    | Seq (Comp (Grp left, Text r_data, pad, false)) ->
      return true (_comp (_grp left) (_text r_data) pad)
    | Seq (Comp (Grp left, Nest right, pad, false)) ->
      return true (_comp (_grp left) (_nest right) pad)
    | Seq (Comp (Grp left, Pack (r_index, right), pad, false)) ->
      return true (_comp (_grp left) (_pack r_index right) pad)
    | Seq (Comp (Grp left, Fix right, pad, false)) ->
      return true (_comp (_grp left) (_fix right) pad)
    | Seq (Comp (Grp left, Grp right, pad, false)) ->
      return true (_comp (_grp left) (_grp right) pad)
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Nest layout1 -> return false (_nest layout1)
    | Pack (index, layout1) -> return false (_pack index layout1)
    | Fix layout1 ->
      _visit layout1 false is_seq @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 is_head false @@ fun change layout2 ->
      if is_head
      then return true layout2
      else return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 false true @@ fun change layout2 ->
      if is_seq
      then return true layout2
      else return change (_seq layout2)
    | Line (left, right) ->
      _visit left is_head is_seq @@ fun l_change left1 ->
      _visit right true false @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit left is_head is_seq @@ fun l_change left1 ->
      _visit right false is_seq @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad)
  in
  let rec _loop layout =
    _visit layout true false @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _lift_nest_pack layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad = Comp (left, right, pad, false) in
  let rec _visit layout return =
    match layout with
    | Fix (Nest layout1) ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true (_nest (_fix layout2))
    | Fix (Pack (index, layout1)) ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true (_pack index (_fix layout2))
    | Grp (Nest layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_nest (_grp layout2))
    | Grp (Pack (index, layout1)) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_pack index (_grp layout2))
    | Seq (Nest layout1) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_nest (_seq layout2))
    | Seq (Pack (index, layout1)) ->
      _visit layout1 @@ fun _change layout2 ->
      return true (_pack index (_seq layout2))
    | Comp (Nest l, Nest r, pad, false) ->
      _visit l @@ fun _l_change l1 ->
      _visit r @@ fun _r_change r1 ->
      return true (_nest (_comp l1 r1 pad))
    | Comp (Pack (l_index, l), Pack (r_index, r), pad, false) ->
      _visit l @@ fun l_change l1 ->
      _visit r @@ fun r_change r1 ->
      if l_index = r_index
      then return true (_pack l_index (_comp l1 r1 pad)) else
      let change = l_change || r_change in
      return change (_comp (_pack l_index l1) (_pack r_index r1) pad)
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit_fix layout1 @@ fun change layout2 ->
      return change (_fix layout2)
    | Grp layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_grp layout2)
    | Seq layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_seq layout2)
    | Nest layout1 ->
      _visit layout1 @@ fun change layout2 ->
      return change (_nest layout2)
    | Pack (index, layout1) ->
      _visit layout1 @@ fun change layout2 ->
      return change (_pack index layout2)
    | Line (left, right) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_line left1 right1)
    | Comp (_l, _r, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit left @@ fun l_change left1 ->
      _visit right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad)
  and _visit_fix fix return =
    match fix with
    | Comp (Nest l, r, pad, false) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit_fix_right r @@ fun _r_change r1 ->
      return true (_nest (_comp l1 r1 pad))
    | Comp (Pack (index, l), r, pad, false) ->
      _visit_fix l @@ fun _l_change l1 ->
      _visit_fix_right r @@ fun _r_change r1 ->
      return true (_pack index (_comp l1 r1 pad))
    (* Base cases *)
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Grp layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Seq layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Nest layout1 ->
      _visit_fix layout1 @@ fun change layout2 ->
      return change (_nest layout2)
    | Pack (index, layout1) ->
      _visit_fix layout1 @@ fun change layout2 ->
      return change (_pack index layout2)
    | Line (_left, _right) -> assert false (* Invariant *)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit_fix left @@ fun l_change left1 ->
      _visit_fix_right right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad)
  and _visit_fix_right fix return =
    match fix with
    | Null -> return false _null
    | Text data -> return false (_text data)
    | Fix layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Grp layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Seq layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Nest layout1 ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Pack (_index, layout1) ->
      _visit_fix layout1 @@ fun _change layout2 ->
      return true layout2
    | Line (_left, _right) -> assert false (* Invariant *)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit_fix_right left @@ fun l_change left1 ->
      _visit_fix_right right @@ fun r_change right1 ->
      let change = l_change || r_change in
      return change (_comp left1 right1 pad)
  in
  let rec _loop layout =
    _visit layout @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let _clean_fix layout return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad = Comp (left, right, pad, false) in
  let rec _visit layout return =
    match layout with
    | Null -> return _null
    | Text data -> return (_text data)
    | Fix layout1 -> _visit_fix layout1 (return <== _fix)
    | Grp layout1 -> _visit layout1 (return <== _grp)
    | Seq layout1 -> _visit layout1 (return <== _seq)
    | Nest layout1 -> _visit layout1 (return <== _nest)
    | Pack (index, layout1) -> _visit layout1 (return <== (_pack index))
    | Line (left, right) ->
      _visit left @@ fun left1 ->
      _visit right @@ fun right1 ->
      return (_line left1 right1)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit left @@ fun left1 ->
      _visit right @@ fun right1 ->
      return (_comp left1 right1 pad)
  and _visit_fix layout return =
    match layout with
    | Null -> return _null
    | Text data -> return (_text data)
    | Fix _layout1 -> assert false (* Invariant *)
    | Grp _layout1 -> assert false (* Invariant *)
    | Seq _layout1 -> assert false (* Invariant *)
    | Nest layout1 -> _visit_fix layout1 return
    | Pack (_index, layout1) -> _visit_fix layout1 return
    | Line (_left, _right) -> assert false (* Invariant *)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit_fix left @@ fun left1 ->
      _visit_fix right @@ fun right1 ->
      return (_comp left1 right1 pad)
  in
  _visit layout return

let pre_normalize layout return =
  (* print_layout layout (print_endline <== (String.conc "pre_normalize: ")); *)
  _elim_broken layout @@ fun layout1 ->
  (* print_layout layout1 (print_endline <== (String.conc "_elim_broken: ")); *)
  _lift_lines layout1 @@ fun layout2 ->
  (* print_layout layout2 (print_endline <== (String.conc "_lift_lines: ")); *)
  _drop_nest_pack layout2 @@ fun layout3 ->
  (* print_layout layout3 (print_endline <== (String.conc "_drop_nest_pack: ")); *)
  _drop_infix_fix layout3 @@ fun layout4 ->
  (* print_layout layout4 (print_endline <== (String.conc "_drop_infix_fix: ")); *)
  _reassociate layout4 @@ fun layout5 ->
  (* print_layout layout5 (print_endline <== (String.conc "_reassociate: ")); *)
  _denull layout5 @@ fun layout6 ->
  (* print_layout layout6 (print_endline <== (String.conc "_denull: ")); *)
  _identities layout6 @@ fun layout7 ->
  (* print_layout layout7 (print_endline <== (String.conc "_identities: ")); *)
  _reassociate layout7 @@ fun layout8 ->
  (* print_layout layout8 (print_endline <== (String.conc "_reassociate: ")); *)
  _lift_nest_pack layout8 @@ fun layout9 ->
  (* print_layout layout9 (print_endline <== (String.conc "_lift_nest_pack: ")); *)
  _clean_fix layout9 @@ fun layout10 ->
  (* print_layout layout10 (print_endline <== (String.conc "_clean_fix: ")); *)
  (* print_endline "*************************************"; *)
  return layout10

let normalize layout return =
  (* print_layout layout (print_endline <== (String.conc "normalize: ")); *)
  _elim_broken layout @@ fun layout1 ->
  (* print_layout layout1 (print_endline <== (String.conc "_elim_broken: ")); *)
  _lift_lines layout1 @@ fun layout2 ->
  (* print_layout layout2 (print_endline <== (String.conc "_lift_lines: ")); *)
  _drop_nest_pack layout2 @@ fun layout3 ->
  (* print_layout layout3 (print_endline <== (String.conc "_drop_nest_pack: ")); *)
  _identities layout3 @@ fun layout4 ->
  (* print_layout layout4 (print_endline <== (String.conc "_identities: ")); *)
  _reassociate layout4  @@ fun layout5 ->
  (* print_layout layout5 (print_endline <== (String.conc "_reassociate: ")); *)
  _lift_nest_pack layout5 @@ fun layout6 ->
  (* print_layout layout6 (print_endline <== (String.conc "_lift_nest_pack: ")); *)
  (* print_endline "*************************************"; *)
  return layout6

let solve layout tab width return =
  let _null = Null in
  let _text data = Text data in
  let _fix layout = Fix layout in
  let _grp layout = Grp layout in
  let _seq layout = Seq layout in
  let _nest layout = Nest layout in
  let _pack index layout = Pack (index, layout) in
  let _line left right = Line (left, right) in
  let _comp left right pad = Comp (left, right, pad, false) in
  let _equal l r = l = r in
  let rec _visit layout head break pos marks return =
    match layout with
    | Null | Text _ -> return false marks layout
    | Fix layout1 ->
      _measure layout1 true pos marks @@ fun _pos1 marks1 ->
      return false marks1 (_fix layout1)
    | Grp layout1 ->
      _visit layout1 head false pos marks @@ fun change marks1 layout2 ->
      if not change then return false marks1 layout else
      return true marks1 (_grp layout2)
    | Seq layout1 ->
      _measure layout1 head pos marks @@ fun pos1 _marks1 ->
      let break1 = width < pos1 in
      _visit layout1 head break1 pos marks @@ fun change marks2 layout2 ->
      if not change then return false marks2 layout else
      return true marks2 (_seq layout2)
    | Nest layout1 ->
      let offset =
        if tab <= 0 then 0 else
        tab - (pos mod tab)
      in
      let pos1 = if head then pos + offset else pos in
      _visit layout1 head break pos1 marks @@ fun change marks1 layout2 ->
      if not change then return false marks1 layout else
      return true marks1 (_nest layout2)
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _visit layout1 head break pos marks1 @@ fun change marks2 layout2 ->
          if not change then return false marks2 layout else
          return true marks2 (_pack index layout2))
        (fun pos1 ->
          let pos2 = max pos pos1 in
          _visit layout1 head break pos2 marks @@ fun change marks1 layout2 ->
          if not change then return false marks1 layout else
          return true marks1 (_pack index layout2))
    | Line (left, right) ->
      _visit left head break pos marks @@ fun l_change marks1 left1 ->
      if l_change then return true marks1 (_line left1 right) else
      _visit right true break 0 marks1 @@ fun r_change marks2 right1 ->
      if not r_change then return false marks2 layout else
      return true marks2 (_line left1 right1)
    | Comp (_left, _right, _pad, true) -> assert false (* Invariant *)
    | Comp (left, right, pad, false) ->
      _visit left head break pos marks @@ fun l_change marks1 left1 ->
      if l_change then return true marks1 (_comp left1 right pad) else
      if break then return true marks1 (_line left1 right) else
      _measure left head pos marks1 @@ fun pos1 marks2 ->
      let pos2 = if pad then pos1 + 1 else pos1 in
      _next_comp right false pos2 marks2 @@ fun pos3 ->
      if width < pos3 then return true marks2 (_line left1 right) else
      _visit right false break pos2 marks2 @@ fun r_change marks3 right1 ->
      return r_change marks3 (_comp left1 right1 pad)
  and _next_comp layout head pos marks return =
    match layout with
    | Null -> return pos
    | Text data -> return (pos + (String.length data))
    | Fix layout1 ->
      _measure layout1 false pos marks @@ fun pos1 _marks ->
      return pos1
    | Seq layout1 -> _next_comp layout1 head pos marks return
    | Grp layout1 ->
      if head then _next_comp layout1 head pos marks return else
      _measure layout1 false pos marks @@ fun pos1 _marks1 ->
      return pos1
    | Nest layout1 ->
      let offset =
        if tab <= 0 then 0 else
        tab - (pos mod tab)
      in
      let pos1 = if head then pos + offset else pos in
      _next_comp layout1 head pos1 marks return
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _next_comp layout1 head pos marks1 return)
        (fun pos1 ->
          let pos2 = max pos pos1 in
          _next_comp layout1 head pos2 marks return)
    | Line (left, _right) -> _next_comp left head pos marks return
    | Comp (left, _right, _pad, _fix) -> _next_comp left head pos marks return
  and _measure layout head pos marks return =
    match layout with
    | Null -> return pos marks
    | Text data ->
      let n = String.length data in
      return (pos + n) marks
    | Fix layout1 | Seq layout1 | Grp layout1 ->
      _measure layout1 head pos marks return
    | Nest layout1 ->
      let offset =
        if tab <= 0 then 0 else
        tab - (pos mod tab)
      in
      let pos1 = if head then pos + offset else pos in
      _measure layout1 head pos1 marks return
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _measure layout1 head pos marks1 return)
        (fun pos1 ->
          let pos2 = max pos pos1 in
          _measure layout1 head pos2 marks return)
    | Line _ -> assert false (* Invariant *)
    | Comp (left, right, true, _fix) ->
      _measure left head pos marks @@ fun pos1 marks1 ->
      _measure right false (pos1 + 1) marks1 return
    | Comp (left, right, false, _fix) ->
      _measure left head pos marks @@ fun pos1 marks1 ->
      _measure right false pos1 marks1 return
  in
  let rec _loop layout =
    _visit layout true false 0 Env.empty @@ fun change _marks layout1 ->
    normalize layout1 @@ fun layout2 ->
    if change
    then _loop layout2
    else return layout2
  in
  pre_normalize layout _loop

let render layout tab width return =
  let open Printf in
  let _equal l r = l = r in
  let rec _print layout head pos marks return =
    match layout with
    | Null -> return pos marks ""
    | Text data ->
      let pos1 = pos + (String.length data) in
      return pos1 marks data
    | Fix layout1 | Seq layout1 | Grp layout1 ->
      _print layout1 head pos marks return
    | Nest layout1 ->
      let offset =
        if tab <= 0 then 0 else
        tab - (pos mod tab)
      in
      let pos1 = if head then pos + offset else pos in
      _print layout1 head pos1 marks @@ fun pos2 marks1 layout2 ->
      if not head then return pos2 marks1 layout2 else
      let indent = String.make offset ' ' in
      return pos2 marks1 (sprintf "%s%s" indent layout2)
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _print layout1 head pos marks1 return)
        (fun pos1 ->
          let pos2 = max pos pos1 in
          _print layout1 head pos2 marks @@ fun pos3 marks1 layout2 ->
          let padding = String.make (max 0 (pos1 - pos)) ' ' in
          return pos3 marks1 (sprintf "%s%s" padding layout2))
    | Line (left, right) ->
      _print left head pos marks @@ fun _pos1 marks1 left1 ->
      _print right true 0 marks1 @@ fun pos2 marks2 right1 ->
      return pos2 marks2 (sprintf "%s\n%s" left1 right1)
    | Comp (left, right, pad, _fix) ->
      _print left head pos marks @@ fun pos1 marks1 left1 ->
      let pos2 = if pad then pos1 + 1 else pos1 in
      _print right false pos2 marks1 @@ fun pos3 marks2 right1 ->
      let padding = if pad then " " else "" in
      return pos3 marks2 (sprintf "%s%s%s" left1 padding right1)
  in
  solve layout tab width @@ fun layout1 ->
  _print layout1 true 0 Env.empty @@ fun _pos _marks result ->
  return result
