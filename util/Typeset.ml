open Infix
open Extra

type attr =
  { pad : bool
  ; fix : bool
  }

type eDSL =
  | UNull
  | UText of string
  | UFix of eDSL
  | UGrp of eDSL
  | USeq of eDSL
  | UNest of eDSL
  | UPack of eDSL
  | ULine of eDSL * eDSL
  | UComp of eDSL * eDSL * attr

let null = UNull
let text data = UText data
let fix layout = UFix layout
let grp layout = UGrp layout
let seq layout = USeq layout
let nest layout = UNest layout
let pack layout = UPack layout
let line left right = ULine (left, right)
let comp left right pad fix =
  UComp (left, right,
    { pad = pad
    ; fix = fix
    })

let (~$) data = text data
let (</>) left right = line left right
let (<&>) left right = comp left right false false
let (<+>) left right = comp left right true false
let (<!&>) left right = comp left right false true
let (<!+>) left right = comp left right true true

type break =
  | BNull
  | BText of string
  | BFix of break
  | BGrp of break
  | BSeq of bool * break
  | BNest of break
  | BPack of break
  | BLine of break * break
  | BComp of break * break * attr

(* Annotate broken sequences *)
let _broken eDSL return =
  let null = BNull in
  let text data = BText data in
  let fix layout = BFix layout in
  let grp layout = BGrp layout in
  let seq broken layout = BSeq (broken, layout) in
  let nest layout = BNest layout in
  let pack layout = BPack layout in
  let line left right = BLine (left, right) in
  let comp left right attr = BComp (left, right, attr) in
  let rec _visit eDSL return =
    match eDSL with
    | UNull -> return false null
    | UText data -> return false (text data)
    | UFix eDSL1 ->
      _visit eDSL1 @@ fun broken layout ->
      return broken (fix layout)
    | UGrp eDSL1 ->
      _visit eDSL1 @@ fun broken layout ->
      return broken (grp layout)
    | USeq eDSL1 ->
      _visit eDSL1 @@ fun broken layout ->
      return broken (seq broken layout)
    | UNest eDSL1 ->
      _visit eDSL1 @@ fun broken layout ->
      return broken (nest layout)
    | UPack eDSL1 ->
      _visit eDSL1 @@ fun broken layout ->
      return broken (pack layout)
    | ULine (left, right) ->
      _visit left @@ fun _l_broken left1 ->
      _visit right @@ fun _r_broken right1 ->
      return true (line left1 right1)
    | UComp (left, right, attr) ->
      _visit left @@ fun l_broken left1 ->
      _visit right @@ fun r_broken right1 ->
      let broken = l_broken || r_broken in
      return broken (comp left1 right1 attr)
  in
  _visit eDSL @@ fun _break layout ->
  return layout

(*
  Collapse broken sequences.
  Remove identities under fix.
  Shrink wrap packs.
*)
let _collapse eDSL return =
  let null = UNull in
  let text data = UText data in
  let fix eDSL = UFix eDSL in
  let grp eDSL = UGrp eDSL in
  let seq eDSL = USeq eDSL in
  let nest eDSL = UNest eDSL in
  let pack eDSL = UPack eDSL in
  let line left right = ULine (left, right) in
  let comp left right attr = UComp (left, right, attr) in
  let rec _visit eDSL break packer return =
    match eDSL with
    | BNull -> return (packer null)
    | BText data -> return (packer (text data))
    | BFix eDSL1 -> _visit_fix eDSL1 false packer (return <== fix)
    | BGrp eDSL1 -> _visit eDSL1 false packer (return <== grp)
    | BSeq (broken, eDSL1) ->
      if broken
      then _visit eDSL1 true packer return
      else _visit eDSL1 false packer (return <== seq)
    | BNest eDSL1 -> _visit eDSL1 break identity (return <== packer <== nest)
    | BPack eDSL1 -> _visit eDSL1 break pack return
    | BLine (left, right) ->
      _visit left break identity @@ fun left1 ->
      _visit right break identity @@ fun right1 ->
      return (packer (line left1 right1))
    | BComp (left, right, attr) ->
      _visit left break identity @@ fun left1 ->
      _visit right break identity @@ fun right1 ->
      if break && not attr.fix
      then return (packer (line left1 right1))
      else return (packer (comp left1 right1 attr))
  and _visit_fix eDSL break packer return =
    match eDSL with
    | BNull -> return (packer null)
    | BText data -> return (packer (text data))
    | BFix eDSL1 -> _visit_fix eDSL1 break packer return
    | BGrp eDSL1 -> _visit_fix eDSL1 break packer return
    | BSeq (broken, eDSL1) -> _visit_fix eDSL1 broken packer return
    | BNest eDSL1 ->
      _visit_fix eDSL1 break identity (return <== packer <== nest)
    | BPack eDSL1 -> _visit_fix eDSL1 break pack return
    | BLine (left, right) ->
      _visit_fix left break identity @@ fun left1 ->
      _visit_fix right break identity @@ fun right1 ->
      return (packer (line left1 right1))
    | BComp (left, right, attr) ->
      _visit_fix left break identity @@ fun left1 ->
      _visit_fix right break identity @@ fun right1 ->
      if break
      then return (packer (line left1 right1))
      else return (packer (comp left1 right1 attr))
  in
  _broken eDSL @@ fun eDSL1 ->
  _visit eDSL1 false identity return

type marked =
  | MNull
  | MText of string
  | MFix of marked
  | MGrp of marked
  | MSeq of marked
  | MNest of marked
  | MMark of int * marked
  | MMove of int * marked
  | MLine of marked * marked
  | MComp of marked * marked * attr

(* Convert pack to mark and move *)
let _unpack eDSL return =
  let null = MNull in
  let text data = MText data in
  let fix layout = MFix layout in
  let grp layout = MGrp layout in
  let seq layout = MSeq layout in
  let nest layout = MNest layout in
  let mark index layout = MMark (index, layout) in
  let move index layout = MMove (index, layout) in
  let line left right = MLine (left, right) in
  let comp left right attr = MComp (left, right, attr) in
  let rec _visit eDSL index return =
    match eDSL with
    | UNull -> return null
    | UText data -> return (text data)
    | UFix eDSL1 -> _visit eDSL1 index (return <== fix)
    | UGrp eDSL1 -> _visit eDSL1 index (return <== grp)
    | USeq eDSL1 -> _visit eDSL1 index (return <== seq)
    | UNest eDSL1 -> _visit eDSL1 index (return <== nest)
    | UPack eDSL1 ->
      _visit_move_left eDSL1 index @@ fun l ls ->
      return (ls (mark index l))
    | ULine (l, r) ->
      _visit l index @@ fun l1 ->
      _visit r index @@ fun r1 ->
      return (line l1 r1)
    | UComp (l, r, attr) ->
      _visit l index @@ fun l1 ->
      _visit r index @@ fun r1 ->
      return (comp l1 r1 attr)
  and _visit_move_left eDSL index defer =
    match eDSL with
    | UNull | UText _ | UFix _ | UPack _ ->
      _visit eDSL (index + 1) @@ fun l1 ->
      defer l1 identity
    | UGrp eDSL1 ->
      _visit_move eDSL1 index @@ fun eDSL2 ->
      defer (grp eDSL2) identity
    | USeq eDSL1 ->
      _visit_move eDSL1 index @@ fun eDSL2 ->
      defer (seq eDSL2) identity
    | UNest eDSL1 ->
      _visit_move eDSL1 index @@ fun eDSL2 ->
      defer (nest eDSL2) identity
    | ULine (l, r) ->
      _visit_move_left l index @@ fun ll ls ->
      _visit_move r index @@ fun r1 ->
      defer ll @@ fun ll1 ->
      line (ls ll1) (move index r1)
    | UComp (l, r, attr) ->
      _visit_move_left l index @@ fun ll ls ->
      _visit_move r index @@ fun r1 ->
      defer ll @@ fun ll1 ->
      comp (ls ll1) (move index r1) attr
  and _visit_move eDSL index return =
    match eDSL with
    | UNull | UText _ | UFix _ | UPack _ ->
      _visit eDSL (index + 1) return
    | UGrp eDSL1 ->
      _visit_move eDSL1 index (return <== grp)
    | USeq eDSL1 ->
      _visit_move eDSL1 index (return <== seq)
    | UNest eDSL1 ->
      _visit_move eDSL1 index (return <== nest)
    | ULine (l, r) ->
      _visit_move l index @@ fun l1 ->
      _visit_move r index @@ fun r1 ->
      return (line l1 (move index r1))
    | UComp (l, r, attr) ->
      _visit_move l index @@ fun l1 ->
      _visit_move r index @@ fun r1 ->
      return (comp l1 (move index r1) attr)
  in
  _visit eDSL 0 return

type lin_doc =
  | LEOD
  | LLine of lin_obj
  | LEmpty of lin_doc
  | LBreak of lin_obj * lin_doc
and lin_obj =
  | LNull
  | LText of string
  | LFix of lin_obj
  | LGrp of lin_obj
  | LSeq of lin_obj
  | LNest of lin_obj
  | LMark of int * lin_obj
  | LMove of int * lin_obj
  | LComp of lin_obj * lin_obj * attr

(* Lift lines to root *)
let _linearize eDSL (return : lin_doc -> 'a) : 'a =
  let eod = LEOD in
  let line obj = LLine obj in
  let empty doc = LEmpty doc in
  let break obj doc = LBreak (obj, doc) in
  let null = LNull in
  let text data = LText data in
  let fix obj = LFix obj in
  let grp obj = LGrp obj in
  let seq obj = LSeq obj in
  let nest obj = LNest obj in
  let mark index obj = LMark (index, obj) in
  let move index obj = LMove (index, obj) in
  let comp left right attr = LComp (left, right, attr) in
  let _last xs none_case some_case =
    let _cons k x xs = k (x :: xs) in
    let rec _visit xs path =
      match xs with
      | [] -> none_case ()
      | x :: [] -> some_case x path
      | x :: xs1 -> _visit xs1 (_cons path x)
    in
    _visit xs identity
  in
  let rec _flatten layout result return =
    match layout with
    | MNull -> return null result
    | MText data -> return (text data) result
    | MFix layout1 ->
      _flatten layout1 [] @@ fun first rest ->
      return (fix first)
        (List.fold result (List.cons <== fix) rest)
    | MGrp layout1 ->
      _flatten layout1 [] @@ fun first rest ->
      return (grp first)
        (List.fold result (List.cons <== grp) rest)
    | MSeq layout1 ->
      _visit_seq layout1 @@ fun layout2 ->
      return (seq layout2) result
    | MNest layout1 ->
      _flatten layout1 [] @@ fun first rest ->
      return (nest first)
        (List.fold result (List.cons <== nest) rest)
    | MMark (index, layout1) ->
      _flatten layout1 [] @@ fun first rest ->
      return (mark index first)
        (List.fold result (List.cons <== (move index)) rest)
    | MMove (index, layout1) ->
      _flatten layout1 [] @@ fun first rest ->
      return (move index first)
        (List.fold result (List.cons <== (move index)) rest)
    | MLine (left, right) ->
      _flatten right result @@ fun first rest ->
      _flatten left (first :: rest) return
    | MComp (left, right, attr) ->
      _flatten right result @@ fun r_first r_rest ->
      _flatten left [] @@ fun l_first l_rest ->
      _last l_rest
        (fun () ->
          return (comp l_first r_first attr) r_rest)
        (fun l_last l_path ->
          return l_first (l_path ((comp l_last r_first attr) :: r_rest)))
  and _visit_seq layout return =
    match layout with
    | MNull -> return null
    | MText data -> return (text data)
    | MFix layout1 -> _visit_seq layout1 (return <== fix)
    | MGrp layout1 -> _visit_seq layout1 (return <== grp)
    | MSeq layout1 -> _visit_seq layout1 (return <== seq)
    | MNest layout1 -> _visit_seq layout1 (return <== nest)
    | MMark (index, layout1) -> _visit_seq layout1 (return <== (mark index))
    | MMove (index, layout1) -> _visit_seq layout1 (return <== (move index))
    | MComp (left, right, attr) ->
      _visit_seq left @@ fun left1 ->
      _visit_seq right @@ fun right1 ->
      return (comp left1 right1 attr)
    | MLine _ -> assert false (* Invariant *)
  in
  _flatten eDSL [] @@ fun first rest ->
  List.fold
    (fun return -> return eod)
    (fun obj visit_rest return ->
      visit_rest @@ fun doc ->
      match obj, doc with
      | _, LEOD -> return (line obj)
      | LNull, _ -> return (empty doc)
      | _, _ -> return (break obj doc))
    (first :: rest) return

type expand_doc =
  | EEOD
  | ELine of expand_obj
  | EEmpty of expand_doc
  | EBreak of expand_obj * expand_doc
and expand_obj =
  | ENull
  | EText of string
  | EFix of expand_obj
  | EGrp of expand_obj
  | ESeq of expand_obj
  | ENest of bool * expand_obj
  | EMark of bool * int * expand_obj
  | EMove of bool * int * expand_obj
  | EComp of expand_obj * expand_obj * attr

(* Sink nests and annotate terms *)
let _expand doc return =
  let eod = EEOD in
  let line obj = ELine obj in
  let empty doc = EEmpty doc in
  let break obj doc = EBreak (obj, doc) in
  let null = ENull in
  let text data = EText data in
  let fix obj = EFix obj in
  let grp obj = EGrp obj in
  let seq obj = ESeq obj in
  let nest is_term obj = ENest (is_term, obj) in
  let mark is_term index obj = EMark (is_term, index, obj) in
  let move is_term index obj = EMove (is_term, index, obj) in
  let comp left right attr = EComp (left, right, attr) in
  let rec _gen_nests count is_term obj =
    if count <= 0 then obj else
    _gen_nests (count - 1) is_term (nest is_term obj)
  in
  let rec _visit_doc doc return =
    match doc with
    | LEOD -> return eod
    | LLine obj ->
      _visit_obj 0 obj @@ fun _is_term obj1 ->
      return (line obj1)
    | LEmpty doc1 -> _visit_doc doc1 (return <== empty)
    | LBreak (obj, doc1) ->
      _visit_obj 0 obj @@ fun _is_term obj1 ->
      _visit_doc doc1 (return <== (break obj1))
  and _visit_obj depth obj return =
    match obj with
    | LNull -> return true (_gen_nests depth true null)
    | LText data -> return true (_gen_nests depth true (text data))
    | LNest obj1 -> _visit_obj (depth + 1) obj1 return
    | LFix obj1 ->
      _visit_fix true depth obj1 @@ fun is_atom depth1 layout ->
      if is_atom
      then return true (_gen_nests depth1 true layout)
      else return true (_gen_nests depth1 true (fix layout))
    | LGrp obj1 ->
      _visit_obj depth obj1 @@ fun is_term layout ->
      if is_term
      then return true layout
      else return false (grp layout)
    | LSeq obj1 ->
      _visit_obj depth obj1 @@ fun is_term layout ->
      if is_term
      then return true layout
      else return false (seq layout)
    | LMark (index, obj1) ->
      _visit_obj 0 obj1 @@ fun is_term layout ->
      return is_term (_gen_nests depth is_term (mark is_term index layout))
    | LMove (index, obj1) ->
      _visit_obj 0 obj1 @@ fun is_term layout ->
      return is_term (_gen_nests depth is_term (move is_term index layout))
    | LComp (left, right, attr) ->
      _visit_obj depth left @@ fun _l_is_term left1 ->
      _visit_obj depth right @@ fun _r_is_term right1 ->
      return false (comp left1 right1 attr)
  and _visit_fix head depth obj return =
    match obj with
    | LNull -> return true depth null
    | LText data -> return true depth (text data)
    | LFix obj1 -> _visit_fix head depth obj1 return
    | LGrp obj1 -> _visit_fix head depth obj1 return
    | LSeq obj1 -> _visit_fix head depth obj1 return
    | LNest obj1 ->
      if head
      then _visit_fix true (depth + 1) obj1 return
      else _visit_fix false depth obj1 return
    | LMark (index, obj1) ->
      _visit_fix head depth obj1 @@ fun is_atom depth1 layout ->
      return is_atom depth1 (mark true index layout)
    | LMove (index, obj1) ->
      _visit_fix head depth obj1 @@ fun is_atom depth1 layout ->
      return is_atom depth1 (move true index layout)
    | LComp (left, right, attr) ->
      _visit_fix head depth left @@ fun _l_is_atom l_depth left1 ->
      _visit_fix false 0 right @@ fun _r_is_atom _r_depth right1 ->
      return false l_depth (comp left1 right1 { attr with fix = false})
  in
  _visit_doc doc return

type desugar_doc =
  | DEOD
  | DLine of desugar_obj
  | DEmpty of desugar_doc
  | DBreak of desugar_obj * desugar_doc
and desugar_obj =
  | DNull
  | DText of string
  | DFix of desugar_obj
  | DGrp of desugar_obj
  | DSeq of desugar_obj
  | DNest of bool * desugar_obj
  | DMark of bool * int * desugar_obj
  | DMove of bool * int * desugar_obj
  | DComp of desugar_obj * desugar_obj * bool

(* Sink fixed compositions *)
let _desugar doc return =
  let eod = DEOD in
  let line obj = DLine obj in
  let empty doc = DEmpty doc in
  let break obj doc = DBreak (obj, doc) in
  let null = DNull in
  let text data = DText data in
  let fix obj = DFix obj in
  let grp obj = DGrp obj in
  let seq obj = DSeq obj in
  let nest is_term obj = DNest (is_term, obj) in
  let mark is_term index obj = DMark (is_term, index, obj) in
  let move is_term index obj = DMove (is_term, index, obj) in
  let comp left right pad = DComp (left, right, pad) in
  let rec _visit_doc doc return =
    match doc with
    | EEOD -> return eod
    | ELine obj -> _visit_obj obj (return <== line)
    | EEmpty doc1 -> _visit_doc doc1 (return <== empty)
    | EBreak (obj, doc1) ->
      _visit_obj obj @@ fun obj1 ->
      _visit_doc doc1 (return <== break obj1)
  and _visit_obj obj return =
    match obj with
    | ENull -> return null
    | EText data -> return (text data)
    | EFix obj1 -> _visit_fix obj1 (return <== fix)
    | EGrp obj1 -> _visit_obj obj1 (return <== grp)
    | ESeq obj1 -> _visit_obj obj1 (return <== seq)
    | ENest (is_term, obj1) ->
      if is_term
      then _visit_term obj1 (return <== (nest true))
      else _visit_obj obj1 (return <== (nest false))
    | EMark (is_term, index, obj1) ->
      if is_term
      then _visit_term obj1 (return <== (mark true index))
      else _visit_obj obj1 (return <== (mark false index))
    | EMove (is_term, index, obj1) ->
      if is_term
      then _visit_term obj1 (return <== (move true index))
      else _visit_obj obj1 (return <== (move false index))
    | EComp (l, r, attr) ->
      if attr.fix
      then
        _rightmost l @@ fun lr ls ->
        _leftmost r @@ fun rl rs ->
        return (rs (ls (fix (comp lr rl attr.pad))))
      else
        _visit_obj l @@ fun l1 ->
        _visit_obj r @@ fun r1 ->
        return (comp l1 r1 attr.pad)
  and _visit_term obj return =
    match obj with
    | ENull -> return null
    | EText data -> return (text data)
    | EFix obj1 -> _visit_fix obj1 (return <== fix)
    | ENest (true, obj1) ->
      _visit_term obj1 (return <== (nest true))
    | EMark (true, index, obj1) ->
      _visit_term obj1 (return <== (mark true index))
    | EMove (true, index, obj1) ->
      _visit_term obj1 (return <== (move true index))
    | EGrp _ -> assert false (* Invariant *)
    | ESeq _ -> assert false (* Invariant *)
    | ENest (false, _) -> assert false (* Invariant *)
    | EMark (false, _, _) -> assert false (* Invariant *)
    | EMove (false, _, _) -> assert false (* Invariant *)
    | EComp _ -> assert false (* Invariant *)
  and _visit_fix obj return =
    match obj with
    | ENull -> return null
    | EText data -> return (text data)
    | EMark (_is_term, index, obj1) ->
      _visit_fix obj1 (return <== (mark true index))
    | EMove (_is_term, index, obj1) ->
      _visit_fix obj1 (return <== (move true index))
    | EComp (left, right, attr) ->
      _visit_fix left @@ fun left1 ->
      _visit_fix right @@ fun right1 ->
      return (comp left1 right1 attr.pad)
    | EFix _ -> assert false (* Invariant *)
    | EGrp _ -> assert false (* Invariant *)
    | ESeq _ -> assert false (* Invariant *)
    | ENest _ -> assert false (* Invariant *)
  and _leftmost obj return =
    let _local obj return defer =
      match obj with
      | ENull -> defer null return
      | EText data -> defer (text data) return
      | EFix obj1 ->
        _visit_fix obj1 @@ fun obj2 ->
        defer (fix obj2) return
      | EGrp obj1 -> _visit_obj obj1 (swap defer (return <== grp))
      | ESeq obj1 -> _visit_obj obj1 (swap defer (return <== seq))
      | ENest (is_term, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer (nest true layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer (nest false layout1) return
      | EMark (is_term, index, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer (mark true index layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer (mark false index layout1) return
      | EMove (is_term, index, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer (move true index layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer (move false index layout1) return
      | EComp (l, r, attr) ->
        if attr.fix
        then
          _leftmost r @@ fun rl rs ->
          _ambimost l
            (fun ll lr ls ->
              defer ll @@ fun ll1 ->
              return (rs (ls ll1 (fix (comp lr rl attr.pad)))))
            (fun ll ls ->
              defer ll @@ fun ll1 ->
              return (rs (ls (fix (comp ll1 rl attr.pad)))))
        else
          _visit_obj r @@ fun r1 ->
          _leftmost l @@ fun ll ls ->
          defer ll @@ fun ll1 ->
          return (comp (ls ll1) r1 attr.pad)
    in
    _local obj identity return
  and _rightmost obj return =
    let _local obj return defer =
      match obj with
      | ENull -> defer null return
      | EText data -> defer (text data) return
      | EFix obj1 ->
        _visit_fix obj1 @@ fun obj2 ->
        defer (fix obj2) return
      | EGrp obj1 -> _visit_obj obj1 (swap defer (return <== grp))
      | ESeq obj1 -> _visit_obj obj1 (swap defer (return <== seq))
      | ENest (is_term, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer (nest true layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer (nest false layout1) return
      | EMark (is_term, index, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer (mark true index layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer (mark false index layout1) return
      | EMove (is_term, index, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer (move true index layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer (move false index layout1) return
      | EComp (l, r, attr) ->
        if attr.fix
        then
          _rightmost l @@ fun lr ls ->
          _ambimost r
            (fun rl rr rs ->
              defer rr @@ fun rr1 ->
              return (rs (ls (fix (comp lr rl attr.pad))) rr1))
            (fun rr rs ->
              defer rr @@ fun rr1 ->
              return (rs (ls (fix (comp lr rr1 attr.pad)))))
        else
          _visit_obj l @@ fun l1 ->
          _rightmost r @@ fun rr rs ->
          defer rr @@ fun rr1 ->
          return (comp l1 (rs rr1) attr.pad)
    in
    _local obj identity return
  and _ambimost obj return_two return_one =
    let _local obj return defer_two defer_one =
      match obj with
      | ENull -> defer_one null return
      | EText data -> defer_one (text data) return
      | EFix obj1 ->
        _visit_fix obj1 @@ fun obj2 ->
        defer_one (fix obj2) return
      | EGrp obj1 -> _visit_obj obj1 (swap defer_one (return <== grp))
      | ESeq obj1 -> _visit_obj obj1 (swap defer_one (return <== seq))
      | ENest (is_term, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer_one (nest true layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer_one (nest false layout1) return
      | EMark (is_term, index, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer_one (mark true index layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer_one (mark false index layout1) return
      | EMove (is_term, index, obj1) ->
        if is_term
        then
          _visit_term obj1 @@ fun layout1 ->
          defer_one (move true index layout1) return
        else
          _visit_obj obj1 @@ fun layout1 ->
          defer_one (move false index layout1) return
      | EComp (l, r, attr) ->
        if attr.fix
        then
          _ambimost l
            (fun ll lr ls ->
              _ambimost r
                (fun rl rr rs ->
                  defer_two ll rr @@ fun ll1 rr1 ->
                  return (rs (ls ll1 (fix (comp lr rl attr.pad))) rr1))
                (fun rr rs ->
                  defer_two ll rr @@ fun ll1 rr1 ->
                  return (rs (ls ll1 (fix (comp lr rr1 attr.pad))))))
            (fun ll ls ->
              _ambimost r
                (fun rl rr rs ->
                  defer_two ll rr @@ fun ll1 rr1 ->
                  return (rs (ls (fix (comp ll1 rl attr.pad))) rr1))
                (fun rr rs ->
                  defer_two ll rr @@ fun ll1 rr1 ->
                  return (rs (ls (fix (comp ll1 rr1 attr.pad))))))
        else
          _leftmost l @@ fun ll ls ->
          _rightmost r @@ fun rr rs ->
          defer_two ll rr @@ fun ll1 rr1 ->
          return (comp (ls ll1) (rs rr1) attr.pad)
    in
    _local obj identity return_two return_one
  in
  _visit_doc doc return

type fixed_doc =
  | FEOD
  | FLine of fixed_obj
  | FEmpty of fixed_doc
  | FBreak of fixed_obj * fixed_doc
and fixed_obj =
  | FNull
  | FText of string
  | FFix of fixed_fix
  | FGrp of fixed_obj
  | FSeq of fixed_obj
  | FNest of bool * fixed_obj
  | FMark of bool * int * fixed_obj
  | FMove of bool * int * fixed_obj
  | FComp of fixed_obj * fixed_obj * bool
and fixed_fix =
  | FFNull
  | FFText of string
  | FFMark of int * fixed_fix
  | FFMove of int * fixed_fix
  | FFComp of fixed_fix * fixed_fix * bool

(* Propagate fix semantics *)
let _propagate doc return =
  let eod = FEOD in
  let line obj = FLine obj in
  let empty doc = FEmpty doc in
  let break obj doc = FBreak (obj, doc) in
  let null = FNull in
  let text data = FText data in
  let fix obj = FFix obj in
  let grp obj = FGrp obj in
  let seq obj = FSeq obj in
  let nest is_term obj = FNest (is_term, obj) in
  let mark is_term index obj = FMark (is_term, index, obj) in
  let move is_term index obj = FMove (is_term, index, obj) in
  let comp left right pad = FComp (left, right, pad) in
  let fix_null = FFNull in
  let fix_text data = FFText data in
  let fix_mark index obj = FFMark (index, obj) in
  let fix_move index obj = FFMove (index, obj) in
  let fix_comp left right pad = FFComp (left, right, pad) in
  let _cont_nest k obj = k (nest true obj) in
  let _cont_mark k index obj = k (mark true index obj) in
  let _cont_move k index obj = k (move true index obj) in
  let rec _visit_doc doc return =
    match doc with
    | DEOD -> return eod
    | DLine obj -> _visit_obj obj (return <== line)
    | DEmpty doc1 -> _visit_doc doc1 (return <== empty)
    | DBreak (obj, doc1) ->
      _visit_obj obj @@ fun obj1 ->
      _visit_doc doc1 (return <== (break obj1))
  and _visit_obj obj return =
    match obj with
    | DNull -> return null
    | DText data -> return (text data)
    | DFix obj1 ->
      _visit_fix true identity obj1 @@ fun header layout ->
      return (header (fix layout))
    | DGrp obj1 -> _visit_obj obj1 (return <== grp)
    | DSeq obj1 -> _visit_obj obj1 (return <== seq)
    | DNest (is_term, obj1) ->
      _visit_obj obj1 (return <== (nest is_term))
    | DMark (is_term, index, obj1) ->
      _visit_obj obj1 (return <== (mark is_term index))
    | DMove (is_term, index, obj1) ->
      _visit_obj obj1 (return <== (move is_term index))
    | DComp (left, right, pad) ->
      _visit_obj left @@ fun left1 ->
      _visit_obj right @@ fun right1 ->
      return (comp left1 right1 pad)
  and _visit_fix head header obj return =
    match obj with
    | DNull -> return header fix_null
    | DText data -> return header (fix_text data)
    | DFix obj1 -> _visit_fix head header obj1 return
    | DGrp obj1 -> _visit_fix head header obj1 return
    | DSeq obj1 -> _visit_fix head header obj1 return
    | DNest (_is_term, obj1) ->
      if head
      then _visit_fix true (_cont_nest header) obj1 return
      else _visit_fix false header obj1 return
    | DMark (_is_term, index, obj1) ->
      if head then _visit_fix true (_cont_mark header index) obj1 return else
      _visit_fix false header obj1 @@ fun header1 obj2 ->
      return header1 (fix_mark index obj2)
    | DMove (_is_term, index, obj1) ->
      if head then _visit_fix true (_cont_move header index) obj1 return else
      _visit_fix false header obj1 @@ fun header1 obj2 ->
      return header1 (fix_move index obj2)
    | DComp (left, right, pad) ->
      _visit_fix head header left @@ fun l_header left1 ->
      _visit_fix false identity right @@ fun _r_header right1 ->
      return l_header (fix_comp left1 right1 pad)
  in
  _visit_doc doc return

(* Make compositions right-associative *)
let _reassociate doc return =
  let eod = FEOD in
  let line obj = FLine obj in
  let empty doc = FEmpty doc in
  let break obj doc = FBreak (obj, doc) in
  let fix obj = FFix obj in
  let grp obj = FGrp obj in
  let seq obj = FSeq obj in
  let nest is_term obj = FNest (is_term, obj) in
  let mark is_term index obj = FMark (is_term, index, obj) in
  let move is_term index obj = FMove (is_term, index, obj) in
  let comp left right pad = FComp (left, right, pad) in
  let fix_mark index obj = FFMark (index, obj) in
  let fix_move index obj = FFMove (index, obj) in
  let fix_comp left right pad = FFComp (left, right, pad) in
  let rec _visit doc return =
    match doc with
    | FEOD -> return eod
    | FLine obj -> _visit_obj obj identity (return <== line)
    | FEmpty doc1 -> _visit doc1 (return <== empty)
    | FBreak (obj, doc1) ->
      _visit_obj obj identity @@ fun obj1 ->
      _visit doc1 (return <== (break obj1))
  and _visit_obj obj feed return =
    match obj with
    | FNull | FText _ -> return (feed obj)
    | FFix obj1 ->
      _visit_fix obj1 identity @@ fun obj2 ->
      return (feed (fix obj2))
    | FGrp obj1 ->
      _visit_obj obj1 identity @@ fun obj2 ->
      return (feed (grp obj2))
    | FSeq obj1 ->
      _visit_obj obj1 identity @@ fun obj2 ->
      return (feed (seq obj2))
    | FNest (is_term, obj1) ->
      _visit_obj obj1 identity @@ fun obj2 ->
      return (feed (nest is_term obj2))
    | FMark (is_term, index, obj1) ->
      _visit_obj obj1 identity @@ fun obj2 ->
      return (feed (mark is_term index obj2))
    | FMove (is_term, index, obj1) ->
      _visit_obj obj1 identity @@ fun obj2 ->
      return (feed (move is_term index obj2))
    | FComp (left, right, pad) ->
      _visit_obj right feed @@ fun right1 ->
      _visit_obj left (fun left1 -> comp left1 right1 pad) return
  and _visit_fix obj feed return =
    match obj with
    | FFNull | FFText _ -> return (feed obj)
    | FFMark (index, obj1) ->
      _visit_fix obj1 identity @@ fun obj2 ->
      return (feed (fix_mark index obj2))
    | FFMove (index, obj1) ->
      _visit_fix obj1 identity @@ fun obj2 ->
      return (feed (fix_move index obj2))
    | FFComp (left, right, pad) ->
      _visit_fix right feed @@ fun right1 ->
      _visit_fix left (fun left1 -> fix_comp left1 right1 pad) return
  in
  _visit doc return

type doc =
  | SEOD
  | SLine of doc_obj
  | SEmpty of doc
  | SBreak of doc_obj * doc
and doc_obj =
  | SNull
  | SText of string
  | SFix of doc_obj_fix
  | SGrp of doc_obj
  | SSeq of doc_obj
  | SNest of doc_obj
  | SMark of int * doc_obj
  | SMove of int * doc_obj
  | SComp of doc_obj * doc_obj * bool
and doc_obj_fix =
  | SFNull
  | SFText of string
  | SFMark of int * doc_obj_fix
  | SFMove of int * doc_obj_fix
  | SFComp of doc_obj_fix * doc_obj_fix * bool

(* Float nests back up *)
let _retract doc return =
  let eod = SEOD in
  let line obj = SLine obj in
  let empty doc = SEmpty doc in
  let break obj doc = SBreak (obj, doc) in
  let null = SNull in
  let text data = SText data in
  let fix obj = SFix obj in
  let grp obj = SGrp obj in
  let seq obj = SSeq obj in
  let nest obj = SNest obj in
  let mark index obj = SMark (index, obj) in
  let move index obj = SMove (index, obj) in
  let comp left right pad = SComp (left, right, pad) in
  let fix_null = SFNull in
  let fix_text data = SFText data in
  let fix_mark index obj = SFMark (index, obj) in
  let fix_move index obj = SFMove (index, obj) in
  let fix_comp left right pad = SFComp (left, right, pad) in
  let rec _gen_nests count obj =
    if count <= 0 then obj else
    _gen_nests (count - 1) (nest obj)
  in
  let _depth_join l r return =
    let c = min l r in
    return c (l - c) (r - c)
  in
  let rec _visit_doc doc return =
    match doc with
    | FEOD -> return eod
    | FLine obj ->
      _visit_obj 0 obj @@ fun depth obj1 ->
      return (line (_gen_nests depth obj1))
    | FEmpty doc1 -> _visit_doc doc1 (return <== empty)
    | FBreak (obj, doc1) ->
      _visit_obj 0 obj @@ fun depth obj1 ->
      _visit_doc doc1 (return <== (break (_gen_nests depth obj1)))
  and _visit_obj depth obj return =
    match obj with
    | FNull -> return depth null
    | FText data -> return depth (text data)
    | FFix obj1 -> _visit_fix obj1 (return depth <== fix)
    | FGrp obj1 ->
      _visit_obj depth obj1 @@ fun depth1 obj2 ->
      return depth1 (grp obj2)
    | FSeq obj1 ->
      _visit_obj depth obj1 @@ fun depth1 obj2 ->
      return depth1 (seq obj2)
    | FNest (_is_term, obj1) ->
      _visit_obj (depth + 1) obj1 return
    | FMark (_is_term, index, obj1) ->
      _visit_obj depth obj1 @@ fun depth1 obj2 ->
      return 0 (mark index (_gen_nests depth1 obj2))
    | FMove (_is_term, index, obj1) ->
      _visit_obj depth obj1 @@ fun depth1 obj2 ->
      return 0 (move index (_gen_nests depth1 obj2))
    | FComp (left, right, pad) ->
      _visit_obj depth left @@ fun l_depth left1 ->
      _visit_obj depth right @@ fun r_depth right1 ->
      _depth_join l_depth r_depth @@ fun depth1 l_depth1 r_depth1 ->
      return depth1 (comp
        (_gen_nests l_depth1 left1)
        (_gen_nests r_depth1 right1)
        pad)
  and _visit_fix obj return =
    match obj with
    | FFNull -> return fix_null
    | FFText data -> return (fix_text data)
    | FFMark (index, obj1) -> _visit_fix obj1 (return <== (fix_mark index))
    | FFMove (index, obj1) -> _visit_fix obj1 (return <== (fix_move index))
    | FFComp (left, right, pad) ->
      _visit_fix left @@ fun left1 ->
      _visit_fix right @@ fun right1 ->
      return (fix_comp left1 right1 pad)
  in
  _visit_doc doc return

(* Clean up identities *)
let _cleanup doc return =
  let eod = SEOD in
  let line obj = SLine obj in
  let empty doc = SEmpty doc in
  let break obj doc = SBreak (obj, doc) in
  let null = SNull in
  let text data = SText data in
  let fix obj = SFix obj in
  let grp obj = SGrp obj in
  let seq obj = SSeq obj in
  let nest obj = SNest obj in
  let mark index obj = SMark (index, obj) in
  let move index obj = SMove (index, obj) in
  let comp left right pad = SComp (left, right, pad) in
  let fix_mark index obj = SFMark (index, obj) in
  let fix_move index obj = SFMove (index, obj) in
  let fix_comp left right pad = SFComp (left, right, pad) in
  let rec _visit_doc doc return =
    match doc with
    | SEOD -> return eod
    | SLine obj ->
      _visit_obj obj @@ fun _is_term _is_null obj1 ->
      return (line obj1)
    | SEmpty doc1 -> _visit_doc doc1 (return <== empty)
    | SBreak (obj, doc1) ->
      _visit_obj obj @@ fun _is_term _is_null obj1 ->
      _visit_doc doc1 (return <== (break obj1))
  and _visit_obj obj return =
    match obj with
    | SNull -> return true true obj
    | SText data ->
      let n = String.length data in
      return true (n = 0) obj
    | SFix obj1 ->
      _visit_fix obj1 @@ fun is_term is_null obj2 ->
      if is_term
      then _unfix obj2 (return true is_null)
      else return true false (fix obj2)
    | SGrp obj1 ->
      _visit_obj obj1 @@ fun is_term is_null obj2 ->
      if is_term
      then return true is_null obj2
      else return false is_null (grp obj2)
    | SSeq obj1 ->
      _visit_obj obj1 @@ fun is_term is_null obj2 ->
      if is_term
      then return true is_null obj2
      else return false is_null (seq obj2)
    | SNest obj1 ->
      _visit_obj obj1 @@ fun is_term _is_null obj2 ->
      return is_term false (nest obj2)
    | SMark (index, obj1) ->
      _visit_obj obj1 @@ fun is_term _is_null obj2 ->
      return is_term false (mark index obj2)
    | SMove (index, obj1) ->
      _visit_obj obj1 @@ fun is_term _is_null obj2 ->
      return is_term false (move index obj2)
    | SComp (left, right, true) ->
      _visit_obj left @@ fun _l_is_term _l_is_null left1 ->
      _visit_obj right @@ fun _r_is_term _r_is_null right1 ->
      return false false (comp left1 right1 true)
    | SComp (left, right, false) ->
      _visit_obj left @@ fun l_is_term l_is_null left1 ->
      _visit_obj right @@ fun r_is_term r_is_null right1 ->
      if l_is_null then return r_is_term r_is_null right1 else
      if r_is_null then return l_is_term l_is_null left1 else
      return false false (comp left1 right1 false)
  and _visit_fix obj return =
    match obj with
    | SFNull -> return true true obj
    | SFText data ->
      let n = String.length data in
      return true (n = 0) obj
    | SFMark (index, obj1) ->
      _visit_fix obj1 @@ fun is_term _is_null obj2 ->
      return is_term false (fix_mark index obj2)
    | SFMove (index, obj1) ->
      _visit_fix obj1 @@ fun is_term _is_null obj2 ->
      return is_term false (fix_move index obj2)
    | SFComp (left, right, true) ->
      _visit_fix left @@ fun _l_is_term _l_is_null left1 ->
      _visit_fix right @@ fun _r_is_term _r_is_null right1 ->
      return false false (fix_comp left1 right1 true)
    | SFComp (left, right, false) ->
      _visit_fix left @@ fun l_is_term l_is_null left1 ->
      _visit_fix right @@ fun r_is_term r_is_null right1 ->
      if l_is_null then return r_is_term r_is_null right1 else
      if r_is_null then return l_is_term l_is_null left1 else
      return false false (fix_comp left1 right1 false)
  and _unfix obj return =
    match obj with
    | SFNull -> return null
    | SFText data -> return (text data)
    | SFMark (index, obj1) -> _unfix obj1 (return <== (mark index))
    | SFMove (index, obj1) -> _unfix obj1 (return <== (move index))
    | SFComp _ -> assert false (* Invariant *)
  in
  _visit_doc doc return

let compile eDSL return =
  _collapse eDSL @@ fun eDSL1 ->
  _unpack eDSL1 @@ fun eDSL2 ->
  _linearize eDSL2 @@ fun doc ->
  _expand doc @@ fun doc1 ->
  _desugar doc1 @@ fun doc2 ->
  _propagate doc2 @@ fun doc3 ->
  _reassociate doc3 @@ fun doc4 ->
  _retract doc4 @@ fun doc5 ->
  _cleanup doc5 return

type metric =
  { width : int
  ; next_comp : int
  }

let _measure tab head pos marks obj return =
  let _equal left right = left = right in
  let _fail () = assert false (* Invariant *) in
  let _null_metric () =
    { width = 0
    ; next_comp = 0
    }
  in
  let _metric_from_width width =
    { width = width
    ; next_comp = width
    }
  in
  let rec _measure_obj head pos marks obj return =
    match obj with
    | SNull -> return marks (_null_metric ())
    | SText data ->
      let w = String.length data in
      let m = _metric_from_width w in
      return marks m
    | SFix obj1 ->
      _measure_obj_fix pos marks obj1 @@ fun marks1 w ->
      let m = _metric_from_width w in
      return marks1 m
    | SGrp obj1 ->
      _measure_obj head pos marks obj1 @@ fun marks1 m ->
      let m1 = { m with next_comp = m.width } in
      return marks1 m1
    | SSeq obj1 ->
      _measure_obj head pos marks obj1 @@ fun marks1 m ->
      return marks1 m
    | SNest obj1 ->
      let pos1 = if head then pos + tab else pos in
      _measure_obj head pos1 marks obj1 @@ fun marks1 m ->
      let m1 = { m with width = if head then m.width + tab else m.width } in
      return marks1 m1
    | SMark (index, obj1) ->
      Env.bind index pos marks @@ fun marks1 ->
      _measure_obj head pos marks1 obj1 @@ fun marks2 m ->
      return marks2 m
    | SMove (index, obj1) ->
      Env.lookup _equal index marks _fail @@ fun pos1 ->
      let pos2 = max pos pos1 in
      _measure_obj head pos2 marks obj1 @@ fun marks1 m ->
      let m1 = { m with width = (pos2 - pos) + m.width } in
      return marks1 m1
    | SComp (left, right, pad) ->
      _measure_obj head pos marks left @@ fun marks1 ml ->
      let pos1 = pos + ml.width in
      let pos2 = if pad then pos1 + 1 else pos1 in
      _measure_obj false pos2 marks1 right @@ fun marks2 mr ->
      let m =
        { width = if pad
          then ml.width + mr.width + 1
          else ml.width + mr.width
        ; next_comp = ml.next_comp
        }
      in
      return marks2 m
  and _measure_obj_fix pos marks obj_fix return =
    match obj_fix with
    | SFNull -> return marks 0
    | SFText data ->
      let w = String.length data in
      return marks w
    | SFMark (index, obj_fix1) ->
      Env.bind index pos marks @@ fun marks1 ->
      _measure_obj_fix pos marks1 obj_fix1 @@ fun marks2 w ->
      return marks2 w
    | SFMove (index, obj_fix1) ->
      Env.lookup _equal index marks _fail @@ fun pos1 ->
      let pos2 = max pos pos1 in
      _measure_obj_fix pos2 marks obj_fix1 @@ fun marks1 w ->
      let w1 = (pos2 - pos) + w in
      return marks1 w1
    | SFComp (left, right, pad) ->
      _measure_obj_fix pos marks left @@ fun marks1 a ->
      let pos1 = pos + a in
      let pos2 = if pad then pos1 + 1 else pos1 in
      _measure_obj_fix pos2 marks1 right @@ fun marks2 b ->
      let w = if pad then a + b + 1 else a + b in
      return marks2 w
  in
  _measure_obj head pos marks obj return

type state =
  { head : bool
  ; break : bool
  ; lvl : int
  ; pos : int
  ; marks : (int, int) Env.env
  }

let init () =
  { head = true
  ; break = false
  ; lvl = 0
  ; pos = 0
  ; marks = Env.empty
  }

let reset state return =
  return
  { head = true
  ; break = false
  ; lvl = 0
  ; pos = 0
  ; marks = state.marks
  }

let get_head state return = return state.head
let set_head head state return =
  return { state with head = head }

let get_break state return = return state.break
let set_break break state return =
  return { state with break = break }

let get_lvl state return = return state.lvl
let set_lvl lvl state return =
  return { state with lvl = lvl }
let indent tab state return =
  if not state.head then return { state with lvl = state.lvl + tab} else
  return { state with lvl = state.lvl + tab; pos = state.pos + tab }

let get_pos state return = return state.pos
let inc_pos n state return =
  return { state with pos = state.pos + n }

let set_mark index state return =
  Env.bind index state.pos state.marks @@ fun marks1 ->
  return { state with marks = marks1 }

let move_to index state return =
  let _equal l r = l = r in
  let _fail () = assert false (* Invariant *) in
  Env.lookup _equal index state.marks _fail @@ fun pos ->
  return { state with pos = max state.pos pos }

let measure tab state obj return =
  _measure tab state.head state.pos state.marks obj @@ fun marks1 m ->
  return m { state with pos = state.pos + m.width; marks = marks1 }

let render doc tab width return =
  let open Printf in
  let _whitespace n = String.make n ' ' in
  let rec _render_doc doc state return =
    reset state @@ fun state1 ->
    match doc with
    | SEOD -> return "" state
    | SLine obj -> _render_obj obj state1 return
    | SEmpty doc1 ->
      _render_doc doc1 state1 @@ fun doc2 state2 ->
      return (sprintf "\n%s" doc2) state2
    | SBreak (obj, doc1) ->
      _render_obj obj state1 @@ fun obj1 state2 ->
      _render_doc doc1 state2 @@ fun doc2 state3 ->
      return (sprintf "%s\n%s" obj1 doc2) state3
  and _render_obj obj state return =
    match obj with
    | SNull -> return "" state
    | SText data ->
      let n = String.length data in
      inc_pos n state (return data)
    | SFix obj1 -> _render_obj_fix obj1 state return
    | SGrp obj1 ->
      set_break false state @@ fun state1 ->
      _render_obj obj1 state1 return
    | SSeq obj1 ->
      get_pos state @@ fun pos ->
      measure tab state obj1 @@ fun m _state ->
      set_break (width < pos + m.width) state @@ fun state1 ->
      _render_obj obj1 state1 return
    | SNest obj1 ->
      get_head state @@ fun head ->
      get_lvl state @@ fun lvl ->
      indent tab state @@ fun state1 ->
      _render_obj obj1 state1 @@ fun obj2 state2 ->
      set_lvl lvl state2 @@ fun state3 ->
      let padding = _whitespace (if head then tab else 0) in
      return (sprintf "%s%s" padding obj2) state3
    | SMark (index, obj1) ->
      set_mark index state @@ fun state1 ->
      _render_obj obj1 state1 return
    | SMove (index, obj1) ->
      get_pos state @@ fun pos ->
      move_to index state @@ fun state1 ->
      get_pos state1 @@ fun pos1 ->
      _render_obj obj1 state1 @@ fun obj2 state2 ->
      let padding = _whitespace (max 0 (pos1 - pos)) in
      return (sprintf "%s%s" padding obj2) state2
    | SComp (left, right, pad) ->
      let _linebreak state =
        get_lvl state @@ fun lvl ->
        get_break state @@ fun break ->
        _render_obj left state @@ fun left1 state1 ->
        reset state1 @@ fun state2 ->
        indent lvl state2 @@ fun state3 ->
        set_break break state3 @@ fun state4 ->
        _render_obj right state4 @@ fun right1 state5 ->
        let padding = _whitespace lvl in
        return (sprintf "%s\n%s%s" left1 padding right1) state5
      in
      get_break state @@ fun break ->
      if break then _linebreak state else
      get_pos state @@ fun pos ->
      measure tab state left @@ fun ml l_state ->
      set_head false l_state @@ fun l_state1 ->
      inc_pos (if pad then 1 else 0) l_state1 @@ fun l_state2 ->
      measure tab l_state2 right @@ fun mr _r_state ->
      let p1 = pos + ml.width in
      let p2 = if pad then p1 + 1 else p1 in
      let p3 = p2 + mr.width in
      if p3 <= width then _render_obj_inline obj state return else
      if p1 = width then _linebreak state else
      if p2 = width then _linebreak state else
      if width < p1 then _linebreak state else
      if width < p2 + mr.next_comp then _linebreak state else
      _render_obj left state @@ fun left1 state1 ->
      set_head false state1 @@ fun state2 ->
      inc_pos (if pad then 1 else 0) state2 @@ fun state3 ->
      _render_obj right state3 @@ fun right1 state4 ->
      let padding = if pad then " " else "" in
      return (sprintf "%s%s%s" left1 padding right1) state4
  and _render_obj_fix obj_fix state return =
    match obj_fix with
    | SFNull -> return "" state
    | SFText data ->
      let n = String.length data in
      inc_pos n state (return data)
    | SFMark (index, obj_fix1) ->
      set_mark index state @@ fun state1 ->
      _render_obj_fix obj_fix1 state1 return
    | SFMove (index, obj_fix1) ->
      get_pos state @@ fun pos ->
      move_to index state @@ fun state1 ->
      get_pos state1 @@ fun pos1 ->
      _render_obj_fix obj_fix1 state1 @@ fun obj2 state2 ->
      let padding = _whitespace (max 0 (pos1 - pos)) in
      return (sprintf "%s%s" padding obj2) state2
    | SFComp (left, right, pad) ->
      _render_obj_fix left state @@ fun left1 state1 ->
      inc_pos (if pad then 1 else 0) state1 @@ fun state2 ->
      set_head false state2 @@ fun state3 ->
      _render_obj_fix right state3 @@ fun right1 state4 ->
      let padding = _whitespace (if pad then 1 else 0) in
      return (sprintf "%s%s%s" left1 padding right1) state4
  and _render_obj_inline obj state return =
    match obj with
    | SNull -> return "" state
    | SText data ->
      let n = String.length data in
      inc_pos n state (return data)
    | SFix obj1 -> _render_obj_fix obj1 state return
    | SGrp obj1 | SSeq obj1 ->
      _render_obj_inline obj1 state return
    | SNest obj1 ->
      get_head state @@ fun head ->
      get_lvl state @@ fun lvl ->
      indent tab state @@ fun state1 ->
      _render_obj_inline obj1 state1 @@ fun obj2 state2 ->
      set_lvl lvl state2 @@ fun state3 ->
      let padding = _whitespace (if head then tab else 0) in
      return (sprintf "%s%s" padding obj2) state3
    | SMark (index, obj1) ->
      set_mark index state @@ fun state1 ->
      _render_obj_inline obj1 state1 return
    | SMove (index, obj1) ->
      get_pos state @@ fun pos ->
      move_to index state @@ fun state1 ->
      get_pos state1 @@ fun pos1 ->
      _render_obj_inline obj1 state1 @@ fun obj2 state2 ->
      let padding = _whitespace (max 0 (pos1 - pos)) in
      return (sprintf "%s%s" padding obj2) state2
    | SComp (left, right, pad) ->
      _render_obj_inline left state @@ fun left1 state1 ->
      inc_pos (if pad then 1 else 0) state1 @@ fun state2 ->
      set_head false state2 @@ fun state3 ->
      _render_obj_inline right state3 @@ fun right1 state4 ->
      let padding = _whitespace (if pad then 1 else 0) in
      return (sprintf "%s%s%s" left1 padding right1) state4
  in
  let state = init () in
  _render_doc doc state @@ fun result _state1 ->
  return result
