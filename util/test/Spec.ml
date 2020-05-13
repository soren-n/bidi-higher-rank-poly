open Util
open Infix
open Typeset

(*
  Specification implementation of the typeset layout algorithm.
  Achieved via fixpoint algorithms that do local transformations;
    i.e. not efficient, but correct.
*)

type layout =
  | Null
  | Text of string
  | Fix of layout
  | Grp of layout
  | Seq of layout
  | Nest of layout
  | Mark of int * layout
  | Move of int * layout
  | Line of layout * layout
  | Comp of layout * layout * bool

let null = Null
let text data = Text data
let fix layout = Fix layout
let grp layout = Grp layout
let seq layout = Seq layout
let nest layout = Nest layout
let mark index layout = Mark (index, layout)
let move index layout = Move (index, layout)
let line left right = Line (left, right)
let comp left right pad = Comp (left, right, pad)

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
    | Mark (index, layout1) ->
      _visit layout1 (return <== (sprintf "(Mark %d %s)" index))
    | Move (index, layout1) ->
      _visit layout1 (return <== (sprintf "(Move %d %s)" index))
    | Line (left, right) ->
      _visit left @@ fun left1 ->
      _visit right @@ fun right1 ->
      return (sprintf "(Line %s\n%s)" left1 right1)
    | Comp (left, right, pad) ->
      _visit left @@ fun left1 ->
      _visit right @@ fun right1 ->
      return (sprintf "(Comp %s %s %b)" left1 right1 pad)
  in
  _visit layout return

let desugar doc return =
  let null = Null in
  let text data = Text data in
  let fix layout = Fix layout in
  let grp layout = Grp layout in
  let seq layout = Seq layout in
  let nest layout = Nest layout in
  let mark index layout = Mark (index, layout) in
  let move index layout = Move (index, layout) in
  let line left right = Line (left, right) in
  let comp left right pad = Comp (left, right, pad) in
  let rec _visit_doc doc return =
    match doc with
    | SEOD -> return null
    | SLine obj -> _visit_obj obj return
    | SEmpty doc1 -> _visit_doc doc1 (return <== (line null))
    | SBreak (obj, doc1) ->
      _visit_obj obj @@ fun obj1 ->
      _visit_doc doc1 (return <== (line obj1))
  and _visit_obj obj return =
    match obj with
    | SNull -> return null
    | SText data -> return (text data)
    | SFix obj1 -> _visit_fix obj1 (return <== fix)
    | SGrp obj1 -> _visit_obj obj1 (return <== grp)
    | SSeq obj1 -> _visit_obj obj1 (return <== seq)
    | SNest obj1 -> _visit_obj obj1 (return <== nest)
    | SMark (index, obj1) -> _visit_obj obj1 (return <== (mark index))
    | SMove (index, obj1) -> _visit_obj obj1 (return <== (move index))
    | SComp (left, right, pad) ->
      _visit_obj left @@ fun left1 ->
      _visit_obj right @@ fun right1 ->
      return (comp left1 right1 pad)
  and _visit_fix obj return =
    match obj with
    | SFNull -> return null
    | SFText data -> return (text data)
    | SFMark (index, obj1) -> _visit_fix obj1 (return <== (mark index))
    | SFMove (index, obj1) -> _visit_fix obj1 (return <== (move index))
    | SFComp (left, right, pad) ->
      _visit_fix left @@ fun left1 ->
      _visit_fix right @@ fun right1 ->
      return (comp left1 right1 pad)
  in
  _visit_doc doc return

let _equal left right = left = right
let _fail () = assert false (* Invariant *)

let normalize layout return =
  let rec _visit layout head fixed return =
    match layout with
    | Null | Text _ -> return false layout
    | Fix Null -> return true null
    | Fix (Text data) -> return true (text data)
    | Fix (Nest layout1) ->
      _visit layout1 head true @@ fun _change layout2 ->
      return true (nest (fix layout2))
    | Fix (Line (left, right)) ->
      _visit left head true @@ fun _l_change left1 ->
      _visit right true true @@ fun _r_change right1 ->
      if fixed
      then return true (line left1 right1)
      else return true (line (fix left1) (fix right1))
    | Fix layout1 ->
      _visit layout1 head true @@ fun change layout2 ->
      if fixed then return true layout2 else
      if not change then return false layout else
      return true (fix layout2)
    | Grp Null -> return true null
    | Grp (Text data) -> return true (text data)
    | Grp (Line (left, right)) ->
      _visit left head fixed @@ fun _l_change left1 ->
      _visit right true fixed @@ fun _r_change right1 ->
      if fixed
      then return true (line left1 right1)
      else return true (line (grp left1) (grp right1))
    | Grp layout1 ->
      _visit layout1 head fixed @@ fun change layout2 ->
      if fixed then return true layout2 else
      if not change then return false layout else
      return true (grp layout2)
    | Seq Null -> return true null
    | Seq (Text data) -> return true (text data)
    | Seq (Line (left, right)) ->
      _visit_elim left @@ fun left1 ->
      _visit_elim right @@ fun right1 ->
      return true (line left1 right1)
    | Seq layout1 ->
      _visit layout1 head fixed @@ fun change layout2 ->
      if fixed then return true layout2 else
      if not change then return false layout else
      return true (seq layout2)
    | Nest (Line (left, right)) ->
      _visit left head fixed @@ fun _l_change left1 ->
      _visit right true fixed @@ fun _r_change right1 ->
      begin match head, fixed with
      | false, true -> return true (line left1 (nest right1))
      | _, _ -> return true (line (nest left1) (nest right1))
      end
    | Nest layout1 ->
      _visit layout1 head fixed @@ fun change layout2 ->
      if not head && fixed then return true layout2 else
      if not change then return false layout else
      return true (nest layout2)
    | Mark (index, Line (left, right)) ->
      _visit left head fixed @@ fun _l_change left1 ->
      _visit right true fixed @@ fun _r_change right1 ->
      return true (line (mark index left1) (move index right1))
    | Mark (index, layout1) ->
      _visit layout1 head fixed @@ fun change layout2 ->
      if not change then return false layout else
      return true (mark index layout2)
    | Move (index, Line (left, right)) ->
      _visit left head fixed @@ fun _l_change left1 ->
      _visit right true fixed @@ fun _r_change right1 ->
      return true (line (move index left1) (move index right1))
    | Move (index, layout1) ->
      _visit layout1 head fixed @@ fun change layout2 ->
      if not change then return false layout else
      return true (move index layout2)
    | Line (Line (ll, lr), r) ->
      _visit ll head fixed @@ fun _ll_change ll1 ->
      _visit lr true fixed @@ fun _lr_change lr1 ->
      _visit r true fixed @@ fun _r_change r1 ->
      return true (line ll1 (line lr1 r1))
    | Line (left, right) ->
      _visit left head fixed @@ fun l_change left1 ->
      _visit right true fixed @@ fun r_change right1 ->
      let change = l_change || r_change in
      if not change then return false layout else
      return true (line left1 right1)
    | Comp (Null, right, false) -> return true right
    | Comp (left, Null, false) -> return true left
    | Comp (Text "", right, false) -> return true right
    | Comp (left, Text "", false) -> return true left
    | Comp (Line (ll, lr), r, pad) ->
      _visit ll head fixed @@ fun _ll_change ll1 ->
      _visit lr true fixed @@ fun _lr_change lr1 ->
      _visit r true fixed @@ fun _r_change r1 ->
      return true (line ll1 (comp lr1 r1 pad))
    | Comp (l, Line (rl, rr), pad) ->
      _visit l head fixed @@ fun _l_change l1 ->
      _visit rl false fixed @@ fun _rl_change rl1 ->
      _visit rr true fixed @@ fun _rr_change rr1 ->
      return true (line (comp l1 rl1 pad) rr1)
    | Comp (Comp (ll, lr, l_pad), r, r_pad) ->
      _visit ll head fixed @@ fun _ll_change ll1 ->
      _visit lr false fixed @@ fun _l1_change lr1 ->
      _visit r false fixed @@ fun _r1_change r1 ->
      return true (comp ll1 (comp lr1 r1 r_pad) l_pad)
    | Comp (left, right, pad) ->
      _visit left head fixed @@ fun l_change left1 ->
      _visit right false fixed @@ fun r_change right1 ->
      let change = l_change || r_change in
      if not change then return false layout else
      return true (comp left1 right1 pad)
  and _visit_elim layout return =
    match layout with
    | Nest layout1 -> _visit_elim layout1 (return <== nest)
    | Mark (index, layout1) ->
      _visit_elim layout1 (return <== (mark index))
    | Move (index, layout1) ->
      _visit_elim layout1 (return <== (move index))
    | Line (left, right) ->
      _visit_elim left @@ fun left1 ->
      _visit_elim right @@ fun right1 ->
      return (line left1 right1)
    | Comp (left, right, _pad) ->
      _visit_elim left @@ fun left1 ->
      _visit_elim right @@ fun right1 ->
      return (line left1 right1)
    | _ -> return layout
  in
  let rec _loop layout =
    _visit layout true false @@ fun change layout1 ->
    if change
    then _loop layout1
    else return layout1
  in
  _loop layout

let solve layout tab width return =
  let rec _visit layout head break pos marks return =
    match layout with
    | Null | Text _ -> return false marks layout
    | Fix layout1 ->
      _measure layout1 true pos marks @@ fun _pos1 marks1 ->
      return false marks1 (fix layout1)
    | Grp layout1 ->
      _visit layout1 head false pos marks @@ fun change marks1 layout2 ->
      if not change then return false marks1 layout else
      return true marks1 (grp layout2)
    | Seq layout1 ->
      _measure layout1 head pos marks @@ fun pos1 _marks1 ->
      let break1 = width < pos1 in
      _visit layout1 head break1 pos marks @@ fun change marks2 layout2 ->
      if not change then return false marks2 layout else
      return true marks2 (seq layout2)
    | Nest layout1 ->
      let pos1 = if head then pos + tab else pos in
      _visit layout1 head break pos1 marks @@ fun change marks1 layout2 ->
      if not change then return false marks1 layout else
      return true marks1 (nest layout2)
    | Mark (index, layout1) ->
      Env.bind index pos marks @@ fun marks1 ->
      _visit layout1 head break pos marks1 @@ fun change marks2 layout2 ->
      if not change then return false marks2 layout else
      return true marks2 (mark index layout2)
    | Move (index, layout1) ->
      Env.lookup _equal index marks _fail @@ fun pos1 ->
      let pos2 = max pos pos1 in
      _visit layout1 head break pos2 marks @@ fun change marks1 layout2 ->
      if not change then return false marks1 layout else
      return true marks1 (move index layout2)
    | Line (left, right) ->
      _visit left head break pos marks @@ fun l_change marks1 left1 ->
      if l_change then return true marks1 (line left1 right) else
      _visit right true break 0 marks1 @@ fun r_change marks2 right1 ->
      if not r_change then return false marks2 layout else
      return true marks2 (line left1 right1)
    | Comp (left, right, pad) ->
      if break then return true marks (line left right) else
      _measure left head pos marks @@ fun pos1 marks1 ->
      let pos2 = if pad then pos1 + 1 else pos1 in
      _measure right false pos2 marks1 @@ fun pos3 marks2 ->
      if pos3 <= width then return false marks2 layout else
      if width = pos2 then return true marks2 (line left right) else
      if width = pos1 then return true marks2 (line left right) else
      if width < pos1 then return true marks2 (line left right) else
      _next_comp right pos2 marks1 @@ fun pos3 ->
      if width < pos3 then return true marks2 (line left right) else
      _visit right false false pos2 marks1 @@ fun change marks3 right1 ->
      if not change then return false marks3 layout else
      return true marks3 (comp left right1 pad)
  and _next_comp layout pos marks return =
    match layout with
    | Null -> return pos
    | Text data -> return (pos + (String.length data))
    | Fix layout1 ->
      _measure layout1 false pos marks @@ fun pos1 _marks ->
      return pos1
    | Seq layout1 -> _next_comp layout1 pos marks return
    | Grp layout1 ->
      _measure layout1 false pos marks @@ fun pos1 _marks1 ->
      return pos1
    | Nest layout1 -> _next_comp layout1 pos marks return
    | Mark (index, layout1) ->
      Env.bind index pos marks @@ fun marks1 ->
      _next_comp layout1 pos marks1 return
    | Move (index, layout1) ->
      Env.lookup _equal index marks _fail @@ fun pos1 ->
      let pos2 = max pos pos1 in
      _next_comp layout1 pos2 marks return
    | Line (left, _right) -> _next_comp left pos marks return
    | Comp (left, _right, _pad) -> _next_comp left pos marks return
  and _measure layout head pos marks return =
    match layout with
    | Null -> return pos marks
    | Text data ->
      let pos1 = pos + (String.length data) in
      return pos1 marks
    | Fix layout1 | Seq layout1 | Grp layout1 ->
      _measure layout1 head pos marks return
    | Nest layout1 ->
      let pos1 = if head then pos + tab else pos in
      _measure layout1 head pos1 marks return
    | Mark (index, layout1) ->
      Env.bind index pos marks @@ fun marks1 ->
      _measure layout1 head pos marks1 return
    | Move (index, layout1) ->
      Env.lookup _equal index marks _fail @@ fun pos1 ->
      let pos2 = max pos pos1 in
      _measure layout1 head pos2 marks return
    | Line _ -> assert false (* Invariant *)
    | Comp (left, right, true) ->
      _measure left head pos marks @@ fun pos1 marks1 ->
      _measure right false (pos1 + 1) marks1 return
    | Comp (left, right, false) ->
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
  normalize layout _loop

let render layout tab width return =
  let open Printf in
  let rec _print layout head pos marks return =
    match layout with
    | Null -> return pos marks ""
    | Text data ->
      let pos1 = pos + (String.length data) in
      return pos1 marks data
    | Fix layout1 | Seq layout1 | Grp layout1 ->
      _print layout1 head pos marks return
    | Nest layout1 ->
      let pos1 = if head then pos + tab else pos in
      _print layout1 head pos1 marks @@ fun pos2 marks1 layout2 ->
      if not head then return pos2 marks1 layout2 else
      let indent = String.make tab ' ' in
      return pos2 marks1 (sprintf "%s%s" indent layout2)
    | Mark (index, layout1) ->
      Env.bind index pos marks @@ fun marks1 ->
      _print layout1 head pos marks1 return
    | Move (index, layout1) ->
      Env.lookup _equal index marks _fail @@ fun pos1 ->
      let pos2 = max pos pos1 in
      _print layout1 head pos2 marks @@ fun pos3 marks1 layout2 ->
      let padding = String.make (max 0 (pos1 - pos)) ' ' in
      return pos3 marks1 (sprintf "%s%s" padding layout2)
    | Line (left, right) ->
      _print left head pos marks @@ fun _pos1 marks1 left1 ->
      _print right true 0 marks1 @@ fun pos2 marks2 right1 ->
      return pos2 marks2 (sprintf "%s\n%s" left1 right1)
    | Comp (left, right, pad) ->
      _print left head pos marks @@ fun pos1 marks1 left1 ->
      let pos2 = if pad then pos1 + 1 else pos1 in
      _print right false pos2 marks1 @@ fun pos3 marks2 right1 ->
      let padding = if pad then " " else "" in
      return pos3 marks2 (sprintf "%s%s%s" left1 padding right1)
  in
  solve layout tab width @@ fun layout1 ->
  _print layout1 true 0 Env.empty @@ fun _pos _marks result ->
  return result
