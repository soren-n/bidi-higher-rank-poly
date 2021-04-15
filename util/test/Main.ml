open Util
open Typeset
open Spec
open EDSL

let _normal_form layout =
  let rec _spine layout =
    match layout with
    | Null | Text _ -> true
    | Seq layout1 | Grp layout1
    | Fix layout1 | Nest layout1
    | Pack (_, layout1) ->
      _term layout1
    | Line (left, right) ->
      (_term left) &&
      (_spine right)
    | Comp (left, right, _pad, _fix) ->
      (_term left) &&
      (_term right)
  and _term layout =
    match layout with
    | Null | Text _ -> true
    | Seq layout1 | Grp layout1
    | Nest layout1 | Fix layout1
    | Pack (_, layout1) ->
      _term layout1
    | Line _ -> false
    | Comp (left, right, _pad, _fix) ->
      (_term left) &&
      (_term right)
  in
  _spine layout

let _num_critical_comps tab marks layout return =
  let _equal left right = left = right in
  let _fail () = assert false (* Invariant *) in
  let rec _visit head pos marks layout result return =
    match layout with
    | Null -> return result pos marks
    | Text data -> return result (pos + String.length data) marks
    | Fix layout1 -> _visit_fix head pos marks layout1 (return result)
    | Seq layout1 | Grp layout1 ->
      _visit head pos marks layout1 result return
    | Nest layout1 ->
      if head
      then _visit true (pos + tab) marks layout1 result return
      else _visit false pos marks layout1 result return
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _visit head pos marks1 layout1 result return)
        (fun pos1 ->
          _visit head (max pos pos1) marks layout1 result return)
    | Line (left, right) ->
      _visit head pos marks left result @@ fun result1 _pos1 marks1 ->
      _visit true 0 marks1 right result1 return
    | Comp (left, right, pad, _fix) ->
      _visit head pos marks left result @@ fun result1 pos1 marks1 ->
      let pos2 = if pad then pos1 + 1 else pos1 in
      _visit false pos2 marks1 right result1 @@ fun result2 pos3 marks2 ->
      if 0 < pos2 then return result2 pos3 marks2 else
      if 0 < pos3 - pos2 then return result2 pos3 marks2 else
      return (result2 + 1) pos3 marks2
  and _visit_fix head pos marks layout return =
    match layout with
    | Null -> return pos marks
    | Text data -> return (pos + (String.length data)) marks
    | Fix layout1 | Seq layout1 | Grp layout1 ->
      _visit_fix head pos marks layout1 return
    | Nest layout1 ->
      if head
      then _visit_fix true (pos + tab) marks layout1 return
      else _visit_fix false pos marks layout1 return
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _visit_fix head pos marks1 layout1 return)
        (fun pos1 ->
          _visit_fix head (max pos pos1) marks layout1 return)
    | Line (left, _right) ->
      _visit_fix head pos marks left return
    | Comp (left, right, pad, _fix) ->
      _visit_fix head pos marks left @@ fun pos1 marks1 ->
      let pos2 = if pad then pos1 + 1 else pos1 in
      _visit_fix false pos2 marks1 right return
  in
  _visit true 0 marks layout 0 @@ fun result _pos _marks ->
  return result

let _num_lines layout return =
  let rec _visit layout result return =
    match layout with
    | Null | Text _  -> return result
    | Fix layout1 | Seq layout1 | Grp layout1
    | Nest layout1 | Pack (_, layout1) ->
      _visit layout1 result return
    | Line (left, right) ->
      _visit left result @@ fun result1 ->
      _visit right (result1 + 1) return
    | Comp (left, right, _pad, _fix) ->
      _visit left result @@ fun result1 ->
      _visit right result1 return
  in
  _visit layout 1 return

let _solved_form tab width layout =
  let _equal left right = left = right in
  let _fail () = assert false (* Invariant *) in
  let _cont k n m1 x m2 nxs = k m2 ((n, m1, x) :: nxs) in
  let rec _visit marks layout return =
    match layout with
    | Line (left, right) ->
      _measure true 0 marks left @@ fun marks1 length ->
      _visit marks1 right (_cont return length marks left)
    | _ ->
      _measure true 0 marks layout @@ fun marks1 length ->
      return marks1 [(length, marks, layout)]
  and _measure head pos marks layout return =
    match layout with
    | Null -> return marks 0
    | Text data -> return marks (String.length data)
    | Fix layout1 | Seq layout1 | Grp layout1 ->
      _measure head pos marks layout1 return
    | Nest layout1 ->
      let pos1 = if head then pos + tab else pos in
      _measure head pos1 marks layout1 return
    | Pack (index, layout1) ->
      Env.lookup _equal index marks
        (fun _ ->
          Env.bind index pos marks @@ fun marks1 ->
          _measure head pos marks1 layout1 return)
        (fun pos1 ->
          let pos2 = max pos pos1 in
          _measure head pos2 marks layout1 return)
    | Line _ -> assert false (* Invariant *)
    | Comp (left, right, true, _fix) ->
      _measure head pos marks left @@ fun marks1 pos1 ->
      _measure false (pos1 + 1) marks1 right return
    | Comp (left, right, false, _fix) ->
      _measure head pos marks left @@ fun marks1 pos1 ->
      _measure false pos1 marks1 right return
  in
  let rec _check lines return =
    match lines with
    | [] -> return true
    | (length, marks, line) :: lines' ->
      if length <= width then _check lines' return else
      _num_critical_comps tab marks line @@ fun num_comps ->
      if 0 < num_comps then return false else
      _check lines' return
  in
  _visit Env.empty layout @@ fun _marks lines ->
  _check lines (fun result -> result)

(* Define tests *)
let spec_normalize_sound =
  QCheck.Test.make ~count:1024
    ~name:"spec_normalize_sound"
    arbitrary_eDSL
    (fun eDSL ->
      Spec.convert eDSL @@ fun layout ->
      Spec.pre_normalize layout @@ fun layout1 ->
      _normal_form layout1)

let spec_solve_sound =
  QCheck.Test.make ~count:1024
    ~name:"spec_solve_sound"
    QCheck.(triple
      arbitrary_eDSL
      small_nat
      small_nat)
    (fun (eDSL, tab, width) ->
      Spec.convert eDSL @@ fun layout ->
      Spec.solve layout tab width @@ fun layout1 ->
      _solved_form tab width layout1)

let _random_comp_tree x n =
  let open QCheck.Gen in
  let rec _visit n =
    if n <= 1 then return ~$x else
    int_bound (n - 2) >>= fun m ->
    let a = m + 1 in
    let b = n - a in
    map2 (fun l r -> l <&> r)
      (_visit a) (_visit b)
  in
  if n <= 0
  then return Typeset.null
  else _visit n

let spec_solve_box_reflow =
  QCheck.Test.make ~count:32
    ~name:"spec_solve_box_reflow"
    QCheck.(pair small_nat small_nat)
    (fun (count, width) ->
      let eDSL = QCheck.Gen.generate1 (_random_comp_tree "x" count) in
      Spec.convert eDSL @@ fun layout ->
      Spec.solve layout 0 width @@ fun layout1 ->
      let expected_num_lines =
        let _count = max 1 count in
        if width <= 0 then _count else
        if 0 < (_count mod width)
        then (_count / width) + 1
        else _count / width
      in
      _num_lines layout1 @@ fun actual_num_lines ->
      expected_num_lines = actual_num_lines)

let impl_compile_normalizes =
  QCheck.Test.make ~count:4(*4096*)
    ~name:"impl_compile_normalizes"
    arbitrary_eDSL
    (fun eDSL ->
      Typeset.compile eDSL @@ fun doc ->
      Spec.undoc doc @@ fun layout ->
      Spec.pre_normalize layout @@ fun layout1 ->
      if not (layout = layout1) then begin
        Spec.print_layout layout print_endline;
        print_endline "------------------------------------";
        Spec.print_layout layout1 print_endline;
        print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        false
      end else
      true)

let impl_spec_normalize_identity =
  QCheck.Test.make ~count:4(*4096*)
    ~name:"impl_spec_normalize_identity"
    arbitrary_eDSL
    (fun eDSL ->
      Typeset.compile eDSL @@ fun doc ->
      Spec.convert eDSL @@ fun layout ->
      Spec.undoc doc @@ fun impl_layout ->
      Spec.pre_normalize layout @@ fun spec_layout ->
      if not (impl_layout = spec_layout) then begin
        Typeset.print doc print_endline;
        print_endline "------------------------------------";
        Spec.print_layout spec_layout print_endline;
        print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        false
      end else
      true)

let impl_spec_render_identity =
  QCheck.Test.make ~count:128(*4096*)
    ~name:"impl_spec_render_identity"
    QCheck.(triple
      arbitrary_eDSL
      small_nat
      small_nat)
    (fun (eDSL, tab, width) ->
      Typeset.compile eDSL @@ fun doc ->
      Typeset.render doc tab width @@ fun output ->
      Spec.convert eDSL @@ fun layout ->
      Spec.render layout tab width @@ fun spec_output ->
      if not (output = spec_output) then begin
        Spec.undoc doc @@ fun layout1 ->
        print_endline output;
        print_endline "------------------------------------";
        print_endline spec_output;
        print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        Spec.print_layout layout1 print_endline;
        false
      end else
      true)

(* Run tests *)
let _ =
  QCheck_runner.run_tests
  [ (*spec_normalize_sound*)
  (* ; spec_solve_sound *)
  (* ; spec_solve_box_reflow *)
  (* ; impl_compile_normalizes *)
  (* ; impl_spec_normalize_identity *)
   impl_spec_render_identity
  ]
