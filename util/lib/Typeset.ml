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
let (<//>) left right = line left (line null right)

type broken =
  | BNull
  | BText of string
  | BFix of broken
  | BGrp of broken
  | BSeq of bool * broken
  | BNest of broken
  | BPack of broken
  | BLine of broken * broken
  | BComp of broken * broken * attr

(* Collapse broken sequences *)
let _broken eDSL return =
  let _mark eDSL return =
    let _null = BNull in
    let _text data = BText data in
    let _fix layout = BFix layout in
    let _grp layout = BGrp layout in
    let _seq broken layout = BSeq (broken, layout) in
    let _nest layout = BNest layout in
    let _pack layout = BPack layout in
    let _line left right = BLine (left, right) in
    let _comp left right attr = BComp (left, right, attr) in
    let rec _visit eDSL return =
      match eDSL with
      | UNull -> return false _null
      | UText data -> return false (_text data)
      | UFix eDSL1 ->
        _visit eDSL1 @@ fun broken layout ->
        return broken (_fix layout)
      | UGrp eDSL1 ->
        _visit eDSL1 @@ fun broken layout ->
        return broken (_grp layout)
      | USeq eDSL1 ->
        _visit eDSL1 @@ fun broken layout ->
        return broken (_seq broken layout)
      | UNest eDSL1 ->
        _visit eDSL1 @@ fun broken layout ->
        return broken (_nest layout)
      | UPack eDSL1 ->
        _visit eDSL1 @@ fun broken layout ->
        return broken (_pack layout)
      | ULine (left, right) ->
        _visit left @@ fun _l_broken left1 ->
        _visit right @@ fun _r_broken right1 ->
        return true (_line left1 right1)
      | UComp (left, right, attr) ->
        _visit left @@ fun l_broken left1 ->
        _visit right @@ fun r_broken right1 ->
        let broken = l_broken || r_broken in
        return broken (_comp left1 right1 attr)
    in
    _visit eDSL @@ fun _break layout ->
    return layout
  in
  let rec _remove eDSL break return =
    match eDSL with
    | BNull -> return null
    | BText data -> return (text data)
    | BFix eDSL1 -> _remove eDSL1 false (return <== fix)
    | BGrp eDSL1 -> _remove eDSL1 false (return <== grp)
    | BSeq (broken, eDSL1) ->
      if broken
      then _remove eDSL1 true return
      else _remove eDSL1 false (return <== seq)
    | BNest eDSL1 -> _remove eDSL1 break (return <== nest)
    | BPack eDSL1 -> _remove eDSL1 break (return <== pack)
    | BLine (left, right) ->
      _remove left break @@ fun left1 ->
      _remove right break @@ fun right1 ->
      return (line left1 right1)
    | BComp (left, right, attr) ->
      _remove left break @@ fun left1 ->
      _remove right break @@ fun right1 ->
      if break && not attr.fix
      then return (line left1 right1)
      else return (comp left1 right1 attr.pad attr.fix)
  in
  _mark eDSL @@ fun eDSL1 ->
  _remove eDSL1 false return

type serial =
  | SNext of serial_term * serial_comp * serial
  | SLast of serial_term * serial
  | SPast
and serial_term =
  | SNull
  | SText of string
  | SNest of serial_term
  | SPack of int * serial_term
and serial_comp =
  | SLine
  | SComp of attr
  | SGrp of int * serial_comp
  | SSeq of int * serial_comp

(*
  Serialize in order to normalize
*)
let _serialize eDSL return =
  let _next term comp serial = SNext (term, comp, serial) in
  let _last term serial = SLast (term, serial) in
  let _past = SPast in
  let _null = SNull in
  let _text data = SText data in
  let _nest term = SNest term in
  let _pack index term = SPack (index, term) in
  let _line = SLine in
  let _comp attr = SComp attr in
  let _grp index comp = SGrp (index, comp) in
  let _seq index comp = SSeq (index, comp) in
  let __line term serial = _next term _line serial in
  let __comp comps attr term serial = _next term (comps (_comp attr)) serial in
  let rec _visit i j fixed terms comps glue result eDSL return =
    match eDSL with
    | UNull -> return i j (result <== (glue _null))
    | UText data -> return i j (result <== (glue (terms (_text data))))
    | UFix eDSL1 -> _visit i j true terms comps glue result eDSL1 return
    | UGrp eDSL1 ->
      _visit
        (i + 1) j fixed
        terms (comps <== (_grp i))
        glue result eDSL1 return
    | USeq eDSL1 ->
      _visit
        (i + 1) j fixed
        terms (comps <== (_seq i))
        glue result eDSL1 return
    | UNest eDSL1 ->
      _visit
        i j fixed
        (terms <== _nest) comps
        glue result eDSL1 return
    | UPack eDSL1 ->
      _visit
        i (j + 1) fixed
        (terms <== (_pack j)) comps
        glue result eDSL1 return
    | ULine (left, right) ->
      _visit i j fixed terms comps __line result left @@ fun i1 j1 result1 ->
      _visit i1 j1 fixed terms comps glue result1 right return
    | UComp (left, right, attr) ->
      let attr1 = { attr with fix = fixed || attr.fix } in
      let glue1 = __comp comps attr1 in
      _visit i j fixed terms comps glue1 result left @@ fun i1 j1 result1 ->
      _visit i1 j1 fixed terms comps glue result1 right return
  in
  let id x = x in
  _visit 0 0 false id id _last id eDSL @@ fun _i _j result ->
  return (result _past)

type linear_doc =
  | LNil
  | LCons of linear_obj * linear_doc
and linear_obj =
  | LNext of linear_term * linear_comp * linear_obj
  | LLast of linear_term
and linear_term =
  | LNull
  | LText of string
  | LNest of linear_term
  | LPack of int * linear_term
and linear_comp =
  | LComp of attr
  | LGrp of int * linear_comp
  | LSeq of int * linear_comp

(*
  Lift newlines to spine
*)
let _linearize serial return =
  let _nil = LNil in
  let _cons obj doc = LCons (obj, doc) in
  let _next comp term obj = LNext (comp, term, obj) in
  let _last term = LLast term in
  let _null = LNull in
  let _text data = LText data in
  let _nest term = LNest term in
  let _pack index term = LPack (index, term) in
  let _comp attr = LComp attr in
  let _grp index comp = LGrp (index, comp) in
  let _seq index comp = LSeq (index, comp) in
  let rec _visit_serial line serial return =
    match serial with
    | SNext (term, SLine, serial1) ->
      _visit_term term @@ fun term1 ->
      _visit_serial identity serial1 @@ fun serial2 ->
      return (_cons (line (_last term1)) serial2)
    | SNext (term, comp, serial1) ->
      _visit_term term @@ fun term1 ->
      _visit_comp comp @@ fun comp1 ->
      _visit_serial (line <== (_next term1 comp1)) serial1 return
    | SLast (term, SPast) ->
      _visit_term term @@ fun term1 ->
      return (_cons (line (_last term1)) _nil)
    | _ -> assert false (* Invariant *)
  and _visit_term term return =
    match term with
    | SNull -> return _null
    | SText data -> return (_text data)
    | SNest term1 -> _visit_term term1 (return <== _nest)
    | SPack (index, term1) -> _visit_term term1 (return <== (_pack index))
  and _visit_comp comp return =
    match comp with
    | SLine -> assert false (* Invariant *)
    | SComp attr -> return (_comp attr)
    | SGrp (index, comp1) -> _visit_comp comp1 (return <== (_grp index))
    | SSeq (index, comp1) -> _visit_comp comp1 (return <== (_seq index))
  in
  _visit_serial identity serial return

type fixed_doc =
  | FEOD
  | FBreak of fixed_obj * fixed_doc
and fixed_obj =
  | FNext of fixed_item * fixed_comp * fixed_obj
  | FLast of fixed_item
and fixed_item =
  | FFix of fixed_fix
  | FTerm of fixed_term
and fixed_term =
  | FNull
  | FText of string
  | FNest of fixed_term
  | FPack of int * fixed_term
and fixed_comp =
  | FComp of bool
  | FGrp of int * fixed_comp
  | FSeq of int * fixed_comp
and fixed_fix =
  | FFNext of fixed_term * fixed_comp * fixed_fix
  | FFLast of fixed_term

(*
  Coalesce fixed comps
*)
let _fixed doc return =
  let _eod = FEOD in
  let _break obj doc = FBreak (obj, doc) in
  let _next item comp obj = FNext (item, comp, obj) in
  let _last item = FLast item in
  let _fix fix = FFix fix in
  let _term term = FTerm term in
  let _null = FNull in
  let _text data = FText data in
  let _nest term = FNest term in
  let _pack index term = FPack (index, term) in
  let _comp pad = FComp pad in
  let _grp index comp = FGrp (index, comp) in
  let _seq index comp = FSeq (index, comp) in
  let _fix_next term comp fix = FFNext (term, comp, fix) in
  let _fix_last term = FFLast term in
  let rec _visit_doc doc return =
    match doc with
    | LNil -> return _eod
    | LCons (obj, doc1) ->
      _visit_obj obj @@ fun obj1 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_break obj1 doc2)
  and _visit_obj obj return =
    match obj with
    | LNext (term, comp, obj1) ->
      _visit_term term @@ fun term1 ->
      _visit_comp comp @@ fun is_fixed comp1 ->
      if is_fixed
      then _visit_fix (_fix_next term1 comp1) obj1 return
      else _visit_obj obj1 (return <== (_next (_term term1) comp1))
    | LLast term ->
      _visit_term term @@ fun term1 ->
      return (_last (_term term1))
  and _visit_fix line obj return =
    match obj with
    | LNext (term, comp, obj1) ->
      _visit_term term @@ fun term1 ->
      _visit_comp comp @@ fun is_fixed comp1 ->
      if is_fixed
      then _visit_fix (line <== (_fix_next term1 comp1)) obj1 return
      else _visit_obj obj1
        (return <== (_next (_fix (line (_fix_last term1))) comp1))
    | LLast term ->
      _visit_term term @@ fun term1 ->
      return (_last (_fix (line (_fix_last term1))))
  and _visit_term term return =
    match term with
    | LNull -> return _null
    | LText data -> return (_text data)
    | LNest term1 -> _visit_term term1 (return <== _nest)
    | LPack (index, term1) -> _visit_term term1 (return <== (_pack index))
  and _visit_comp comp return =
    match comp with
    | LComp attr -> return attr.fix (_comp attr.pad)
    | LGrp (index, comp1) ->
      _visit_comp comp1 @@ fun is_fixed comp2 ->
      return is_fixed (_grp index comp2)
    | LSeq (index, comp1) ->
      _visit_comp comp1 @@ fun is_fixed comp2 ->
      return is_fixed (_seq index comp2)
  in
  _visit_doc doc return

type 'a property =
  | PGrp of 'a
  | PSeq of 'a

type graph_doc =
  | GEOD
  | GBreak of graph_node Array.t * bool list * graph_doc
and graph_node =
  { index : int
  ; term : graph_term
  ; mutable ins_head : graph_edge option
  ; mutable ins_tail : graph_edge option
  ; mutable outs_head : graph_edge option
  ; mutable outs_tail : graph_edge option
  }
and graph_edge =
  { prop : unit property
  ; mutable ins_next : graph_edge option
  ; mutable ins_prev : graph_edge option
  ; mutable outs_next : graph_edge option
  ; mutable outs_prev : graph_edge option
  ; mutable source : graph_node
  ; mutable target : graph_node
  }
and graph_term =
  | GNull
  | GText of string
  | GFix of graph_fix
  | GNest of graph_term
  | GPack of int * graph_term
and graph_fix =
  | GFLast of graph_term
  | GFNext of graph_term * graph_fix * bool

let make_node index term =
  { index = index
  ; term = term
  ; ins_head = None
  ; ins_tail = None
  ; outs_head = None
  ; outs_tail = None
  }

let make_edge prop source target =
  { prop = prop
  ; ins_next = None
  ; ins_prev = None
  ; outs_next = None
  ; outs_prev = None
  ; source = source
  ; target = target
  }

type rebuild_doc =
  | RBEOD
  | RBBreak of rebuild_obj * rebuild_doc
and rebuild_obj =
  | RBTerm of rebuild_term
  | RBFix of rebuild_fix
  | RBGrp of rebuild_obj
  | RBSeq of rebuild_obj
  | RBComp of rebuild_obj * rebuild_obj * bool
and rebuild_fix =
  | RBFTerm of rebuild_term
  | RBFComp of rebuild_fix * rebuild_fix * bool
and rebuild_term =
  | RBNull
  | RBText of string
  | RBNest of rebuild_term
  | RBPack of int * rebuild_term

let _structurize doc return =
  let _graphify doc return =
    let _eod = GEOD in
    let _break nodes pads doc = GBreak (nodes, pads, doc) in
    let _null = GNull in
    let _text data = GText data in
    let _fix fix = GFix fix in
    let _nest term = GNest term in
    let _pack index term = GPack (index, term) in
    let _fix_last term = GFLast term in
    let _fix_next left right pad = GFNext (left, right, pad) in
    let _unary_grp index = PGrp index in
    let _unary_seq index = PSeq index in
    let _binary_grp from_index to_index = PGrp (from_index, to_index) in
    let _binary_seq from_index to_index = PSeq (from_index, to_index) in
    let _lift_stack comp return =
      let rec _visit comp return =
        match comp with
        | FComp pad -> return [] pad
        | FGrp (index, comp1) ->
          _visit comp1 (return <== (List.cons (_unary_grp index)))
        | FSeq (index, comp1) ->
          _visit comp1 (return <== (List.cons (_unary_seq index)))
      in
      _visit comp return
    in
    let _close to_node stack props return =
      let _lookup = Map.lookup_unsafe_cont Order.int_compare in
      let _insert = Map.insert_cont Order.int_compare in
      let rec _visit stack props return =
        match stack with
        | [] -> return props
        | PGrp index :: stack1 ->
          _lookup index props @@ fun prop ->
          begin match prop with
          | PSeq _ -> assert false (* Invariant *)
          | PGrp (from_node, _to_node) ->
            let prop1 = _binary_grp from_node (Some to_node) in
            _insert index prop1 props @@ fun props1 ->
            _visit stack1 props1 return
          end
        | PSeq index :: stack1 ->
          _lookup index props @@ fun prop ->
          begin match prop with
          | PGrp _ -> assert false (* Invariant *)
          | PSeq (from_node, _to_node) ->
            let prop1 = _binary_seq from_node (Some to_node) in
            _insert index prop1 props @@ fun props1 ->
            _visit stack1 props1 return
          end
      in
      _visit stack props return
    in
    let _open from_node stack props return =
      let _insert = Map.insert_cont Order.int_compare in
      let rec _visit stack props return =
        match stack with
        | [] -> return props
        | PGrp index :: stack1 ->
          let prop = _binary_grp from_node None in
          _insert index prop props @@ fun props1 ->
          _visit stack1 props1 return
        | PSeq index :: stack1 ->
          let prop = _binary_seq from_node None in
          _insert index prop props @@ fun props1 ->
          _visit stack1 props1 return
      in
      _visit stack props return
    in
    let _update node scope stack props return =
      let rec _visit scope stack return =
        match scope, stack with
        | _, [] -> _close node scope props (return [])
        | [], _ -> _open node stack props (return stack)
        | PGrp left :: scope1, PGrp right :: stack1 ->
          if left > right then assert false (* Invariant *) else
          if left = right
          then
            _visit scope1 stack1 (return <== (List.cons (_unary_grp left)))
          else
            _close node scope props @@ fun props1 ->
            _open node stack props1 @@ fun props2 ->
            return stack props2
        | PSeq left :: scope1, PSeq right :: stack1 ->
          if left > right then assert false (* Invariant *) else
          if left = right
          then
            _visit scope1 stack1 (return <== (List.cons (_unary_seq left)))
          else
            _close node scope props @@ fun props1 ->
            _open node stack props1 @@ fun props2 ->
            return stack props2
        | _ ->
          _close node scope props @@ fun props1 ->
          _open node stack props1 @@ fun props2 ->
          return stack props2
      in
      _visit scope stack return
    in
    let _transpose props nodes =
      let _push_ins edge node =
        match node.ins_tail with
        | None ->
          node.ins_head <- Some edge;
          node.ins_tail <- Some edge
        | Some tail ->
          edge.ins_prev <- Some tail;
          tail.ins_next <- Some edge;
          node.ins_tail <- Some edge
      in
      let _push_outs edge node =
        match node.outs_tail with
        | None ->
          node.outs_head <- Some edge;
          node.outs_tail <- Some edge
        | Some tail ->
          edge.outs_prev <- Some tail;
          tail.outs_next <- Some edge;
          node.outs_tail <- Some edge
      in
      let rec _visit props =
        match props with
        | [] -> ()
        | PGrp (from_index, Some to_index) :: props1 ->
          if from_index = to_index then _visit props1 else
          let from_node = Array.get nodes from_index in
          let to_node = Array.get nodes to_index in
          let curr = make_edge (_unary_grp ()) from_node to_node in
          _push_ins curr to_node;
          _push_outs curr from_node;
          _visit props1
        | PSeq (from_index, Some to_index) :: props1 ->
          if from_index = to_index then _visit props1 else
          let from_node = Array.get nodes from_index in
          let to_node = Array.get nodes to_index in
          let curr = make_edge (_unary_seq ()) from_node to_node in
          _push_ins curr to_node;
          _push_outs curr from_node;
          _visit props1
        | _ -> assert false (* Invariant *)
      in
      _visit props
    in
    let rec _visit_doc doc return =
      match doc with
      | FEOD -> return _eod
      | FBreak (obj, doc1) ->
        let nodes = identity in
        let pads = identity in
        let props = Map.make () in
        _visit_obj obj 0 [] nodes pads props @@ fun nodes1 pads1 props1 ->
        let nodes2 = Array.of_list (nodes1 []) in
        _transpose (Map.values props1) nodes2;
        _visit_doc doc1 @@ fun doc2 ->
        return (_break nodes2 (pads1 []) doc2)
    and _visit_obj obj index scope nodes pads props return =
      match obj with
      | FNext (FTerm term, comp, obj1) ->
        _visit_term term @@ fun term1 ->
        let nodes1 = nodes <== (List.cons (make_node index term1)) in
        _lift_stack comp @@ fun stack pad ->
        let pads1 = pads <== (List.cons pad) in
        _update index scope stack props @@ fun scope1 props1 ->
        _visit_obj obj1 (index + 1) scope1 nodes1 pads1 props1 return
      | FNext (FFix fix, comp, obj1) ->
        _visit_fix fix index scope props @@ fun fix1 scope1 props1 ->
        let nodes1 = nodes <== (List.cons (make_node index (_fix fix1))) in
        _lift_stack comp @@ fun stack pad ->
        let pads1 = pads <== (List.cons pad) in
        _update index scope1 stack props1 @@ fun scope2 props2 ->
        _visit_obj obj1 (index + 1) scope2 nodes1 pads1 props2 return
      | FLast (FTerm term) ->
        _visit_term term @@ fun term1 ->
        let nodes1 = nodes <== (List.cons (make_node index term1)) in
        _close index scope props @@ fun props1 ->
        return nodes1 pads props1
      | FLast (FFix fix) ->
        _visit_fix fix index scope props @@ fun fix1 scope1 props1 ->
        let nodes1 = nodes <== (List.cons (make_node index (_fix fix1))) in
        _close index scope1 props1 @@ fun props2 ->
        return nodes1 pads props2
    and _visit_term term return =
      match term with
      | FNull -> return _null
      | FText data -> return (_text data)
      | FNest term1 -> _visit_term term1 (return <== _nest)
      | FPack (index, term1) -> _visit_term term1 (return <== (_pack index))
    and _visit_fix fix index scope props return =
      match fix with
      | FFNext (term, comp, fix1) ->
        _visit_term term @@ fun term1 ->
        _lift_stack comp @@ fun stack pad ->
        _update index scope stack props @@ fun scope1 props1 ->
        _visit_fix fix1 index scope1 props1 @@ fun fix2 scope2 props2 ->
        return (_fix_next term1 fix2 pad) scope2 props2
      | FFLast term ->
        _visit_term term @@ fun term1 ->
        return (_fix_last term1) scope props
    in
    _visit_doc doc return
  in
  let _solve doc return =
    let _eod = GEOD in
    let _break nodes pads doc = GBreak (nodes, pads, doc) in
    let _seq index = PSeq index in
    let _move_ins head tail edge =
      let _remove_ins ins =
        let node = ins.target in
        node.ins_head <- None;
        node.ins_tail <- None
      in
      let _append_ins head tail edge =
        let node = edge.target in
        let _set_targets ins =
          let rec _visit maybe_edge =
            match maybe_edge with
            | None -> ()
            | Some edge ->
              edge.target <- node;
              _visit edge.ins_next
          in
          _visit (Some ins)
        in
        _set_targets head;
        match edge.ins_next with
        | None ->
          edge.ins_next <- Some head;
          head.ins_prev <- Some edge;
          node.ins_tail <- Some tail
        | Some next ->
          tail.ins_next <- Some next;
          next.ins_prev <- Some tail;
          edge.ins_next <- Some head;
          head.ins_prev <- Some edge
      in
      _remove_ins head;
      _append_ins head tail edge
    in
    let _move_out curr edge =
      let _remove_out curr =
        let node = curr.source in
        match curr.outs_prev, curr.outs_next with
        | None, None ->
          node.outs_head <- None;
          node.outs_tail <- None
        | Some prev, None ->
          curr.outs_prev <- None;
          prev.outs_next <- None;
          node.outs_tail <- Some prev
        | None, Some next ->
          curr.outs_next <- None;
          next.outs_prev <- None;
          node.outs_head <- Some next
        | Some prev, Some next ->
          curr.outs_prev <- None;
          curr.outs_next <- None;
          prev.outs_next <- Some next;
          next.outs_prev <- Some prev
      in
      let _prepend_out curr edge =
        let node = edge.source in
        curr.source <- node;
        match edge.outs_prev with
        | None ->
          curr.outs_next <- Some edge;
          edge.outs_prev <- Some curr;
          node.outs_head <- Some curr
        | Some prev ->
          prev.outs_next <- Some curr;
          curr.outs_prev <- Some prev;
          curr.outs_next <- Some edge;
          edge.outs_prev <- Some curr;
      in
      _remove_out curr;
      _prepend_out curr edge
    in
    let _resolve edge outs none some =
      let rec _visit maybe_curr edge =
        match maybe_curr with
        | None -> none ()
        | Some curr ->
          begin match curr.prop with
          | PGrp () -> some curr
          | PSeq () ->
            let curr1 = curr.outs_next in
            _move_out curr edge;
            _visit curr1 curr;
          end
      in
      _visit (Some outs) edge
    in
    let _leftmost head return =
      let rec _visit curr index result =
        match curr.ins_next with
        | None -> return result
        | Some next ->
          let index1 = next.source.index in
          if index1 < index
          then _visit next index1 next
          else _visit next index result
      in
      _visit head head.source.index head
    in
    let rec _visit_doc doc return =
      match doc with
      | GEOD -> return _eod
      | GBreak (nodes, pads, doc1) ->
        let count = Array.length nodes in
        _visit_node count 0 nodes;
        _visit_doc doc1 @@ fun doc2 ->
        return (_break nodes pads doc2)
    and _visit_node count index nodes =
      if count = index then () else
      let node = Array.get nodes index in
      match
        (node.ins_head, node.ins_tail),
        (node.outs_head, node.outs_tail)
      with
      | (Some ins_head, Some ins_tail), (Some outs_head, Some _outs_tail) ->
        _leftmost ins_head @@ fun ins_first ->
        _resolve ins_first outs_head
          (fun () ->
            _visit_node count (index + 1) nodes)
          (fun outs_head1 ->
            _move_ins ins_head ins_tail outs_head1;
            _visit_node count (index + 1) nodes)
      | (Some _, None), _ | (None, Some _), _
      | _, (Some _, None) | _, (None, Some _) -> assert false (* Invariant *)
      | _, _ -> _visit_node count (index + 1) nodes
    in
    _visit_doc doc return
  in
  let _rebuild doc return =
    let _eod = RBEOD in
    let _break obj doc = RBBreak (obj, doc) in
    let _term term = RBTerm term in
    let _fix fix = RBFix fix in
    let _grp obj = RBGrp obj in
    let _seq obj = RBSeq obj in
    let _comp left right pad = RBComp (left, right, pad) in
    let _fix_term term = RBFTerm term in
    let _fix_comp left right pad = RBFComp (left, right, pad) in
    let _null = RBNull in
    let _text data = RBText data in
    let _nest term = RBNest term in
    let _pack index term = RBPack (index, term) in
    let __comp left pad right = _comp left right pad in
    let _topology nodes return =
      let _num_ins node return =
        let rec _visit maybe_edge num =
          match maybe_edge with
          | None -> return num
          | Some edge -> _visit edge.ins_next (num + 1)
        in
        _visit node.ins_head 0
      in
      let _prop_outs node return =
        let rec _visit maybe_edge props =
          match maybe_edge with
          | None -> return (props [])
          | Some edge ->
            _visit edge.outs_next
              (props <== (List.cons edge.prop))
        in
        _visit node.outs_head identity
      in
      let count = Array.length nodes in
      let rec _visit index terms ins outs =
        if index = count then return (terms []) (ins []) (outs []) else
        let node = Array.get nodes index in
        _num_ins node @@ fun num_ins ->
        _prop_outs node @@ fun prop_outs ->
        _visit (index + 1)
          (terms <== (List.cons node.term))
          (ins <== (List.cons num_ins))
          (outs <== (List.cons prop_outs))
      in
      _visit 0 identity identity identity
    in
    let _open props stack partial return =
      let rec _visit props stack return =
        match props with
        | [] -> return stack
        | PGrp () :: props1 ->
          _visit props1 (_grp :: stack) return
        | PSeq () :: props1 ->
          _visit props1 (_seq :: stack) return
      in
      match stack with
      | top :: stack1 -> _visit props ((top <== partial) :: stack1) return
      | _ -> assert false (* Invariant *)
    in
    let _close count stack term return =
      let rec _visit count stack result return =
        if count = 0 then return stack result else
        match stack with
        | [] -> assert false (* Invariant *)
        | top :: stack1 ->
          _visit (count - 1) stack1 (top result) return
      in
      _visit count stack term return
    in
    let _final stack term return =
      match stack with
      | last :: [] -> return (last term)
      | _ -> assert false (* Invariant *)
    in
    let rec _visit_doc doc return =
      match doc with
      | GEOD -> return _eod
      | GBreak (nodes, pads, doc1) ->
        _topology nodes @@ fun terms ins outs ->
        _visit_line terms pads ins outs [identity] identity @@ fun obj ->
        _visit_doc doc1 @@ fun doc2 ->
        return (_break obj doc2)
    and _visit_line terms pads ins outs stack partial return =
      match terms, pads with
      | GFix fix :: [], [] ->
        _visit_fix fix @@ fun fix1 ->
        begin match ins, outs with
        | 0 :: [], [] :: [] ->
          _final stack (partial (_fix fix1)) return
        | in_props :: [], [] :: [] ->
          _close in_props stack (partial (_fix fix1)) @@ fun stack1 fix2 ->
          _final stack1 fix2 return
        | _, _ -> assert false (* Invariant *)
        end
      | term :: [], [] ->
        _visit_term term @@ fun term1 ->
        begin match ins, outs with
        | 0 :: [], [] :: [] ->
          _final stack (partial (_term term1)) return
        | in_props :: [], [] :: [] ->
          _close in_props stack (partial (_term term1)) @@ fun stack1 term2 ->
          _final stack1 term2 return
        | _, _ -> assert false (* Invariant *)
        end
      | GFix fix :: terms1, pad :: pads1 ->
        _visit_fix fix @@ fun fix1 ->
        begin match ins, outs with
        | 0 :: ins1, [] :: outs1 ->
          let partial1 = partial <== (__comp (_fix fix1) pad) in
          _visit_line terms1 pads1 ins1 outs1 stack partial1 return
        | in_props :: ins1, [] :: outs1 ->
          _close in_props stack (partial (_fix fix1)) @@ fun stack1 fix2 ->
          let partial1 = __comp fix2 pad in
          _visit_line terms1 pads1 ins1 outs1 stack1 partial1 return
        | 0 :: ins1, out_props :: outs1 ->
          _open out_props stack partial @@ fun stack1 ->
          let partial1 = __comp (_fix fix1) pad in
          _visit_line terms1 pads1 ins1 outs1 stack1 partial1 return
        | _, _ -> assert false (* Invariant *)
        end
      | term :: terms1, pad :: pads1 ->
        _visit_term term @@ fun term1 ->
        begin match ins, outs with
        | 0 :: ins1, [] :: outs1 ->
          let partial1 = partial <== (__comp (_term term1) pad) in
          _visit_line terms1 pads1 ins1 outs1 stack partial1 return
        | in_props :: ins1, [] :: outs1 ->
          _close in_props stack (partial (_term term1)) @@ fun stack1 term2 ->
          let partial1 = __comp term2 pad in
          _visit_line terms1 pads1 ins1 outs1 stack1 partial1 return
        | 0 :: ins1, out_props :: outs1 ->
          _open out_props stack partial @@ fun stack1 ->
          let partial1 = __comp (_term term1) pad in
          _visit_line terms1 pads1 ins1 outs1 stack1 partial1 return
        | _, _ -> assert false (* Invariant *)
        end
      | _, _ -> assert false (* Invariant *)
    and _visit_term term return =
      match term with
      | GNull -> return _null
      | GText data -> return (_text data)
      | GNest term1 -> _visit_term term1 (return <== _nest)
      | GPack (index, term1) -> _visit_term term1 (return <== (_pack index))
      | GFix _fix -> assert false (* Invariant *)
    and _visit_fix fix return =
      match fix with
      | GFLast term -> _visit_term term (return <== _fix_term)
      | GFNext (term, fix1, pad) ->
        _visit_term term @@ fun term1 ->
        _visit_fix fix1 @@ fun fix2 ->
        return (_fix_comp (_fix_term term1) fix2 pad)
    in
    _visit_doc doc return
  in
  _graphify doc @@ fun doc1 ->
  _solve doc1 @@ fun doc2 ->
  _rebuild doc2 return

type denull_doc =
  | DEOD
  | DLine of denull_obj
  | DEmpty of denull_doc
  | DBreak of denull_obj * denull_doc
and denull_obj =
  | DTerm of denull_term
  | DFix of denull_fix
  | DGrp of denull_obj
  | DSeq of denull_obj
  | DComp of denull_obj * denull_obj * bool
and denull_fix =
  | DFTerm of denull_term
  | DFComp of denull_fix * denull_fix * bool
and denull_term =
  | DText of string
  | DNest of denull_term
  | DPack of int * denull_term

(*
  Remove null identities
*)
let _denull doc return =
  let _eod = DEOD in
  let _line obj = DLine obj in
  let _empty doc = DEmpty doc in
  let _break obj doc = DBreak (obj, doc) in
  let _term term = DTerm term in
  let _fix fix = DFix fix in
  let _grp obj = DGrp obj in
  let _seq obj = DSeq obj in
  let _comp left right pad = DComp (left, right, pad) in
  let _fix_term term = DFTerm term in
  let _fix_comp left right pad = DFComp (left, right, pad) in
  let _text data = DText data in
  let _nest term = DNest term in
  let _pack index term = DPack (index, term) in
  let rec _visit_doc doc none some =
    match doc with
    | RBEOD -> none ()
    | RBBreak (obj, doc1) ->
      _visit_obj obj
        (fun () ->
          _visit_doc doc1
            (fun () -> some _eod)
            (fun doc2 -> some (_empty doc2)))
        (fun obj1 ->
          _visit_doc doc1
            (fun () -> some (_line obj1))
            (fun doc2 -> some (_break obj1 doc2)))
        (fun _pad obj1 ->
          _visit_doc doc1
            (fun () -> some (_line obj1))
            (fun doc2 -> some (_break obj1 doc2)))
  and _visit_obj obj last_none last_some next_none =
    match obj with
    | RBTerm term -> _visit_term term last_none (last_some <== _term)
    | RBFix fix ->
      _visit_fix fix last_none (last_some <== _fix)
        (fun _comp fix1 -> last_some (_fix fix1))
    | RBGrp obj1 ->
      _visit_obj obj1
        last_none
        (last_some <== _grp)
        (fun _pad obj2 ->
          last_some (_grp obj2))
    | RBSeq obj1 ->
      _visit_obj obj1
        last_none
        (last_some <== _seq)
        (fun _pad obj2 ->
          last_some (_seq obj2))
    | RBComp (left, right, l_pad) ->
      _visit_obj left
        (fun () ->
          _visit_obj right
            last_none
            (next_none l_pad)
            (fun r_pad right1 ->
              let pad = l_pad || r_pad in
              next_none pad right1))
        (fun left1 ->
          _visit_obj right
            (fun () -> last_some left1)
            (fun right1 -> last_some (_comp left1 right1 l_pad))
            (fun r_pad right1 ->
              let pad = l_pad || r_pad in
              last_some (_comp left1 right1 pad)))
        (fun _pad _left1 -> assert false (* Invariant *))
  and _visit_fix fix last_none last_some next_none =
    match fix with
    | RBFTerm term -> _visit_term term last_none (last_some <== _fix_term)
    | RBFComp (left, right, l_pad) ->
      _visit_fix left
        (fun () ->
          _visit_fix right
            last_none
            (next_none l_pad)
            (fun r_pad right1 ->
              let pad = l_pad || r_pad in
              next_none pad right1))
        (fun left1 ->
          _visit_fix right
            (fun () -> last_some left1)
            (fun right1 -> last_some (_fix_comp left1 right1 l_pad))
            (fun r_pad right1 ->
              let pad = l_pad || r_pad in
              last_some (_fix_comp left1 right1 pad)))
        (fun _pad _left1 -> assert false (* Invariant *))
  and _visit_term term none some =
    match term with
    | RBNull | RBText "" -> none ()
    | RBText data -> some (_text data)
    | RBNest term1 -> _visit_term term1 none (some <== _nest)
    | RBPack (index, term1) -> _visit_term term1 none (some <== (_pack index))
  in
  _visit_doc doc (fun () -> return _eod) return

type count =
  | Zero
  | One
  | Many

(*
  Remove grp and seq identities
*)
let _identities doc return =
  let _eod = DEOD in
  let _empty doc = DEmpty doc in
  let _break obj doc = DBreak (obj, doc) in
  let _line obj = DLine obj in
  let _term term = DTerm term in
  let _fix fix = DFix fix in
  let _grp obj = DGrp obj in
  let _seq obj = DSeq obj in
  let _comp left right pad = DComp (left, right, pad) in
  let _add left right =
    match left, right with
    | Zero, _ -> right
    | _, Zero -> left
    | Many, _ | _, Many | One, One -> Many
  in
  let _elim_seqs doc return =
    let rec _visit_doc doc return =
      match doc with
      | DEOD -> return _eod
      | DEmpty doc1 ->
        _visit_doc doc1 @@ fun doc2 ->
        return (_empty doc2)
      | DBreak (obj, doc1) ->
        _visit_obj obj false @@ fun _count obj1 ->
        _visit_doc doc1 @@ fun doc2 ->
        return (_break obj1 doc2)
      | DLine obj ->
        _visit_obj obj false @@ fun _count obj1 ->
        return (_line obj1)
    and _visit_obj obj under_seq return =
      match obj with
      | DTerm term | DFix (DFTerm term) ->
        return Zero (_term term)
      | DFix fix -> return Zero (_fix fix)
      | DGrp obj1 ->
        _visit_obj obj1 false @@ fun _count obj2 ->
        return Zero (_grp obj2)
      | DSeq obj1 ->
        if under_seq then _visit_obj obj1 true return else
        _visit_obj obj1 true @@ fun count obj2 ->
        begin match count with
        | Zero | One -> return count obj2
        | Many -> return Many (_seq obj2)
        end
      | DComp (left, right, pad) ->
        _visit_obj left under_seq @@ fun l_count left1 ->
        _visit_obj right under_seq @@ fun r_count right1 ->
        let count = _add One (_add l_count r_count) in
        return count (_comp left1 right1 pad)
    in
    _visit_doc doc return
  in
  let _elim_grps doc return =
    let rec _visit_doc doc return =
      match doc with
      | DEOD -> return _eod
      | DEmpty doc1 ->
        _visit_doc doc1 @@ fun doc2 ->
        return (_empty doc2)
      | DBreak (obj, doc1) ->
        _visit_obj obj true @@ fun _count obj1 ->
        _visit_doc doc1 @@ fun doc2 ->
        return (_break obj1 doc2)
      | DLine obj ->
        _visit_obj obj true @@ fun _count obj1 ->
        return (_line obj1)
    and _visit_obj obj in_head return =
      match obj with
      | DTerm term | DFix (DFTerm term) ->
        return Zero (_term term)
      | DFix fix -> return Zero (_fix fix)
      | DGrp obj1 ->
        if in_head then _visit_obj obj1 true return else
        _visit_obj obj1 false @@ fun count obj2 ->
        begin match count with
        | Zero -> return Zero obj2
        | One | Many -> return Zero (_grp obj2)
        end
      | DSeq obj1 ->
        _visit_obj obj1 false @@ fun count obj2 ->
        return count (_seq obj2)
      | DComp (left, right, pad) ->
        _visit_obj left in_head @@ fun l_count left1 ->
        _visit_obj right false @@ fun r_count right1 ->
        let count = _add One (_add l_count r_count) in
        return count (_comp left1 right1 pad)
    in
    _visit_doc doc return
  in
  _elim_seqs doc @@ fun doc1 ->
  _elim_grps doc1 return

(*
  Reassociate after grp and seq removals
*)
let _reassociate doc return =
  let _eod = DEOD in
  let _empty doc = DEmpty doc in
  let _break obj doc = DBreak (obj, doc) in
  let _line obj = DLine obj in
  let _term term = DTerm term in
  let _fix fix = DFix fix in
  let _grp obj = DGrp obj in
  let _seq obj = DSeq obj in
  let _comp left right pad = DComp (left, right, pad) in
  let __comp pad right left = _comp left right pad in
  let rec _visit_doc doc return =
    match doc with
    | DEOD -> return _eod
    | DEmpty doc1 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_empty doc2)
    | DBreak (obj, doc1) ->
      _visit_obj obj identity @@ fun obj1 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_break obj1 doc2)
    | DLine obj ->
      _visit_obj obj identity @@ fun obj1 ->
      return (_line obj1)
  and _visit_obj obj partial return =
    match obj with
    | DTerm term -> return (partial (_term term))
    | DFix fix -> return (partial (_fix fix))
    | DGrp obj1 -> _visit_obj obj1 identity (return <== partial <== _grp)
    | DSeq obj1 -> _visit_obj obj1 identity (return <== partial <== _seq)
    | DComp (left, right, pad) ->
      _visit_obj right partial @@ fun result ->
      _visit_obj left (__comp pad result) return
  in
  _visit_doc doc return

type doc =
  | REOD
  | REmpty of doc
  | RBreak of doc_obj * doc
  | RLine of doc_obj
and doc_obj =
  | RText of string
  | RFix of doc_obj_fix
  | RGrp of doc_obj
  | RSeq of doc_obj
  | RNest of doc_obj
  | RPack of int * doc_obj
  | RComp of doc_obj * doc_obj * bool
and doc_obj_fix =
  | RFText of string
  | RFComp of doc_obj_fix * doc_obj_fix * bool

type prop =
  | PNest
  | PPack of int

(*
  Rescope nest and pack.
*)
let _rescope doc return =
  let _eod = REOD in
  let _empty doc = REmpty doc in
  let _break obj doc = RBreak (obj, doc) in
  let _line obj = RLine obj in
  let _text data = RText data in
  let _fix fix = RFix fix in
  let _grp obj = RGrp obj in
  let _seq obj = RSeq obj in
  let _nest obj = RNest obj in
  let _pack index obj = RPack (index, obj) in
  let _comp left right pad = RComp (left, right, pad) in
  let _fix_text data = RFText data in
  let _fix_comp left right pad = RFComp (left, right, pad) in
  let _prop_nest = PNest in
  let _prop_pack index = PPack index in
  let _join_props l r return =
    let rec _visit l r c return =
      match l, r with
      | PNest :: l1, PNest :: r1 ->
        _visit l1 r1 (c <== (List.cons _prop_nest)) return
      | (PPack l_index) :: l1, (PPack r_index) :: r1 ->
        if l_index <> r_index then return l r (c []) else
        _visit l1 r1 (c <== (List.cons (_prop_pack l_index))) return
      | _, _ ->
        return l r (c [])
    in
    _visit l r identity return
  in
  let _apply_props props term return =
    let rec _visit props return =
      match props with
      | [] -> return term
      | PNest :: props1 -> _visit props1 (return <== _nest)
      | (PPack index) :: props1 -> _visit props1 (return <== (_pack index))
    in
    _visit props return
  in
  let rec _visit_doc doc return =
    match doc with
    | DEOD -> return _eod
    | DEmpty doc1 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_empty doc2)
    | DBreak (obj, doc1) ->
      _visit_obj obj @@ fun props obj1 ->
      _apply_props props obj1 @@ fun obj2 ->
      _visit_doc doc1 @@ fun doc2 ->
      return (_break obj2 doc2)
    | DLine obj ->
      _visit_obj obj @@ fun props obj1 ->
      _apply_props props obj1 @@ fun obj2 ->
      return (_line obj2)
  and _visit_obj obj return =
    match obj with
    | DTerm term ->
      _visit_term term identity return
    | DFix fix ->
      _visit_fix fix @@ fun props fix1 ->
      return props (_fix fix1)
    | DGrp obj1 ->
      _visit_obj obj1 @@ fun props obj2 ->
      return props (_grp obj2)
    | DSeq obj1 ->
      _visit_obj obj1 @@ fun props obj2 ->
      return props (_seq obj2)
    | DComp (left, right, pad) ->
      _visit_obj left @@ fun l_props left1 ->
      _visit_obj right @@ fun r_props right1 ->
      _join_props l_props r_props @@ fun l_props1 r_props1 c_props ->
      _apply_props l_props1 left1 @@ fun left2 ->
      _apply_props r_props1 right1 @@ fun right2 ->
      return c_props (_comp left2 right2 pad)
  and _visit_fix fix return =
    match fix with
    | DFTerm term ->
      _visit_fix_term term identity return
    | DFComp (left, right, pad) ->
      _visit_fix left @@ fun l_props left1 ->
      _visit_fix right @@ fun _r_props right1 ->
      return l_props (_fix_comp left1 right1 pad)
  and _visit_term term result return =
    match term with
    | DText data ->
      return (result []) (_text data)
    | DNest term1 ->
      _visit_term term1 (result <== (List.cons _prop_nest)) return
    | DPack (index, term1) ->
      _visit_term term1 (result <== (List.cons (_prop_pack index))) return
  and _visit_fix_term term result return =
    match term with
    | DText data ->
      return (result []) (_fix_text data)
    | DNest term1 ->
      _visit_fix_term term1 (result <== (List.cons _prop_nest)) return
    | DPack (index, term1) ->
      _visit_fix_term term1 (result <== (List.cons (_prop_pack index))) return
  in
  _visit_doc doc return

let print doc return =
  let open Printf in
  let rec _print_doc doc return =
    match doc with
    | REOD -> return "EOD"
    | REmpty doc1 -> _print_doc doc1 (return <== (sprintf "Empty\n%s"))
    | RBreak (obj, doc1) ->
      _print_obj obj @@ fun obj_s ->
      _print_doc doc1 @@ fun doc1_s ->
      return (sprintf "Break %s\n%s" obj_s doc1_s)
    | RLine obj ->
      _print_obj obj @@ fun obj_s ->
      return (sprintf "Line %s" obj_s)
  and _print_obj obj return =
    let open Printf in
    match obj with
    | RText data -> return (sprintf "(Text \"%s\")" data)
    | RFix obj1 -> _print_fix obj1 (return <== (sprintf "(Fix %s)"))
    | RGrp obj1 -> _print_obj obj1 (return <== (sprintf "(Grp %s)"))
    | RSeq obj1 -> _print_obj obj1 (return <== (sprintf "(Seq %s)"))
    | RNest obj1 ->
      _print_obj obj1 (return <== (sprintf "(Nest %s)"))
    | RPack (index, obj1) ->
      _print_obj obj1 (return <== (sprintf "(Pack %d %s)" index))
    | RComp (left, right, pad) ->
      _print_obj left @@ fun left_s ->
      _print_obj right @@ fun right_s ->
      return (sprintf "(Comp %s %s %b)" left_s right_s pad)
  and _print_fix obj return =
    let open Printf in
    match obj with
    | RFText data -> return (sprintf "(Text \"%s\")" data)
    | RFComp (left, right, pad) ->
      _print_fix left @@ fun left_s ->
      _print_fix right @@ fun right_s ->
      return (sprintf "(Comp %s %s %b)" left_s right_s pad)
  in
  _print_doc doc return

let compile eDSL return =
  _broken eDSL @@ fun eDSL1 ->
  _serialize eDSL1 @@ fun eDSL2 ->
  _linearize eDSL2 @@ fun doc ->
  _fixed doc @@ fun doc1 ->
  _structurize doc1 @@ fun doc2 ->
  _denull doc2 @@ fun doc3 ->
  _identities doc3 @@ fun doc4 ->
  _reassociate doc4 @@ fun doc5 ->
  _rescope doc5 return

type state =
  { head : bool
  ; break : bool
  ; lvl : int
  ; pos : int
  ; marks : (int, int) Env.env
  }

let make_state () =
  { head = true
  ; break = false
  ; lvl = 0
  ; pos = 0
  ; marks = Env.empty
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

let get_pos state return = return state.pos
let set_pos pos state return =
  return { state with pos = pos }

let inc_pos n state return =
  return { state with pos = state.pos + n }

let get_marks state return = return state.marks
let set_marks marks state return =
  return { state with marks = marks }

let indent tab state return =
  if tab <= 0 then return state else
  get_lvl state @@ fun lvl ->
  let lvl1 = lvl + (tab - (lvl mod tab)) in
  set_lvl lvl1 state return

let newline state return =
  set_head true state @@ fun state1 ->
  set_pos 0 state1 return

let reset state return =
  set_head true state @@ fun state1 ->
  set_break false state1 @@ fun state2 ->
  set_pos 0 state2 return

let get_offset state return =
  if not state.head then return 0 else
  get_lvl state @@ fun lvl ->
  get_pos state @@ fun pos ->
  return (max 0 (lvl - pos))

let render doc tab width return =
  let _whitespace n = String.make n ' ' in
  let _pad n result return = return (result ^ (_whitespace n)) in
  let _measure obj state return =
    let rec _visit_obj obj state return =
      match obj with
      | RText data ->
        let length = String.length data in
        inc_pos length state return
      | RFix fix -> _visit_fix fix state return
      | RGrp obj1 -> _visit_obj obj1 state return
      | RSeq obj1 -> _visit_obj obj1 state return
      | RNest obj1 ->
        get_lvl state @@ fun lvl ->
        indent tab state @@ fun state1 ->
        get_offset state1 @@ fun offset ->
        inc_pos offset state1 @@ fun state2 ->
        _visit_obj obj1 state2 @@ fun state3 ->
        set_lvl lvl state3 return
      | RPack (index, obj1) ->
        let _equal l r = l = r in
        get_lvl state @@ fun lvl ->
        get_marks state @@ fun marks ->
        Env.lookup _equal index marks
          (fun _ ->
            get_pos state @@ fun pos ->
            Env.bind index pos marks @@ fun marks1 ->
            set_marks marks1 state @@ fun state1 ->
            set_lvl (max lvl pos) state1 @@ fun state2 ->
            _visit_obj obj1 state2 @@ fun state3 ->
            set_lvl lvl state3 return)
          (fun lvl1 ->
            set_lvl (max lvl lvl1) state @@ fun state1 ->
            get_offset state1 @@ fun offset ->
            inc_pos offset state1 @@ fun state2 ->
            _visit_obj obj1 state2 @@ fun state3 ->
            set_lvl lvl state3 return)
      | RComp (left, right, pad) ->
        _visit_obj left state @@ fun state1 ->
        inc_pos (if pad then 1 else 0) state1 @@ fun state2 ->
        get_head state2 @@ fun head ->
        set_head false state2 @@ fun state3 ->
        _visit_obj right state3 @@ fun state4 ->
        set_head head state4 return
    and _visit_fix fix state return =
      match fix with
      | RFText data ->
        let length = String.length data in
        inc_pos length state return
      | RFComp (left, right, pad) ->
        _visit_fix left state @@ fun state1 ->
        inc_pos (if pad then 1 else 0) state1 @@ fun state2 ->
        _visit_fix right state2 return
    in
    _visit_obj obj state @@ fun state1 ->
    get_pos state1 return
  in
  let _next_comp obj state return =
    let rec _visit_obj obj state return =
      match obj with
      | RText data ->
        let length = String.length data in
        inc_pos length state return
      | RFix fix ->
        _visit_fix fix state return
      | RGrp obj1 ->
        get_head state @@ fun head ->
        if head then _visit_obj obj1 state return else
        _measure obj1 state @@ fun obj_end_pos ->
        set_pos obj_end_pos state return
      | RSeq obj1 ->
        _visit_obj obj1 state return
      | RNest obj1 ->
        get_lvl state @@ fun lvl ->
        indent tab state @@ fun state1 ->
        get_offset state1 @@ fun offset ->
        inc_pos offset state1 @@ fun state2 ->
        _visit_obj obj1 state2 @@ fun state3 ->
        set_lvl lvl state3 return
      | RPack (index, obj1) ->
        let _equal l r = l = r in
        get_lvl state @@ fun lvl ->
        get_marks state @@ fun marks ->
        Env.lookup _equal index marks
          (fun _ ->
            get_pos state @@ fun pos ->
            Env.bind index pos marks @@ fun marks1 ->
            set_marks marks1 state @@ fun state1 ->
            set_lvl (max lvl pos) state1 @@ fun state2 ->
            _visit_obj obj1 state2 @@ fun state3 ->
            set_lvl lvl state3 return)
          (fun lvl1 ->
            set_lvl (max lvl lvl1) state @@ fun state1 ->
            get_offset state1 @@ fun offset ->
            inc_pos offset state1 @@ fun state2 ->
            _visit_obj obj1 state2 @@ fun state3 ->
            set_lvl lvl state3 return)
      | RComp (left, _right, _pad) ->
        _visit_obj left state return
    and _visit_fix fix state return =
      match fix with
      | RFText data ->
        let length = String.length data in
        inc_pos length state return
      | RFComp (left, right, pad) ->
        _visit_fix left state @@ fun state1 ->
        inc_pos (if pad then 1 else 0) state1 @@ fun state2 ->
        _visit_fix right state2 return
    in
    _visit_obj obj state @@ fun state1 ->
    get_pos state1 return
  in
  let _will_fit obj state =
    _measure obj state @@ fun obj_end_pos ->
    obj_end_pos <= width
  in
  let _should_break obj state =
    get_break state @@ fun break ->
    if break then true else
    _next_comp obj state @@ fun next_comp_pos ->
    width < next_comp_pos
  in
  let rec _visit_doc doc state return =
    reset state @@ fun state1 ->
    match doc with
    | REOD -> return state1 ""
    | REmpty doc1 ->
      _visit_doc doc1 state1 @@ fun state2 doc2 ->
      return state2 ("\n" ^ doc2)
    | RBreak (obj, doc1) ->
      _visit_obj obj state1 "" @@ fun state2 obj1 ->
      reset state2 @@ fun state3 ->
      _visit_doc doc1 state3 @@ fun state4 doc2 ->
      return state4 (obj1 ^ "\n" ^ doc2)
    | RLine obj ->
      _visit_obj obj state1 "" return
  and _visit_obj obj state result return =
    match obj with
    | RText data ->
      let length = String.length data in
      inc_pos length state @@ fun state1 ->
      return state1 (result ^ data)
    | RFix fix ->
      _visit_fix fix state result return
    | RGrp obj1 ->
      get_break state @@ fun break ->
      set_break false state @@ fun state1 ->
      _visit_obj obj1 state1 result @@ fun state2 result1 ->
      set_break break state2 @@ fun state3 ->
      return state3 result1
    | RSeq obj1 ->
      if _will_fit obj1 state
      then _visit_obj obj1 state result return else
      get_break state @@ fun break ->
      set_break true state @@ fun state1 ->
      _visit_obj obj1 state1 result @@ fun state2 result1 ->
      set_break break state2 @@ fun state3 ->
      return state3 result1
    | RNest obj1 ->
      get_lvl state @@ fun lvl ->
      indent tab state @@ fun state1 ->
      get_offset state1 @@ fun offset ->
      inc_pos offset state1 @@ fun state2 ->
      _pad offset result @@ fun result1 ->
      _visit_obj obj1 state2 result1 @@ fun state3 result2 ->
      set_lvl lvl state3 @@ fun state4 ->
      return state4 result2
    | RPack (index, obj1) ->
      let _equal l r = l = r in
      get_lvl state @@ fun lvl ->
      get_marks state @@ fun marks ->
      Env.lookup _equal index marks
        (fun _ ->
          get_pos state @@ fun pos ->
          Env.bind index pos marks @@ fun marks1 ->
          set_marks marks1 state @@ fun state1 ->
          set_lvl (max lvl pos) state1 @@ fun state2 ->
          _visit_obj obj1 state2 result @@ fun state3 result1 ->
          set_lvl lvl state3 @@ fun state4 ->
          return state4 result1)
        (fun lvl1 ->
          set_lvl (max lvl lvl1) state @@ fun state1 ->
          get_offset state1 @@ fun offset ->
          inc_pos offset state1 @@ fun state2 ->
          _pad offset result @@ fun result1 ->
          _visit_obj obj1 state2 result1 @@ fun state3 result2 ->
          set_lvl lvl state3 @@ fun state4 ->
          return state4 result2)
    | RComp (left, right, pad) ->
      _visit_obj left state result @@ fun state1 result1 ->
      inc_pos (if pad then 1 else 0) state1 @@ fun state2 ->
      set_head false state2 @@ fun state3 ->
      if _should_break right state3
      then
        newline state1 @@ fun state2 ->
        get_offset state2 @@ fun offset ->
        inc_pos offset state2 @@ fun state3 ->
        _pad offset (result1 ^ "\n") @@ fun result2 ->
        _visit_obj right state3 result2 return
      else
        _pad (if pad then 1 else 0) result1 @@ fun result2 ->
        _visit_obj right state3 result2 return
  and _visit_fix fix state result return =
    match fix with
    | RFText data ->
      let length = String.length data in
      inc_pos length state @@ fun state1 ->
      return state1 (result ^ data)
    | RFComp (left, right, pad) ->
      _visit_fix left state result @@ fun state1 result1 ->
      let padding = if pad then 1 else 0 in
      _pad padding result1 @@ fun result2 ->
      inc_pos padding state1 @@ fun state2 ->
      _visit_fix right state2 result2 return
  in
  _visit_doc doc (make_state ()) @@ fun _state result ->
  return result
