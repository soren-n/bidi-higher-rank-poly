open Util
open Extra
open Syntax
open Context
open Print
open Typeset

(*
  An implementation of:
  Complete and easy bidirectional typechecking for higher-rank polymorphism
  https://arxiv.org/pdf/1306.6032.pdf
*)

type 'r fail = Typeset.eDSL -> 'r
type ('a, 'r) return = ('a -> 'r) -> 'r

(*
  Implementation of figure 8.
  Applying a context, as a substitution, to a type.

  Note on deviation from paper:
  The context is an implementation detail;
  It is due to deferred substitution from the subtype relation.
*)
let rec norm_poly poly tctx return =
  match poly with
  | PNothing -> return poly_nothing
  | PUnit -> return poly_unit
  | PParam param ->
    lookup_t param tctx
      (fun _msg ->
        return (poly_param param))
      (fun poly1 ->
        match poly1 with
        | PVar _ -> norm_poly poly1 tctx return
        | _ -> assert false (* Invariant *))
  | PVar exist ->
    begin match !exist with
    | None -> return (poly_var exist)
    | Some mono ->
      norm_mono mono tctx @@ fun mono1 ->
      return (poly_mono mono1)
    end
  | PArrow (dom, codom) ->
    norm_poly dom tctx @@ fun dom1 ->
    norm_poly codom tctx @@ fun codom1 ->
    return (poly_arrow dom1 codom1)
  | PForall (param, poly1) ->
    norm_poly poly1 tctx @@ fun poly2 ->
    return (poly_forall param poly2)
  | PMono mono ->
    norm_mono mono tctx @@ fun mono1 ->
    return (poly_mono mono1)
and norm_mono mono tctx return =
  match mono with
  | MNothing -> return mono_nothing
  | MUnit -> return mono_unit
  | MParam param ->
    lookup_t param tctx
      (fun _msg ->
        return (mono_param param))
      (fun poly1 ->
        match poly1 with
        | PVar exist -> norm_mono (mono_var exist) tctx return
        | _ -> assert false (* Invariant *))
  | MVar exist ->
    begin match !exist with
    | None -> return (mono_var exist)
    | Some mono ->
      norm_mono mono tctx return
    end
  | MArrow (dom, codom) ->
    norm_mono dom tctx @@ fun dom1 ->
    norm_mono codom tctx @@ fun codom1 ->
    return (mono_arrow dom1 codom1)

let extend label tctx return =
  let var = poly_var (ref None) in
  bind_t label var tctx return

(*
  Implementation of figure 10.
  Instantiate a existential variable, such that the instantiation is a
  subtype or supertype of a given type, depending on whether we are
  instantiating the left or right hand side of the subtype relation.
*)
let rec instantiate_l_poly l_exist poly tctx =
  match poly with
  | PNothing -> l_exist := Some mono_nothing
  | PUnit -> l_exist := Some mono_unit
  | PVar r_exist -> r_exist := Some (mono_var l_exist)
  | PParam name ->
    lookup_t name tctx
      (fun _msg ->
        l_exist := Some (mono_param name))
      (fun poly1 ->
        instantiate_l_poly l_exist poly1 tctx)
  | PArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    l_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instantiate_r_poly dom dom_exist tctx;
    norm_poly codom tctx @@ fun codom1 ->
    instantiate_l_poly codom_exist codom1 tctx
  | PForall (param, poly1) ->
    extend param tctx @@ fun tctx1 ->
    instantiate_l_poly l_exist poly1 tctx1
  | PMono mono ->
    instantiate_l_mono l_exist mono tctx
and instantiate_l_mono l_exist mono tctx =
  match mono with
  | MNothing -> l_exist := Some mono_nothing
  | MUnit -> l_exist := Some mono_unit
  | MVar r_exist -> r_exist := Some (mono_var l_exist)
  | MParam name ->
    lookup_t name tctx
      (fun _msg ->
        l_exist := Some (mono_param name))
      (fun poly1 ->
        instantiate_l_poly l_exist poly1 tctx)
  | MArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    l_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instantiate_r_mono dom dom_exist tctx;
    norm_mono codom tctx @@ fun codom1 ->
    instantiate_l_mono codom_exist codom1 tctx
and instantiate_r_poly poly r_exist tctx =
  match poly with
  | PNothing -> r_exist := Some mono_nothing
  | PUnit -> r_exist := Some mono_unit
  | PVar l_exist -> l_exist := Some (mono_var r_exist)
  | PParam name ->
    lookup_t name tctx
      (fun _msg ->
        r_exist := Some (mono_param name))
      (fun poly1 ->
        instantiate_r_poly poly1 r_exist tctx)
  | PArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    r_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instantiate_l_poly dom_exist dom tctx;
    norm_poly codom tctx @@ fun codom1 ->
    instantiate_r_poly codom1 codom_exist tctx
  | PForall (param, poly1) ->
    extend param tctx @@ fun tctx1 ->
    instantiate_r_poly poly1 r_exist tctx1
  | PMono mono ->
    instantiate_r_mono mono r_exist tctx
and instantiate_r_mono mono r_exist tctx =
  match mono with
  | MNothing -> r_exist := Some mono_nothing
  | MUnit -> r_exist := Some mono_unit
  | MVar l_exist -> l_exist := Some (mono_var r_exist)
  | MParam name ->
    lookup_t name tctx
      (fun _msg ->
        r_exist := Some (mono_param name))
      (fun poly1 ->
        instantiate_r_poly poly1 r_exist tctx)
  | MArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    r_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instantiate_l_mono dom_exist dom tctx;
    norm_mono codom tctx @@ fun codom1 ->
    instantiate_r_mono codom1 codom_exist tctx

let rec acyclic_poly l_exist r_poly fail return =
  let rec _visit poly return =
    match poly with
    | PVar r_exist ->
      if not (exist_equal l_exist r_exist) then return () else
      let ctx = Naming.make_ctx () in
      layout_poly ctx r_poly @@ fun r_poly1 ->
      fail (~$"Type is cyclic" <+> grp r_poly1)
    | PArrow (dom, codom) ->
      _visit dom @@ fun () ->
      _visit codom return
    | PForall (_param, poly1) ->
      _visit poly1 return
    | PMono mono ->
      acyclic_mono l_exist mono fail return
    | PNothing | PUnit | PParam _ -> return ()
  in
  _visit r_poly return
and acyclic_mono l_exist r_mono fail return =
  let rec _visit mono return =
    match mono with
    | MVar r_exist ->
      if not (exist_equal l_exist r_exist) then return () else
      let ctx = Naming.make_ctx () in
      layout_mono ctx r_mono @@ fun r_mono1 ->
      fail (~$"Type is cyclic" <+> grp r_mono1)
    | MArrow (dom, codom) ->
      _visit dom @@ fun () ->
      _visit codom return
    | MNothing | MUnit | MParam _ -> return ()
  in
  _visit r_mono return

let rec mono_2_poly mono return =
  match mono with
  | MNothing -> return poly_nothing
  | MUnit -> return poly_unit
  | MParam label -> return (poly_param label)
  | MVar exist -> return (poly_var exist)
  | MArrow (dom, codom) ->
    mono_2_poly dom @@ fun dom1 ->
    mono_2_poly codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)

let subtype left right tctx fail return =
  let _msg left right tctx =
    let ctx = Naming.make_ctx () in
    norm_poly left tctx @@ fun left1 ->
    norm_poly right tctx @@ fun right1 ->
    layout_poly ctx left1 @@ fun left_s ->
    layout_poly ctx right1 @@ fun right_s ->
    seq (~$"Subtyping" <+>
      nest (seq ((grp left_s) <+> ~$"<:" <!+> (grp right_s))) <+>
    ~$"failed")
  in
  let _fail_end fail left right tctx () =
    fail (_msg left right tctx)
  in
  let _fail_cont fail left right tctx msg =
    fail ((_msg left right tctx) </> ~$"because" <!+> msg)
  in
  let rec _subtype left right tctx fail return =
    let _fail = _fail_end fail left right tctx in
    let __fail = _fail_cont fail left right tctx in
    match left, right with
    | PNothing, PNothing -> return ()
    | PUnit, PUnit -> return ()
    | PParam l_name, PParam r_name ->
      lookup_t l_name tctx
        (fun _msg ->
          if label_equal l_name r_name
          then return ()
          else _fail ())
        (fun left1 ->
          _subtype left1 right tctx fail return)
    | PParam param, _ ->
      lookup_t param tctx
        (fun _msg -> _fail ())
        (fun left1 ->
          _subtype left1 right tctx fail return)
    | _, PParam param ->
      lookup_t param tctx
        (fun _msg -> _fail ())
        (fun right1 ->
          _subtype left right1 tctx fail return)
    | PVar l_exist, PVar r_exist ->
      if exist_equal l_exist r_exist then return () else
      begin instantiate_l_poly l_exist right tctx; return () end
    | PArrow (l_dom, l_codom), PArrow (r_dom, r_codom) ->
      _subtype r_dom l_dom tctx __fail @@ fun () ->
      norm_poly l_codom tctx @@ fun l_codom1 ->
      norm_poly r_codom tctx @@ fun r_codom1 ->
      _subtype l_codom1 r_codom1 tctx __fail return
    | PMono l_mono, PMono r_mono ->
      mono_2_poly l_mono @@ fun left1 ->
      mono_2_poly r_mono @@ fun right1 ->
      _subtype left1 right1 tctx fail return
    | PMono l_mono, _ ->
      mono_2_poly l_mono @@ fun left1 ->
      _subtype left1 right tctx fail return
    | _, PMono r_mono ->
      mono_2_poly r_mono @@ fun right1 ->
      _subtype left right1 tctx fail return
    | PForall (param, left1), _ ->
      extend param tctx @@ fun tctx1 ->
      _subtype left1 right tctx1 __fail return
    | _, PForall (_param, right1) ->
      _subtype left right1 tctx __fail return
    | PVar l_exist, _ ->
      acyclic_poly l_exist right __fail @@ fun () ->
      begin instantiate_l_poly l_exist right tctx; return () end
    | _, PVar r_exist ->
      acyclic_poly r_exist left __fail @@ fun () ->
      begin instantiate_r_poly left r_exist tctx; return () end
    | _, _ ->
      _fail ()
  in
  _subtype left right tctx fail return

let _recursion_allowed tctx poly =
  let rec _visit_poly poly =
    match poly with
    | PNothing -> false
    | PUnit -> false
    | PParam name ->
      lookup_t name tctx
        (fun _msg -> false)
        (fun poly1 -> _visit_poly poly1)
    | PVar exist ->
      begin match !exist with
      | None -> false
      | Some mono -> _visit_mono mono
      end
    | PArrow _ -> true
    | PForall (_name, poly1) ->
      _visit_poly poly1
    | PMono mono ->
      _visit_mono mono
  and _visit_mono mono =
    match mono with
    | MNothing -> false
    | MUnit -> false
    | MParam name ->
      lookup_t name tctx
        (fun _msg -> false)
        (fun poly1 -> _visit_poly poly1)
    | MVar exist ->
      begin match !exist with
      | None -> false
      | Some mono -> _visit_mono mono
      end
    | MArrow _ -> true
  in
  _visit_poly poly

let rec synth_expr expr tctx fail return =
  match expr with
  | EUndefined -> return poly_nothing
  | EUnit -> return poly_unit
  | EVar name -> lookup_v name tctx fail return
  | EAbs (param, body) ->
    let dom = poly_var (ref None) in
    let codom = poly_var (ref None) in
    bind_v param dom tctx @@ fun tctx1 ->
    check_stmt body codom tctx1 fail @@ fun () ->
    return (poly_arrow dom codom)
  | EApp (func, arg) ->
    synth_expr func tctx fail @@ fun func_t ->
    norm_poly func_t tctx @@ fun func_t1 ->
    synth_apply func_t1 arg tctx fail return
  | EAnno (expr1, poly) ->
    check_expr expr1 poly tctx fail @@ fun () ->
    return poly
and synth_stmt stmt tctx fail return =
  match stmt with
  | SDecl (name, poly, stmt1) ->
    if not (_recursion_allowed tctx poly)
    then synth_stmt stmt1 tctx fail return else
    bind_v name poly tctx @@ fun tctx1 ->
    synth_stmt stmt1 tctx1 fail return
  | SDefn (name, expr, stmt1) ->
    synth_expr expr tctx fail @@ fun expr_t ->
    bind_v name expr_t tctx @@ fun tctx1 ->
    synth_stmt stmt1 tctx1 fail return
  | SExpr expr ->
    synth_expr expr tctx fail return
and synth_apply poly expr tctx fail return =
  match poly with
  | PVar exist ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    check_expr expr (poly_var dom_exist) tctx fail @@ fun () ->
    return (poly_var codom_exist)
  | PArrow (dom, codom) ->
    check_expr expr dom tctx fail @@ fun () ->
    return codom
  | PForall (param, poly1) ->
    extend param tctx @@ fun tctx1 ->
    synth_apply poly1 expr tctx1 fail return
  | _ -> assert false (* Invariant *)
and check_expr expr poly tctx fail return =
  match expr, poly with
  | EUnit, PUnit -> return ()
  | EAbs (param, body), PArrow (dom, codom) ->
    bind_v param dom tctx @@ fun tctx1 ->
    check_stmt body codom tctx1 fail return
  | _, PForall (_param, poly1) ->
    check_expr expr poly1 tctx fail return
  | _, _ ->
    synth_expr expr tctx fail @@ fun expr_t ->
    norm_poly expr_t tctx @@ fun expr_t1 ->
    norm_poly poly tctx @@ fun poly1 ->
    subtype expr_t1 poly1 tctx fail return
and check_stmt stmt poly tctx fail return =
  match stmt with
  | SDecl (name, poly1, stmt1) ->
    if not (_recursion_allowed tctx poly1)
    then check_stmt stmt1 poly tctx fail return else
    bind_v name poly1 tctx @@ fun tctx1 ->
    check_stmt stmt1 poly tctx1 fail return
  | SDefn (name, expr, stmt1) ->
    synth_expr expr tctx fail @@ fun expr_t ->
    bind_v name expr_t tctx @@ fun tctx1 ->
    check_stmt stmt1 poly tctx1 fail return
  | SExpr expr ->
    check_expr expr poly tctx fail return

let rec check_prog prog tctx fail return =
  match prog with
  | PEnd -> return tctx
  | PDecl (name, poly, prog1) ->
    bind_v name poly tctx @@ fun tctx1 ->
    check_prog prog1 tctx1 fail return
  | PDefn (name, expr, prog1) ->
    synth_expr expr tctx fail @@ fun expr_t ->
    bind_v name expr_t tctx @@ fun tctx1 ->
    check_prog prog1 tctx1 fail return

let generalize poly return =
  let ctx = Naming.make_ctx () in
  let exists = ref Env.empty in
  let rec _visit_poly poly env return =
    match poly with
    | PParam from_label ->
      Env.lookup label_equal from_label env
        (fun () -> assert false (* Invariant *))
        (fun to_label ->
          return (poly_param to_label))
    | PVar exist ->
      begin match !exist with
      | Some mono ->
        _visit_mono mono env @@ fun mono1 ->
        return (poly_mono mono1)
      | None ->
        let _exists = !exists in
        Env.lookup exist_equal exist _exists
          (fun () ->
            Naming.sample_label ctx @@ fun label ->
            Env.bind exist label _exists @@ fun exists1 ->
            exists := exists1;
            return (poly_param label))
          (fun label ->
            return (poly_param label))
      end
    | PArrow (dom, codom) ->
      _visit_poly dom env @@ fun dom1 ->
      _visit_poly codom env @@ fun codom1 ->
      return (poly_arrow dom1 codom1)
    | PForall (from_label, poly1) ->
      Naming.sample_label ctx @@ fun to_label ->
      Env.bind from_label to_label env @@ fun env1 ->
      _visit_poly poly1 env1 @@ fun poly2 ->
      return (poly_forall to_label poly2)
    | PMono mono ->
      _visit_mono mono env @@ fun mono1 ->
      return (poly_mono mono1)
    | PNothing | PUnit -> return poly
  and _visit_mono mono env return =
    match mono with
    | MParam from_label ->
      Env.lookup label_equal from_label env
        (fun () -> assert false (* Invariant *))
        (fun to_label ->
          return (mono_param to_label))
    | MVar exist ->
      begin match !exist with
      | Some mono ->
        _visit_mono mono env return
      | None ->
        let _exists = !exists in
        Env.lookup exist_equal exist _exists
          (fun () ->
            Naming.sample_label ctx @@ fun label ->
            Env.bind exist label _exists @@ fun exists1 ->
            exists := exists1;
            return (mono_param label))
          (fun label ->
            return (mono_param label))
      end
    | MArrow (dom, codom) ->
      _visit_mono dom env @@ fun dom1 ->
      _visit_mono codom env @@ fun codom1 ->
      return (mono_arrow dom1 codom1)
    | MNothing | MUnit -> return mono
  in
  _visit_poly poly Env.empty @@ fun poly1 ->
  Env.values !exists @@ fun labels ->
  return (List.fold_rev poly1 poly_forall labels)
