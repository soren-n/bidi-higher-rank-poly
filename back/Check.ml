open Printf
open Util
open Extra
open Syntax
open Context
open Print

let rec norm_poly poly return =
  match poly with
  | PNothing -> return poly_nothing
  | PUnit -> return poly_unit
  | PParam name -> return (poly_param name)
  | PVar exist ->
    begin match !exist with
    | None -> return (poly_var exist)
    | Some mono ->
      norm_mono mono @@ fun mono1 ->
      return (poly_mono mono1)
    end
  | PArrow (dom, codom) ->
    norm_poly dom @@ fun dom1 ->
    norm_poly codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)
  | PForall (param, poly1) ->
    norm_poly poly1 @@ fun poly2 ->
    return (poly_forall param poly2)
  | PMono mono ->
    norm_mono mono @@ fun mono1 ->
    return (poly_mono mono1)
and norm_mono mono return =
  match mono with
  | MNothing -> return mono_nothing
  | MUnit -> return mono_unit
  | MParam name -> return (mono_param name)
  | MVar exist ->
    begin match !exist with
    | None -> return (mono_var exist)
    | Some mono ->
      norm_mono mono return
    end
  | MArrow (dom, codom) ->
    norm_mono dom @@ fun dom1 ->
    norm_mono codom @@ fun codom1 ->
    return (mono_arrow dom1 codom1)

let extend label ctx return =
  let var = poly_var (ref None) in
  bind_t label var ctx return

let rec instantiate_l l_exist poly ctx fail return =
  match poly with
  | PNothing ->
    l_exist := Some MNothing;
    return ()
  | PUnit ->
    l_exist := Some MUnit;
    return ()
  | PVar r_exist ->
    r_exist := Some (mono_var l_exist);
    return ()
  | PParam name ->
    lookup_t name ctx
      (fun _msg ->
        l_exist := Some (mono_param name);
        return ())
      (fun poly1 ->
        instantiate_l l_exist poly1 ctx fail return)
  | PArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    l_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instantiate_r dom dom_exist ctx fail @@ fun () ->
    norm_poly codom @@ fun codom1 ->
    instantiate_l codom_exist codom1 ctx fail return
  | PForall (param, poly1) ->
    extend param ctx @@ fun ctx1 ->
    instantiate_l l_exist poly1 ctx1 fail return
  | PMono mono ->
    l_exist := Some mono;
    return ()
and instantiate_r poly r_exist ctx fail return =
  match poly with
  | PNothing ->
    r_exist := Some MNothing;
    return ()
  | PUnit ->
    r_exist := Some MUnit;
    return ()
  | PVar l_exist ->
    l_exist := Some (mono_var r_exist);
    return ()
  | PParam name ->
    lookup_t name ctx
      (fun _msg ->
        r_exist := Some (mono_param name);
        return ())
      (fun poly1 ->
        instantiate_r poly1 r_exist ctx fail return)
  | PArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    r_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instantiate_l dom_exist dom ctx fail @@ fun () ->
    norm_poly codom @@ fun codom1 ->
    instantiate_r codom1 codom_exist ctx fail return
  | PForall (param, poly1) ->
    extend param ctx @@ fun ctx1 ->
    instantiate_r poly1 r_exist ctx1 fail return
  | PMono mono ->
    r_exist := Some mono;
    return ()

let rec acyclic_poly l_exist r_poly fail return =
  let rec _visit poly return =
    match poly with
    | PVar r_exist ->
      if exist_equal l_exist r_exist
      then
        let ctx = Naming.make_ctx () in
        print_poly ctx r_poly @@ fun r_poly1 ->
        fail (sprintf "Type is cyclic %s" r_poly1)
      else return ()
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
      if exist_equal l_exist r_exist
      then
        let ctx = Naming.make_ctx () in
        print_mono ctx r_mono @@ fun r_mono1 ->
        fail (sprintf "Type is cyclic %s" r_mono1)
      else return ()
    | MArrow (dom, codom) ->
      _visit dom @@ fun () ->
      _visit codom return
    | MNothing | MUnit | MParam _ -> return ()
  in
  _visit r_mono return

let rec mono_poly mono return =
  match mono with
  | MNothing -> return poly_nothing
  | MUnit -> return poly_unit
  | MParam label -> return (poly_param label)
  | MVar exist -> return (poly_var exist)
  | MArrow (dom, codom) ->
    mono_poly dom @@ fun dom1 ->
    mono_poly codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)

let subtype left right ctx fail return =
  let _msg left right =
    let ctx = Naming.make_ctx () in
    print_poly ctx left @@ fun left_s ->
    print_poly ctx right @@ fun right_s ->
    sprintf "Subtyping %s <: %s failed" left_s right_s
  in
  let _fail_end fail left right () =
    fail (_msg left right)
  in
  let _fail_cont fail left right msg =
    fail (sprintf "%s because\n%s" (_msg left right) msg)
  in
  let rec _subtype left right ctx fail return =
    let _fail = _fail_end fail left right in
    let __fail = _fail_cont fail left right in
    match left, right with
    | PNothing, PNothing -> return ()
    | PUnit, PUnit -> return ()
    | PParam left1, PParam right1 ->
      if label_equal left1 right1 then return ()
      else _fail ()
    | PVar l_exist, PVar r_exist ->
      if exist_equal l_exist r_exist then return ()
      else instantiate_l l_exist right ctx __fail return
    | PArrow (l_dom, l_codom), PArrow (r_dom, r_codom) ->
      _subtype r_dom l_dom ctx __fail @@ fun () ->
      norm_poly l_codom @@ fun l_codom1 ->
      norm_poly r_codom @@ fun r_codom1 ->
      _subtype l_codom1 r_codom1 ctx __fail return
    | PMono l_mono, PMono r_mono ->
      mono_poly l_mono @@ fun left1 ->
      mono_poly r_mono @@ fun right1 ->
      _subtype left1 right1 ctx fail return
    | PMono l_mono, _ ->
      mono_poly l_mono @@ fun left1 ->
      _subtype left1 right ctx fail return
    | _, PMono r_mono ->
      mono_poly r_mono @@ fun right1 ->
      _subtype left right1 ctx fail return
    | PForall (param, left1), _ ->
      extend param ctx @@ fun ctx1 ->
      _subtype left1 right ctx1 __fail return
    | _, PForall (_param, right1) ->
      _subtype left right1 ctx __fail return
    | PVar l_exist, _ ->
      acyclic_poly l_exist right __fail @@ fun () ->
      instantiate_l l_exist right ctx __fail return
    | _, PVar r_exist ->
      acyclic_poly r_exist left __fail @@ fun () ->
      instantiate_r left r_exist ctx __fail return
    | _, _ ->
      _fail ()
  in
  _subtype left right ctx fail return

let rec synth expr ctx fail return =
  match expr with
  | EUndefined -> return poly_nothing
  | EUnit -> return poly_unit
  | EVar name -> lookup_v name ctx fail return
  | EAbs (param, body) ->
    let dom = poly_var (ref None) in
    let codom = poly_var (ref None) in
    bind_v param dom ctx @@ fun ctx1 ->
    check body codom ctx1 fail @@ fun () ->
    return (poly_arrow dom codom)
  | EApp (func, arg) ->
    synth func ctx fail @@ fun func_t ->
    norm_poly func_t @@ fun func_t1 ->
    synth_apply func_t1 arg ctx fail return
  | EAnno (expr1, poly) ->
    check expr1 poly ctx fail @@ fun () ->
    return poly
and synth_apply poly expr ctx fail return =
  match poly with
  | PVar exist ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    check expr (poly_var dom_exist) ctx fail @@ fun () ->
    return (poly_var codom_exist)
  | PArrow (dom, codom) ->
    check expr dom ctx fail @@ fun () ->
    return codom
  | PForall (param, poly1) ->
    extend param ctx @@ fun ctx1 ->
    synth_apply poly1 expr ctx1 fail return
  | _ -> assert false
and check expr poly ctx fail return =
  match expr, poly with
  | EUnit, PUnit -> return ()
  | EAbs (param, body), PArrow (dom, codom) ->
    bind_v param dom ctx @@ fun ctx1 ->
    check body codom ctx1 fail return
  | _, PForall (_param, poly1) ->
    check expr poly1 ctx fail return
  | _, _ ->
    synth expr ctx fail @@ fun expr_t ->
    norm_poly expr_t @@ fun expr_t1 ->
    norm_poly poly @@ fun poly1 ->
    subtype expr_t1 poly1 ctx fail return

let generalize poly return =
  let ctx = Naming.make_ctx () in
  let exists = ref Env.empty in
  let rec _visit_poly poly env return =
    match poly with
    | PParam from_label ->
      Env.lookup label_equal from_label env
        (fun () -> assert false)
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
        (fun () -> assert false)
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
