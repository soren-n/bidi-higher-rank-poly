open Printf
open Syntax
open Context
open Print

let rec apply_poly ctx poly return =
  match poly with
  | PUnit -> return poly_unit
  | PParam name -> return (poly_param name)
  | PVar exist ->
    begin match !exist with
    | None -> return (poly_var exist)
    | Some mono ->
      apply_mono ctx mono @@ fun mono1 ->
      return (poly_mono mono1)
    end
  | PArrow (dom, codom) ->
    apply_poly ctx dom @@ fun dom1 ->
    apply_poly ctx codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)
  | PForall (param, poly1) ->
    apply_poly ctx poly1 @@ fun poly2 ->
    return (poly_forall param poly2)
  | PMono mono ->
    apply_mono ctx mono @@ fun mono1 ->
    return (poly_mono mono1)
and apply_mono ctx mono return =
  match mono with
  | MUnit -> return mono_unit
  | MParam name -> return (mono_param name)
  | MVar exist ->
    begin match !exist with
    | None -> return (mono_var exist)
    | Some mono ->
      apply_mono ctx mono return
    end
  | MArrow (dom, codom) ->
    apply_mono ctx dom @@ fun dom1 ->
    apply_mono ctx codom @@ fun codom1 ->
    return (mono_arrow dom1 codom1)

let rec valid_poly poly ctx fail return =
  match poly with
  | PUnit -> return ()
  | PParam name -> bound name ctx fail return
  | PVar exist ->
    begin match !exist with
    | None -> return ()
    | Some mono -> valid_mono mono ctx fail return
    end
  | PArrow (dom, codom) ->
    valid_poly dom ctx fail @@ fun () ->
    valid_poly codom ctx fail return
  | PForall (param, poly1) ->
    extend param ctx @@ fun ctx1 ->
    valid_poly poly1 ctx1 fail return
  | PMono mono ->
    valid_mono mono ctx fail return
and valid_mono mono ctx fail return =
  match mono with
  | MUnit -> return ()
  | MParam name -> bound name ctx fail return
  | MVar exist ->
    begin match !exist with
    | None -> return ()
    | Some mono1 -> valid_mono mono1 ctx fail return
    end
  | MArrow (dom, codom) ->
    valid_mono dom ctx fail @@ fun () ->
    valid_mono codom ctx fail return

let rec subst_poly param to_exist poly return =
  match poly with
  | PUnit -> return poly
  | PParam name ->
    if param = name
    then return (poly_var to_exist)
    else return poly
  | PVar from_exist ->
    begin match !from_exist with
    | None -> return poly
    | Some mono ->
      subst_mono param to_exist mono @@ fun mono1 ->
      from_exist := Some mono1;
      return poly
    end
  | PArrow (dom, codom) ->
    subst_poly param to_exist dom @@ fun dom1 ->
    subst_poly param to_exist codom @@ fun codom1 ->
    return (poly_arrow dom1 codom1)
  | PForall (param, poly1) ->
    subst_poly param to_exist poly1 @@ fun poly2 ->
    return (poly_forall param poly2)
  | PMono mono ->
    subst_mono param to_exist mono @@ fun mono1 ->
    return (poly_mono mono1)
and subst_mono param to_exist mono return =
  match mono with
  | MUnit -> return mono
  | MParam name ->
    if param = name
    then return (mono_var to_exist)
    else return mono
  | MVar from_exist ->
    begin match !from_exist with
    | None -> return mono
    | Some mono1 ->
      subst_mono param to_exist mono1 @@ fun mono2 ->
      from_exist := Some mono2;
      return mono
    end
  | MArrow (dom, codom) ->
    subst_mono param to_exist dom @@ fun dom1 ->
    subst_mono param to_exist codom @@ fun codom1 ->
    return (mono_arrow dom1 codom1)

let rec instance_l l_exist poly ctx fail return =
  match poly with
  | PVar r_exist ->
    r_exist := Some (mono_var l_exist);
    return ()
  | PArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    l_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instance_r dom dom_exist ctx fail @@ fun () ->
    apply_poly ctx codom @@ fun codom1 ->
    instance_l codom_exist codom1 ctx fail return
  | PForall (param, poly1) ->
    extend param ctx @@ fun ctx1 ->
    instance_l l_exist poly1 ctx1 fail return
  | PMono mono ->
    valid_mono mono ctx fail @@ fun () ->
    l_exist := Some mono;
    return ()
  | _ -> assert false (* Unreachable by invariant *)
and instance_r poly r_exist ctx fail return =
  match poly with
  | PVar l_exist ->
    l_exist := Some (mono_var r_exist);
    return ()
  | PArrow (dom, codom) ->
    let dom_exist = ref None in
    let codom_exist = ref None in
    r_exist := Some (mono_arrow
      (mono_var dom_exist)
      (mono_var codom_exist));
    instance_l dom_exist dom ctx fail @@ fun () ->
    apply_poly ctx codom @@ fun codom1 ->
    instance_r codom1 codom_exist ctx fail return
  | PForall (param, poly1) ->
    let l_exist = ref None in
    subst_poly param l_exist poly1 @@ fun poly2 ->
    instance_r poly2 r_exist ctx fail return
  | PMono mono ->
    valid_mono mono ctx fail @@ fun () ->
    r_exist := Some mono;
    return ()
  | _ -> assert false (* Unreachable by invariant *)

let rec acyclic_poly l_exist r_poly fail return =
  let rec _visit poly return =
    match poly with
    | PVar r_exist ->
      if l_exist == r_exist
      then
        print_poly r_poly @@ fun r_poly1 ->
        fail (sprintf "Type is cyclic %s" r_poly1)
      else return ()
    | PArrow (dom, codom) ->
      _visit dom @@ fun () ->
      _visit codom return
    | PForall (_param, poly1) ->
      _visit poly1 return
    | PMono mono ->
      acyclic_mono l_exist mono fail return
    | PUnit | PParam _ -> return ()
  in
  _visit r_poly return
and acyclic_mono l_exist r_mono fail return =
  let rec _visit mono return =
    match mono with
    | MVar r_exist ->
      if l_exist == r_exist
      then
        print_mono r_mono @@ fun r_mono1 ->
        fail (sprintf "Type is cyclic %s" r_mono1)
      else return ()
    | MArrow (dom, codom) ->
      _visit dom @@ fun () ->
      _visit codom return
    | MUnit | MParam _ -> return ()
  in
  _visit r_mono return

let subtype left right ctx fail return =
  let _fail left1 right1 =
    print_poly left1 @@ fun left2 ->
    print_poly right1 @@ fun right2 ->
    fail (sprintf "Failed %s <: %s" left2 right2)
  in
  let rec _subtype left right ctx return =
    match left, right with
    | PUnit, PUnit -> return ()
    | PParam left1, PParam right1 ->
      if left1 = right1 then return () else _fail left right
    | PVar l_exist, PVar r_exist ->
      if l_exist == r_exist then return ()
      else instance_l l_exist right ctx fail return
    | PVar l_exist, _ ->
      acyclic_poly l_exist right fail @@ fun () ->
      instance_l l_exist right ctx fail return
    | _, PVar r_exist ->
      acyclic_poly r_exist left fail @@ fun () ->
      instance_r left r_exist ctx fail return
    | PForall (param, left1), _ ->
      let dom_exist = ref None in
      subst_poly param dom_exist left1 @@ fun left2 ->
      _subtype left2 right ctx return
    | _, PForall (param, right1) ->
      extend param ctx @@ fun ctx1 ->
      _subtype left right1 ctx1 return
    | PArrow (l_dom, l_codom), PArrow (r_dom, r_codom) ->
      _subtype r_dom l_dom ctx @@ fun () ->
      apply_poly ctx l_codom @@ fun l_codom1 ->
      apply_poly ctx r_codom @@ fun r_codom1 ->
      _subtype l_codom1 r_codom1 ctx return
    | _, _ -> _fail left right
  in
  _subtype left right ctx return

let rec synth expr ctx fail return =
  match expr with
  | EUnit -> return poly_unit
  | EVar name -> lookup name ctx fail return
  | EAbs (param, body) ->
    let dom = poly_var (ref None) in
    let codom = poly_var (ref None) in
    update param dom ctx @@ fun ctx1 ->
    check body codom ctx1 fail @@ fun () ->
    return (poly_arrow dom codom)
  | EApp (func, arg) ->
    synth func ctx fail @@ fun func_t ->
    apply_poly ctx func_t @@ fun func_t1 ->
    synth_apply func_t1 arg ctx fail return
  | EAnno (expr1, poly) ->
    valid_poly poly ctx fail @@ fun () ->
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
    let dom_exist = ref None in
    subst_poly param dom_exist poly1 @@ fun poly2 ->
    synth_apply poly2 expr ctx fail return
  | _ -> return poly
and check expr poly ctx fail return =
  match expr, poly with
  | EUnit, PUnit -> return ()
  | EAbs (param, body), PArrow (dom, codom) ->
    update param dom ctx @@ fun ctx1 ->
    check body codom ctx1 fail return
  | _, PForall (param, poly1) ->
    extend param ctx @@ fun ctx1 ->
    check expr poly1 ctx1 fail return
  | _, _ ->
    synth expr ctx fail @@ fun expr_t ->
    apply_poly ctx expr_t @@ fun expr_t1 ->
    apply_poly ctx poly @@ fun poly1 ->
    subtype expr_t1 poly1 ctx fail return
