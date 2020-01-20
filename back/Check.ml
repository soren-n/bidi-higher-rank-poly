open Printf
open Syntax
open Context
open Print

let rec norm_poly poly return =
  match poly with
  | PBot -> return poly_bot
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
  | MBot -> return mono_bot
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
  | PBot ->
    l_exist := Some MBot;
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
  | PBot ->
    r_exist := Some MBot;
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
    | PBot | PUnit | PParam _ -> return ()
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
    | MBot | MUnit | MParam _ -> return ()
  in
  _visit r_mono return

let rec mono_poly mono return =
  match mono with
  | MBot -> return poly_bot
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
    | PBot, PBot -> return ()
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
  | EBot -> return poly_bot
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
