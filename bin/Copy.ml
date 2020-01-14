open Util
open Syntax

let rec _copy_mono mono env return =
  match mono with
  | MUnit -> return mono_unit env
  | MParam name -> return (mono_param name) env
  | MVar from_exist ->
    Env.lookup exist_equal from_exist env
      (fun () ->
        let to_exist = ref None in
        Env.bind from_exist to_exist env @@ fun env1 ->
        match !from_exist with
        | None -> return (mono_var to_exist) env1
        | Some mono1 ->
          _copy_mono mono1 env1 @@ fun mono2 env2 ->
          to_exist := Some mono2;
          return (mono_var to_exist) env2)
      (fun to_exist ->
        return (mono_var to_exist) env)
  | MArrow (dom, codom) ->
    _copy_mono dom env @@ fun dom1 env1 ->
    _copy_mono codom env1 @@ fun codom1 env2 ->
    return (mono_arrow dom1 codom1) env2

let copy_mono mono return =
  _copy_mono mono Env.empty @@ fun result _env1 ->
  return result

let rec _copy_poly poly env return =
  match poly with
  | PUnit -> return poly_unit env
  | PParam name -> return (poly_param name) env
  | PVar from_exist ->
    Env.lookup exist_equal from_exist env
      (fun () ->
        let to_exist = ref None in
        Env.bind from_exist to_exist env @@ fun env1 ->
        match !from_exist with
        | None -> return (poly_var to_exist) env1
        | Some mono1 ->
          _copy_mono mono1 env1 @@ fun mono2 env2 ->
          to_exist := Some mono2;
          return (poly_var to_exist) env2)
      (fun to_exist ->
        return (poly_var to_exist) env)
  | PArrow (dom, codom) ->
    _copy_poly dom env @@ fun dom1 env1 ->
    _copy_poly codom env1 @@ fun codom1 env2 ->
    return (poly_arrow dom1 codom1) env2
  | PForall (param, poly1) ->
    _copy_poly poly1 env @@ fun poly2 env1 ->
    return (poly_forall param poly2) env1
  | PMono mono ->
    _copy_mono mono env @@ fun mono1 env1 ->
    return (poly_mono mono1) env1

let copy_poly poly return =
  _copy_poly poly Env.empty @@ fun result _env1 ->
  return result
