open Printf
open Util
open Syntax

type ctx =
  { venv : (label, poly) Env.env
  ; tenv : label Set.set
  }

let empty =
  { venv = Env.empty
  ; tenv = Set.empty
  }

let make venv tenv =
  { venv = venv
  ; tenv = tenv
  }

let get_venv ctx return = return ctx.venv
let get_tenv ctx return = return ctx.tenv

let update label poly ctx return =
  Env.update label poly ctx.venv @@ fun venv1 ->
  return { ctx with venv = venv1 }

let extend label ctx return =
  Set.add label ctx.tenv @@ fun tenv1 ->
  return { ctx with tenv = tenv1 }

let lookup name ctx fail return =
  let _equal l r = l = r in
  Env.lookup _equal name ctx.venv
    (fun () -> fail (sprintf "Unknown parameter \"%s\"" name))
    return

let bound name ctx fail return =
  let _equal l r = l = r in
  Set.member _equal name ctx.tenv
    (fun () -> fail (sprintf "Unknown type parameter \"%s\"" name))
    return

let print ctx return =
  let _id x k = k x in
  Env.print _id Print.print_poly ctx.venv @@ fun venv1 ->
  Set.print _id ctx.tenv @@ fun tenv1 ->
  return (sprintf "%s\n%s" venv1 tenv1)
