open Printf
open Util
open Syntax

type ctx =
  { venv : (label, poly) Env.env
  ; tenv : (label, poly) Env.env
  }

let empty =
  { venv = Env.empty
  ; tenv = Env.empty
  }

let make venv tenv =
  { venv = venv
  ; tenv = tenv
  }

let get_venv ctx return = return ctx.venv
let get_tenv ctx return = return ctx.tenv

let bind_v label poly ctx return =
  Env.bind label poly ctx.venv @@ fun venv1 ->
  return { ctx with venv = venv1 }

let bind_t label poly ctx return =
  Env.bind label poly ctx.tenv @@ fun tenv1 ->
  return { ctx with tenv = tenv1 }

let lookup_v label ctx fail return =
  Env.lookup label_equal label ctx.venv
    (fun () -> fail (sprintf "Unknown program parameter \"%s\"" label))
    return

let lookup_t label ctx fail return =
  Env.lookup label_equal label ctx.tenv
    (fun () -> fail (sprintf "Unknown type parameter \"%s\"" label))
    return

let bound_v label ctx fail return =
  Env.bound label_equal label ctx.venv
    (fun () -> fail (sprintf "Unknown program parameter \"%s\"" label))
    return

let bound_t label ctx fail return =
  Env.bound label_equal label ctx.tenv
    (fun () -> fail (sprintf "Unknown type parameter \"%s\"" label))
    return

let print gen ctx return =
  let _id x k = k x in
  Env.print _id (Print.print_poly gen) ctx.venv @@ fun venv1 ->
  Env.print _id (Print.print_poly gen) ctx.tenv @@ fun tenv1 ->
  return (sprintf "%s\n%s" venv1 tenv1)
