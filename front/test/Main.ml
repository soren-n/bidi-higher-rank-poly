open Util
open Back
open Front
open Shared
open Expr

let print layout =
  Typeset.compile layout @@ fun doc ->
  Typeset.render doc 2 80 @@ fun msg ->
  print_endline msg

let (<:) left right =
  Check.subtype left right Native.tenv
    (fun msg -> print msg; false)
    (fun () -> true)

let (==>) expr return =
  Check.synth_expr expr Native.tenv
    (fun msg -> print msg; assert false)
    return

let (<==) expr poly =
  Check.check_expr expr poly Native.tenv
    (fun msg -> print msg; false)
    (fun () -> true)

let interp expr return =
  Interp.eval_expr expr Native.venv @@ fun value ->
  Value.value_2_expr value return

(* Define tests *)
let interp_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:64
    ~name:"interp_sound"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      Poly.simple_mono_2_simple_poly simple_mono @@ fun expr_t ->
      try
        interp expr @@ fun expr1 ->
        if not (expr1 <== expr_t) then
          let ctx = Naming.make_ctx () in
          Print.print_expr ctx expr print_endline;
          print_endline "-----------------------------------";
          Print.print_expr ctx expr1 print_endline;
          print_endline "-----------------------------------";
          Print.print_poly ctx expr_t print_endline;
          print_endline "***********************************";
          false
        else true
      with Assert_failure (msg, line, index) ->
        let open Printf in
        print_endline (sprintf "%s: line %d, index %d" msg line index);
        let ctx = Naming.make_ctx () in
        Print.print_expr ctx expr print_endline;
        print_endline "-----------------------------------";
        Print.print_poly ctx expr_t print_endline;
        print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        false
      )

(* Run tests *)
let _ =
  QCheck_runner.run_tests
  [ interp_sound
  ];
