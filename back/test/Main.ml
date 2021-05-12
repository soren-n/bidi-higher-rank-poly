open Util
open Back
open Front
open Shared
open Poly
open Expr
open Simple

let parse input return =
  return (Parser.input Lexer.token (Lexing.from_string input))

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

let purely_universally_quantified poly =
  let open Syntax in
  let rec _visit_poly poly =
    match poly with
    | PNothing -> true
    | PUnit -> true
    | PBit _size -> true
    | PParam _label -> true
    | PVar _exist -> false
    | PArrow (dom, codom) ->
      _visit_poly dom && _visit_poly codom
    | PForall (_label, poly1) ->
      _visit_poly poly1
    | PMono mono ->
      _visit_mono mono
  and _visit_mono mono =
    match mono with
    | MNothing -> true
    | MUnit -> true
    | MBit _size -> true
    | MParam _label -> true
    | MVar _exist -> false
    | MArrow (dom, codom) ->
      _visit_mono dom && _visit_mono codom
  in
  _visit_poly poly

(* Define tests *)
let print_parse_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:32
    ~name:"print_parse_sound"
    (arbitrary_typed_stmt ctx)
    (fun (stmt, _simple_mono) ->
      Print.print_stmt ctx stmt @@ fun stmt_s ->
      parse stmt_s @@ fun stmt1 ->
      Syntax.stmt_equal stmt stmt1)

let subtype_sound =
  QCheck.Test.make ~count:64
    ~name:"subtype_sound"
    arbitrary_simple
    (fun simple ->
      Mono.simple_2_simple_mono simple @@ fun simple_mono ->
      Poly.simple_mono_2_simple_poly simple_mono @@ fun simple_poly_exist ->
      Poly.simple_2_simple_poly simple @@ fun simple_poly ->
      if not (simple_poly_exist <: simple_poly) then
        let ctx = Naming.make_ctx () in
        Print.print_poly ctx simple_poly print_endline;
        print_endline "-----------------------------------";
        Print.print_poly ctx simple_poly_exist print_endline;
        print_endline "***********************************";
        false
      else true)

let synth_expr_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:128
    ~name:"synth_expr_sound"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      Poly.simple_mono_2_simple_poly simple_mono @@ fun expr_t ->
      if not (expr <== expr_t) then
        let ctx = Naming.make_ctx () in
        Print.print_expr ctx expr print_endline;
        print_endline "-----------------------------------";
        Print.print_poly ctx expr_t print_endline;
        print_endline "***********************************";
        false
      else true)

let synth_type_sound_l =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:64
    ~name:"synth_type_sound_l"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      Poly.simple_mono_2_simple_poly simple_mono @@ fun left ->
      expr ==> fun right ->
      left <: right)

let synth_type_sound_r =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:64
    ~name:"synth_type_sound_r"
    (arbitrary_typed_expr ctx)
    (fun (expr, simple_mono) ->
      Poly.simple_mono_2_simple_poly simple_mono @@ fun right ->
      expr ==> fun left ->
      left <: right)

let check_type_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:64
    ~name:"check_type_sound"
    (arbitrary_typed_expr ctx)
    (fun (expr, _simple_mono) ->
      expr ==> fun expr_t ->
      expr <== expr_t)

let generalize_sound =
  let ctx = Naming.make_ctx () in
  QCheck.Test.make ~count:64
    ~name:"generalize_sound"
    (arbitrary_poly ctx)
    (fun poly ->
      Check.generalize poly @@ fun poly1 ->
      purely_universally_quantified poly1)

(* Run tests *)
let _ =
  QCheck_runner.run_tests
  [ print_parse_sound
  (* ; subtype_sound *)
  ; synth_expr_sound
  (* ; synth_type_sound_l
  ; synth_type_sound_r
  ; check_type_sound
  ; generalize_sound *)
  ];
