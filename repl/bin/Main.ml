open Back
open Util
open Front
open Extra
open Typeset

let print layout =
  Typeset.compile layout @@ fun doc ->
  Typeset.render doc 2 80 @@ fun msg ->
  print_endline msg

let error msg =
  print (~$"🔥 Error:" <+> msg </> null)

let success value poly =
  let ctx = Naming.make_ctx () in
  Check.generalize poly @@ fun poly1 ->
  Value.print_value value @@ fun value1 ->
  Print.layout_poly ctx poly1 @@ fun poly2 ->
  print (~$value1 <+> ~$":" <+> poly2 </> null)

let report_context tctx =
  let ctx = Naming.make_ctx () in
  Context.get_venv tctx @@ fun venv ->
  Env.fold
    (fun return -> return ~$"")
    (fun name poly visit_env return ->
      Print.layout_poly ctx poly @@ fun poly1 ->
      visit_env @@ fun binds ->
      return (~$name <+> ~$":" <+> poly1 </> binds))
    venv print

let parse parser tokens =
  try
    let result = parser Lexer.token tokens in
    Result.make_value result
  with
  | Lexer.Error msg ->
    Result.make_error (~$"Lexing error:" <+> ~$msg)
  | Parser.Error ->
    Result.make_error ~$"Parsing error"

let parse_file path =
  try
    let file_in = open_in path in
    let tokens = Lexing.from_channel file_in in
    let result = parse Parser.file tokens in
    close_in file_in;
    result
  with Sys_error msg ->
    Result.make_error ~$msg

let parse_input input =
  parse Parser.input (Lexing.from_string input)

let options = []

let files = ref []
let anonymous path =
  files := path :: !files

let interp_input tctx env input =
  match parse_input input with
  | Result.Error msg -> error msg
  | Result.Value stmt ->
    Valid.check_stmt stmt tctx error @@ fun () ->
    Check.synth_stmt stmt tctx error @@ fun result_t ->
    Interp.eval_stmt stmt env @@ fun result_v ->
    success result_v result_t

let interp_file tctx env path =
  match parse_file path with
  | Result.Error msg -> error msg; exit 1
  | Result.Value prog ->
    Valid.check_prog prog tctx error @@ fun () ->
    Check.check_prog prog tctx error @@ fun tctx1 ->
    Interp.eval_prog prog env @@ fun () ->
    report_context tctx1

let interp_files tctx env paths =
  List.iter (interp_file tctx env) paths;
  exit 0

let read_input () =
  let _complete input =
    let length = String.length input in
    if length < 2 then false else
    if input.[length - 1] <> ';' then false else
    if input.[length - 2] <> ';' then false else
    true
  in
  let prompt = "▶  " in
  let prompt_more = "⋮  " in
  print_string prompt;
  let input = ref (read_line ()) in
  while not (_complete !input) do
    print_string prompt_more;
    input := !input ^ (read_line ())
  done;
  let result = !input in
  String.sub result 0 (String.length result - 2)

let repl tctx env =
  while true do
    let input = read_input () in
    if input = "exit" then exit 0 else
    if input = "context" then report_context tctx else
    interp_input tctx env input
  done

let usage =
  "Usage: BHRP [file] ..."

let () =
  Sys.catch_break true;
  Arg.parse options anonymous usage;
  let _files = !files in
  if (List.length _files) <> 0
  then interp_files Native.tenv Native.venv !files
  else repl Native.tenv Native.venv
