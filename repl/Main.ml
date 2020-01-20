open Printf
open Back
open Util
open Front
open Extra

let report msg =
  if (String.length msg) > 0 then
  print_endline msg

let error msg =
  printf "🔥 Error: %s\n" msg

let success value poly =
  let ctx = Naming.make_ctx () in
  Check.generalize poly @@ fun poly1 ->
  Interp.print_value value @@ fun value_s ->
  Print.print_poly ctx poly1 @@ fun poly_s ->
  printf "%s : %s\n" value_s poly_s

let parse parser tokens =
  try
    let result = parser Lexer.token tokens in
    Result.make_value result
  with
  | Lexer.Error msg ->
    Result.make_error (sprintf "Lexing error: %s" msg)
  | Parser.Error ->
    Result.make_error "Parsing error"

let parse_file path =
  try
    let file_in = open_in path in
    let tokens = Lexing.from_channel file_in in
    let result = parse Parser.file tokens in
    close_in file_in;
    result
  with Sys_error msg ->
    Result.make_error msg

let parse_input input =
  parse Parser.input (Lexing.from_string input)

let options = []

let files = ref []
let anonymous path =
  files := path :: !files

let usage =
  "Usage: BHRP [file] ..."

let interp ctx env expr =
  Valid.check_expr expr ctx error @@ fun () ->
  Check.synth expr ctx error @@ fun result_t ->
  Interp.eval expr env @@ fun result_v ->
  success result_v result_t

let interp_input ctx env input =
  match parse_input input with
  | Result.Error msg -> error msg
  | Result.Value expr -> interp ctx env expr

let interp_file ctx env path =
  match parse_file path with
  | Result.Error msg -> error msg; exit 1
  | Result.Value expr -> interp ctx env expr

let interp_files ctx env paths =
  List.iter (interp_file ctx env) paths;
  exit 0

let read_input () =
  let _complete input =
    let length = String.length input in
    if length < 2 then false else
    if input.[length - 1] <> ';' then false else
    if input.[length - 2] <> ';' then false else
    true
  in
  let prompt = "▶ " in
  let prompt_more = "⋮ " in
  print_string prompt;
  let input = ref (read_line ()) in
  while not (_complete !input) do
    print_string prompt_more;
    input := !input ^ (read_line ())
  done;
  let result = !input in
  String.sub result 0 (String.length result - 2)

let report_context tctx =
  let ctx = Naming.make_ctx () in
  Context.get_venv tctx @@ fun venv ->
  Env.fold
    (fun return -> return "")
    (fun name poly visit_env return ->
      Print.print_poly ctx poly @@ fun poly_s ->
      visit_env @@ fun binds ->
      return (sprintf "%s : %s\n%s" name poly_s binds))
    venv report

let repl ctx env =
  while true do
    let input = read_input () in
    if input = "exit" then exit 0 else
    if input = "context" then report_context ctx else
    interp_input ctx env input
  done

let () =
  Sys.catch_break true;
  Arg.parse options anonymous usage;
  let _files = !files in
  if (List.length _files) <> 0
  then interp_files Native.tenv Native.venv !files
  else repl Native.tenv Native.venv
