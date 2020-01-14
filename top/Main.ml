open Printf
open Bin
open Util
open Extra

let report header msg =
  printf "%s%s\n" header msg

let error msg =
  report "Error: " msg

let parse parser tokens =
  try
    let result = parser Lexer.token tokens in
    Result.make_value result
  with
  | Lexer.Error msg ->
    Result.make_error
      (sprintf "Lexer error: %s" msg)
  | Parser.Error ->
    Result.make_error
      "Parser error"

let parse_file path =
  let file_in = open_in path in
  let tokens = Lexing.from_channel file_in in
  let result = parse Parser.file tokens in
  close_in file_in;
  result

let parse_input input =
  parse Parser.input (Lexing.from_string input)

let options = []

let files = ref []
let anonymous path =
  files := path :: !files

let usage =
  "Usage: BHRP [file] ..."

let interp expr ctx =
  Check.synth expr ctx error @@ fun result_t ->
  Interp.eval expr Native.venv @@ fun result_v ->
  Interp.print_value result_v @@ fun result_v_s ->
  Print.print_poly result_t @@ fun result_t_s ->
  report "" (sprintf "%s : %s" result_v_s result_t_s)

let interp_input input ctx =
  match parse_input input with
  | Result.Error msg -> error msg
  | Result.Value expr -> interp expr ctx

let interp_file path ctx =
  match parse_file path with
  | Result.Error msg -> error msg
  | Result.Value expr -> interp expr ctx

let rec interp_files paths ctx =
  match paths with
  | [] -> ()
  | path :: paths1 ->
    interp_file path ctx;
    interp_files paths1 ctx

let read_input () =
  let _complete input =
    let length = String.length input in
    if length < 2 then false else
    if input.[length - 1] <> ';' then false else
    if input.[length - 2] <> ';' then false else
    true
  in
  let prompt = "> " in
  let prompt_more = "  " in
  print_string prompt;
  let input = ref (read_line ()) in
  while not (_complete !input) do
    print_string prompt_more;
    input := !input ^ (read_line ())
  done;
  let result = !input in
  String.sub result 0 (String.length result - 2)

let report_context ctx =
  Context.get_venv ctx @@ fun venv ->
  Env.fold
    (fun return -> return "")
    (fun name poly visit_env return ->
      Print.print_poly poly @@ fun poly_s ->
      visit_env @@ fun binds ->
      return (sprintf "%s : %s\n%s" name poly_s binds))
    venv (report "Context:\n")

let repl ctx =
  while true do
    let input = read_input () in
    if input = "exit" then exit 0 else
    if input = "context" then report_context ctx else
    interp_input input ctx
  done

let () =
  Sys.catch_break true;
  Arg.parse options anonymous usage;
  let _files = !files in
  if (List.length _files) <> 0
  then interp_files !files Native.ctx
  else repl Native.ctx
