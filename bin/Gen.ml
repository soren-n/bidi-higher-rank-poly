open Printf
open Util.Extra

type gen = int ref
let make_gen () = ref 0
let sample_gen gen =
  let result = !gen in
  gen := result + 1;
  result

let digits =
  [|"\u{2080}"; "\u{2081}"; "\u{2082}"; "\u{2083}"; "\u{2084}"
  ; "\u{2085}"; "\u{2086}"; "\u{2087}"; "\u{2088}"; "\u{2089}"|]

let subscript n =
  String.fold ""
    (fun c ->
      sprintf "%s%s" digits.((int_of_char c) - 48))
    (string_of_int (abs n))

let alphabet =
  [| 'a'; 'b'; 'c'; 'd'; 'e'; 'f'; 'g'
  ; 'h'; 'i'; 'j'; 'k'; 'l'; 'm'; 'n'
  ; 'o'; 'p'; 'q'; 'r'; 's'; 't'; 'u'
  ; 'v'; 'w'; 'x'; 'y'; 'z' |]

let name n suffix =
  String.fold ""
    (fun c ->
      sprintf "%c%s%s" alphabet.((int_of_char c) - 48) suffix)
    (string_of_int (abs n))

type var =
  { c : string
  ; i : gen
  }

let make_param gen =
  { c = name (sample_gen gen) ""
  ; i = make_gen ()
  }

let make_exist gen =
  let hat = "\u{0302}" in
  { c = name (sample_gen gen) hat
  ; i = make_gen ()
  }

let sample_var var =
  String.conc var.c (subscript (sample_gen var.i))
