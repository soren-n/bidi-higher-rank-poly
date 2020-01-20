open Printf
open Util.Extra

type gen = int ref
let make_gen () = ref 0
let sample gen =
  let result = !gen in
  gen := result + 1;
  abs result

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

type ctx =
  { label : gen
  ; exist : gen
  }

let make_ctx () =
  { label = make_gen ()
  ; exist = make_gen ()
  }

let sample_label ctx return =
  let _n = sample ctx.label in
  let a = _n mod 26 in
  let i = _n / 26 in
  return (sprintf "%c%s" alphabet.(a) (subscript i))

let sample_exist ctx return =
  let n = sample ctx.exist in
  let a = n mod 26 in
  let i = n / 26 in
  return (sprintf "%c\u{0302}%s" alphabet.(a) (subscript i))
