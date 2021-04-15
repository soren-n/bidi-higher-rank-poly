let word_chars =
  "0123456789" ^
  "abcdefghijklmnopqrstuvwxyz" ^
  "ABCDEFGHIJKLMNOPQRSTUVWXYZ" ^
  "[]{}!\"'#$%*+-.,/\\:;<>=?@~^_`|"

let word_char_gen state =
  let index =
    Random.State.int state
      (String.length word_chars - 1)
  in
  String.get word_chars index

let gen_word =
  let open QCheck.Gen in
  small_nat >>= fun n ->
  string_size ~gen:word_char_gen (1--(n + 1))

let shrink_word word yield =
  let length = String.length word in
  if length <= 1 then () else
  let last = length - 1 in
  for i = 0 to last do
    let word' = Bytes.init last
      (fun j -> if j<i then word.[j] else word.[j+1])
    in
    yield (Bytes.unsafe_to_string word')
  done

let print_word = Printf.sprintf "\"%s\""

let arbitrary_word =
  QCheck.make gen_word
    ~print:print_word
    ~shrink:shrink_word
