open Extra

type 'a set = 'a list

let empty = []

let add item set return =
  return (item :: set)

let member equal item set fail return =
  let rec _visit set =
    match set with
    | [] -> fail ()
    | item1 :: set1 ->
      if equal item item1
      then return ()
      else _visit set1
  in
  _visit set

let print print_item set return =
  let open Printf in
  let _cont k x xs = k (x :: xs) in
  let rec _visit set return =
    match set with
    | [] -> return []
    | item :: items1 ->
      print_item item @@ fun item1 ->
      _visit items1 (_cont return item1)
  in
  _visit set @@ fun items ->
  return (sprintf "{%s}" (String.join_with "; " items))
