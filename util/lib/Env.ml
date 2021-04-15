open Extra

type ('key, 'value) env =
  ('key * 'value) list

let empty = []

let from_list binds =
  List.fold empty
    (fun (key, value) env ->
      (key, value) :: env)
    binds

let fold empty_case bind_case env =
  let rec _visit env return =
    match env with
    | [] -> return empty_case
    | (key, value) :: env1 ->
      _visit env1 @@ fun result ->
      return (bind_case key value result)
  in
  _visit env identity

let bind key value env return =
  return ((key, value) :: env)

let lookup equal key env fail return =
  let rec _visit env =
    match env with
    | [] -> fail ()
    | (key1, value) :: env1 ->
      if equal key key1
      then return value
      else _visit env1
  in
  _visit env

let bound equal key env fail return =
  let rec _visit env =
    match env with
    | [] -> fail ()
    | (key1, _value) :: env1 ->
      if equal key key1
      then return ()
      else _visit env1
  in
  _visit env

let keys order env return =
  fold
    (fun return -> return (Set.make ()))
    (fun key _value visit_env return ->
      visit_env @@ fun keys ->
      return (Set.add order key keys))
    env return

let values env return =
  fold
    (fun return -> return [])
    (fun _key value visit_env return ->
      visit_env @@ fun values ->
      return (value :: values))
    env return

let print print_key print_value env return =
  let open Printf in
  let _cont k x y xys = k ((sprintf "%s = %s" x y) :: xys) in
  let rec _visit env return =
    match env with
    | [] -> return []
    | (key, value) :: env1 ->
      print_key key @@ fun key1 ->
      print_value value @@ fun value1 ->
      _visit env1 (_cont return key1 value1)
  in
  _visit env @@ fun binds ->
  return (String.join_with "\n" binds)
