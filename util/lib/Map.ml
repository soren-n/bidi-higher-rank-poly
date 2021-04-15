open Extra

type ('key, 'value) map = (('key, 'value) data) AVL.tree
and ('key, 'value) data =
  | Peek of 'key
  | Bind of 'key * 'value

let make_peek key = Peek key
let make_bind key value = Bind (key, value)

let size = AVL.get_count

let get_key data =
  match data with
  | Peek key -> key
  | Bind (key, _) -> key

let get_value data fail return =
  match data with
  | Peek _ -> fail ()
  | Bind (_, value) -> return value

let get_value_unsafe data return =
  match data with
  | Peek _ -> assert false
  | Bind (_, value) -> return value

let make = AVL.make_null

let fold empty_case bind_case binds =
  List.fold empty_case
    (fun bind result ->
      match bind with
      | Peek _ -> assert false
      | Bind (key, value) ->
        bind_case key value result)
    (AVL.to_list binds)

let map f binds =
  (AVL.from_list
    (List.map
      (fun bind ->
        match bind with
        | Peek _ -> assert false
        | Bind (key, value) ->
          Bind (key, f value))
      (AVL.to_list binds)))

let contains key_order =
  let _bind_order a b = key_order a (get_key b) in
  AVL.is_member _bind_order

let insert_cont order key value binds return =
  let _data_order left right = order (get_key left) (get_key right) in
  AVL.insert_cont _data_order (make_bind key value) binds return

let insert order key value binds =
  insert_cont order key value binds identity

let remove_cont order key binds return =
  let _data_order left right = order (get_key left) (get_key right) in
  AVL.remove_cont _data_order (make_peek key) binds return

let remove order key binds =
  remove_cont order key binds identity

let lookup_cont order key binds fail return =
  let open AVL in
  let open Order in
  let rec _visit tree =
    match tree with
    | Null -> fail ()
    | Node (_, _, data, left, right) ->
      begin match order key (get_key data) with
      | EQ -> get_value data fail return
      | LT -> _visit left
      | GT -> _visit right
      end
  in
  _visit binds

let lookup order key binds =
  lookup_cont order key binds Option.make_none Option.make_some

let lookup_unsafe_cont order key binds return =
  let open AVL in
  let open Order in
  let rec _visit tree =
    match tree with
    | Null -> assert false
    | Node (_, _, data, left, right) ->
      match order key (get_key data) with
      | EQ -> get_value_unsafe data return
      | LT -> _visit left
      | GT -> _visit right
  in
  _visit binds

let lookup_unsafe order key binds =
  lookup_unsafe_cont order key binds identity

let entries binds =
  List.map
    (fun bind ->
      match bind with
      | Peek _ -> assert false
      | Bind (key, value) -> key, value)
    (AVL.to_list binds)

let keys binds =
  List.map
    (fun bind ->
      match bind with
      | Peek _ -> assert false
      | Bind (key, _) -> key)
    (AVL.to_list binds)

let values binds =
  List.map
    (fun bind ->
      match bind with
      | Peek _ -> assert false
      | Bind (_, value) -> value)
    (AVL.to_list binds)

let from_entries entries =
  AVL.from_list
    (List.map (fun (key, value) -> Bind (key, value))
    entries)
