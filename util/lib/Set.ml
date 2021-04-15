open Extra

type 'a set = 'a AVL.tree

let make = AVL.make_null
let is_empty set = (AVL.get_count set) = 0
let is_member = AVL.is_member
let get_member = AVL.get_member
let size = AVL.get_count
let add = AVL.insert
let remove = AVL.remove
let to_list = AVL.to_list
let from_list = AVL.from_list

let fold empty_case item_case set =
  List.fold empty_case item_case (to_list set)

let union order xs ys =
  let open AVL in
  let open Order in
  let _cont k x xs = k (x :: xs) in
  let rec _visit xs ys return =
    match xs, ys with
    | [], _ -> return ys
    | _, [] -> return xs
    | x :: xs', y :: ys' ->
      match order x y with
      | EQ -> _visit xs' ys' (_cont return x)
      | LT -> _visit xs' ys (_cont return x)
      | GT -> _visit xs ys' (_cont return y)
  in
  from_list (_visit (to_list xs) (to_list ys) identity)

let difference order xs ys =
  let open AVL in
  let open Order in
  let _cont k x xs = k (x :: xs) in
  let rec _visit xs ys return =
    match xs, ys with
    | [], _ | _, [] -> return xs
    | x :: xs', y :: ys' ->
      match order x y with
      | EQ -> _visit xs' ys' return
      | LT -> _visit xs' ys (_cont return x)
      | GT -> _visit xs' ys' (_cont return x)
  in
  from_list (_visit (to_list xs) (to_list ys) identity)

let intersection order xs ys =
  let open AVL in
  let open Order in
  let _cont k x xs = k (x :: xs) in
  let rec _visit xs ys return =
    match xs, ys with
    | [], _ | _, [] -> return []
    | x :: xs', y :: ys' ->
      match order x y with
      | EQ -> _visit xs' ys' (_cont return x)
      | LT -> _visit xs' ys return
      | GT -> _visit xs ys' return
  in
  from_list (_visit (to_list xs) (to_list ys) identity)

let first values = AVL.get_leftmost values
let first_unsafe values =
  match AVL.get_leftmost values with
  | None -> assert false
  | Some value -> value

let last values = AVL.get_rightmost values
let last_unsafe values =
  match AVL.get_rightmost values with
  | None -> assert false
  | Some value -> value
