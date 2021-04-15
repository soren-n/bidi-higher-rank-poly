let make_none () = None
let make_some x = Some x

let is_none x =
  match x with
  | Some _ -> false
  | None -> true

let is_some x =
  match x with
  | Some _ -> true
  | None -> false

let map f x =
  match x with
  | Some x' -> Some (f x')
  | _ -> None

let map2 f x y =
  match x, y with
  | Some x', Some y' -> Some (f x' y')
  | _, _ -> None

let case none_case some_case x =
  match x with
  | None -> none_case
  | Some y -> some_case y
