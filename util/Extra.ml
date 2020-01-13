let identity x = x
let app f x = f x
let swap f x y = f y x
let compose f g x = f (g x)
let pipe f g x = g (f x)
let tap f g x = begin f x; g x end

module List = struct
  let nil = []
  let cons x xs = x :: xs

  let length = List.length

  let fold null_case list_case term =
    let rec _visit xs return =
      match xs with
      | [] -> return null_case
      | x :: xs' ->
        _visit xs' (compose return (list_case x))
    in
    _visit term identity

  let fold_rev null_case list_case term =
    let rec _visit xs result =
      match xs with
      | [] -> result
      | x :: xs' ->
        _visit xs' (list_case x result)
    in
    _visit term null_case

  let map f term =
    fold [] (compose cons f) term

  let conc xs ys =
    fold ys cons xs

  let rec zip xs ys =
    match xs, ys with
    | [], _ -> []
    | _, [] -> []
    | x :: xs1, y :: ys1 ->
      (x, y) :: (zip xs1 ys1)
end

module String = struct
  let epsi = ""
  let conc a b = a ^ b

  let make = String.make
  let get = String.get
  let sub = String.sub
  let length = String.length

  let fold null_case char_case term =
    let length = String.length term in
    let rec _visit index return =
      if length <= index then return null_case else
      _visit (index + 1) (compose return (char_case (String.get term index)))
    in
    _visit 0 identity

  let join terms =
    List.fold "" conc terms

  let join_with sep terms =
    let _sep = conc sep in
    List.fold
      (fun _sep return -> return "")
      (fun term visit_terms sep return ->
        visit_terms _sep @@ fun terms1 ->
        return (sep (conc term terms1)))
      terms identity identity
end
