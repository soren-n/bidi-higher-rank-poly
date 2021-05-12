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

  let iter f term =
    fold () (fun item () -> f item) term

  let init count item =
    if count <= 0 then [] else
    let rec _visit index result =
      if index = count then result else
      _visit (index + 1) (item :: result)
    in
    _visit 0 []

  let map f term =
    fold [] (compose cons f) term

  let conc xs ys =
    fold ys cons xs

  let flatten xs =
    fold [] conc xs

  let rec zip xs ys =
    match xs, ys with
    | [], _ -> []
    | _, [] -> []
    | x :: xs1, y :: ys1 ->
      (x, y) :: (zip xs1 ys1)

  let print print_x xs =
    let open Printf in
    let join_with sep terms =
      let _conc a b = a ^ b in
      let _sep = _conc sep in
      fold
        (fun _sep return -> return "")
        (fun term visit_terms sep return ->
          visit_terms _sep @@ fun terms1 ->
          return (sep (_conc term terms1)))
        terms identity identity
    in
    sprintf "[%s]"
      (join_with "; "
        (map print_x xs))
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

  let contain y xs =
    fold false
      (fun x result ->
        if result
        then result
        else x = y)
      xs

  let count y xs =
    fold 0
      (fun x result ->
        if x = y
        then result + 1
        else result)
      xs
end

let bytes_2_binary value =
  let last = Bytes.length value in
  let rec _visit_bytes index result =
    if index = last then result else
    let value1 = Char.code (Bytes.get value index) in
    let result1 = _visit_byte 0 value1 result in
    _visit_bytes (index + 1) result1
  and _visit_byte index value result =
    if index = 8 then result else
    let result1 = if (value mod 2) = 0 then "0" :: result else "1" :: result in
    _visit_byte (index + 1) (value / 2) result1
  in
  let result = _visit_bytes 0 [] in
  List.fold "" String.conc result

let binary_2_bytes binary =
  let last = (String.length binary) / 8 in
  let rec _visit_bytes index result =
    if index = last then result else
    let index1 = (index * 8) - 1 in
    let last1 = index1 + 8 in
    let byte = _visit_byte index1 last1 1 0 in
    Bytes.set result (last - (index + 1)) (Char.chr byte);
    _visit_bytes (index + 1) result
  and _visit_byte index last place result =
    if index = last then result else
    let result1 =
      if (String.get binary last) = '0'
      then result else place + result
    in
    _visit_byte index (last - 1) (place * 2) result1
  in
  let value = Bytes.create last in
  _visit_bytes 0 value
