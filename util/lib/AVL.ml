open Infix
open Order
open Extra

type 'a tree =
  | Null
  | Node of int * int * 'a * 'a tree * 'a tree

let make_null () = Null

let make_node count height data left right =
  Node (count, height, data, left, right)

let fold null_case node_case tree =
  let rec _visit tree return =
    match tree with
    | Null -> return null_case
    | Node (count, height, data, left, right) ->
      _visit left (fun left' ->
      _visit right (fun right' ->
      return (node_case count height data left' right')))
  in
  _visit tree identity

let map f tree =
  fold Null
    (fun c h x l r ->
      make_node c h (f x) l r)
    tree

let get_count tree =
  match tree with
  | Null -> 0
  | Node (count, _, _, _, _) -> count

let get_height tree =
  match tree with
  | Null -> 0
  | Node (_, height, _, _, _) -> height

let local_inbalance pos tree =
  match tree with
  | Null -> EQ
  | Node (_, _, _, l, r) ->
    let h_l = get_height l in
    let h_r = get_height r in
    let h_diff = h_l - h_r in
    match pos with
    | EQ ->
      if h_diff > 1 then LT else
      if h_diff < -1 then GT else
      EQ
    | LT ->
      if h_diff > 1 then LT else
      if h_diff < 0 then GT else
      EQ
    | GT ->
      if h_diff > 0 then LT else
      if h_diff < -1 then GT else
      EQ

let local_rebalance pos tree =
  let _rotate_left p =
    match p with
    | Null -> assert false
    | Node (c_p, _, u, a, q) ->
      let c_a = get_count a in
      let h_a = get_height a in
      match q with
      | Null -> assert false
      | Node (_, _, v, b, c) ->
        let c_b = get_count b in
        let h_b = get_height b in
        let c_l = c_a + c_b + 1 in
        let h_l = (max h_a h_b) + 1 in
        let h_r = get_height c in
        Node (c_p, (max h_l h_r) + 1, v, Node (c_l, h_l, u, a, b), c)
  in
  let _rotate_right q =
    match q with
    | Null -> assert false
    | Node (c_q, _, v, p, c) ->
      let c_c = get_count c in
      let h_c = get_height c in
      match p with
      | Null -> assert false
      | Node (_, _, u, a, b) ->
        let c_b = get_count b in
        let h_b = get_height b in
        let c_r = c_b + c_c + 1 in
        let h_l = get_height a in
        let h_r = (max h_b h_c) + 1 in
        Node (c_q, (max h_l h_r) + 1, u, a, Node (c_r, h_r, v, b, c))
  in
  match local_inbalance pos tree with
  | EQ -> tree
  | LT -> _rotate_right tree
  | GT -> _rotate_left tree

let insert_cont order data tree return =
  let rec _visit tree pos updated inserted =
    match tree with
    | Null -> inserted (make_node 1 1 data Null Null)
    | Node (count, height, data', left, right) ->
      match order data data' with
      | EQ -> updated (make_node count height data left right)
      | LT ->
        _visit left LT
          (updated <== (swap (make_node count height data') right))
          (inserted <== (local_rebalance pos) <== (fun left' ->
            let height' = max ((get_height left') + 1) height in
            make_node (count + 1) height' data' left' right))
      | GT ->
        _visit right GT
          (updated <== (make_node count height data' left))
          (inserted <== (local_rebalance pos) <== (fun right' ->
            let height' = max ((get_height right') + 1) height in
            make_node (count + 1) height' data' left right'))
  in
  _visit tree EQ return (return <== (local_rebalance EQ))

let insert order data tree =
  insert_cont order data tree identity

let remove_cont order data tree return =
  let rec _leftmost tree =
    match tree with
    | Null -> assert false
    | Node (_, _, data, Null, _) -> data
    | Node (_, _, _, left, _) -> _leftmost left
  in
  let rec _rightmost tree =
    match tree with
    | Null -> assert false
    | Node (_, _, data, _, Null) -> data
    | Node (_, _, _, _, right) -> _rightmost right
  in
  let rec _visit tree pos data return =
    match tree with
    | Null -> tree
    | Node (count, height, data', left, right) ->
      begin match order data data' with
      | EQ ->
        begin match left, right with
        | Null, Null -> return (make_null ())
        | Null, _ ->
          let data' = _leftmost right in
          _visit right GT data'
            (return <== (local_rebalance pos) <== (fun right' ->
              let height' = max ((get_height right') + 1) height in
              make_node (count - 1) height' data' left right'))
        | _, Null ->
          let data' = _rightmost left in
          _visit left LT data'
            (return <== (local_rebalance pos) <== (fun left' ->
              let height' = max ((get_height left') + 1) height in
              make_node (count - 1) height' data' left' right))
        | _, _ ->
          let left_count = get_count left in
          let right_count = get_count right in
          begin match int_compare left_count right_count with
          | LT ->
            let data' = _leftmost right in
            _visit right GT data'
              (return <== (local_rebalance pos) <== (fun right' ->
                let height' = max ((get_height right') + 1) height in
                make_node (count - 1) height' data' left right'))
          | GT | EQ ->
            let data' = _rightmost left in
            _visit left LT data'
              (return <== (local_rebalance pos) <== (fun left' ->
                let height' = max ((get_height left') + 1) height in
                make_node (count - 1) height' data' left' right))
          end
        end
      | LT ->
        _visit left LT data
          (return <== (local_rebalance pos) <== (fun left' ->
            let height' = max ((get_height left') + 1) height in
            make_node (count - 1) height' data' left' right))
      | GT ->
        _visit right GT data
          (return <== (local_rebalance pos) <== (fun right' ->
            let height' = max ((get_height right') + 1) height in
            make_node (count - 1) height' data' left right'))
      end
  in
  _visit tree EQ data (return <== (local_rebalance EQ))

let remove order data tree =
  remove_cont order data tree identity

let is_member order item tree =
  let rec _visit tree =
    match tree with
    | Null -> false
    | Node (_, _, data, left, right) ->
      match order item data with
      | EQ -> true
      | LT -> _visit left
      | GT -> _visit right
  in
  _visit tree

let rec get_member index tree =
  match tree with
  | Null -> None
  | Node (_, _, data, left, right) ->
    if index = 0 then Some data else
    let left_count = get_count left in
    if left_count <= index
    then get_member (index - left_count) right
    else get_member index left

let rec get_leftmost tree =
  match tree with
  | Null -> None
  | Node (_, _, data, left, _) ->
    if left = Null then Some data else
    get_leftmost left

let rec get_rightmost tree =
  match tree with
  | Null -> None
  | Node (_, _, data, _, right) ->
    if right = Null then Some data else
    get_rightmost right

let to_list tree =
  fold
    (fun result -> result)
    (fun _ _ data visit_left visit_right result ->
      visit_left (data :: (visit_right result)))
    tree []

let from_list items =
  let _pop items f =
    match items with
    | item :: items' -> f item items'
    | [] -> assert false
  in
  let rec _build pos count items return =
    match count with
    | 0 -> return items 0 (make_null ())
    | 1 ->
      _pop items (fun data items1 ->
      return items1 1 (make_node 1 1 data (make_null ()) (make_null ())))
    | _ ->
      let n = count - 1 in
      let m = n / 2 in
      let _left () =
        let sm = m + 1 in
        _build LT sm items (fun items1 l_h left ->
        _pop items1 (fun data items2 ->
        _build GT m items2 (fun items3 r_h right ->
        let height = (max l_h r_h) + 1 in
        return items3 height (make_node count height data left right))))
      in
      let _right () =
        let sm = m + 1 in
        _build LT m items (fun items1 l_h left ->
        _pop items1 (fun data items2 ->
        _build GT sm items2 (fun items3 r_h right ->
        let height = (max l_h r_h) + 1 in
        return items3 height (make_node count height data left right))))
      in
      begin match pos, n mod 2 with
      | _, 0 ->
        _build LT m items (fun items1 l_h left ->
        _pop items1 (fun data items2 ->
        _build GT m items2 (fun items3 r_h right ->
        let height = (max l_h r_h) + 1 in
        return items3 height (make_node count height data left right))))
      | EQ, _ | LT, _ -> _left ()
      | GT, _ -> _right ()
      end
  in
  let count = List.length items in
  _build EQ count items (fun _ _ x -> x)
