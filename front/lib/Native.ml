open Util
open Back
open Syntax

let _and xs =
  match xs with
  | (EBit l_value) :: (EBit r_value) :: [] ->
    let value =
      Bytes.create (max
        (Bytes.length l_value)
        (Bytes.length r_value))
    in
    expr_bit value
  | _ -> assert false (* Invariant *)

let _or xs =
  match xs with
  | (EBit l_value) :: (EBit _r_value) :: [] -> expr_bit l_value
  | _ -> assert false (* Invariant *)

let _xor xs =
  match xs with
  | (EBit l_value) :: (EBit _r_value) :: [] -> expr_bit l_value
  | _ -> assert false (* Invariant *)

let _neg xs =
  match xs with
  | (EBit value) :: [] -> expr_bit value
  | _ -> assert false (* Invariant *)

let venv =
  Env.from_list
  [ "and", expr_proc "and" 2 _and
  ; "or", expr_proc "or" 2 _or
  ; "xor", expr_proc "xor" 2 _xor
  ; "neg", expr_proc "neg" 2 _neg
  ]

let tenv =
  let _unit = poly_unit in
  let _bit8 = poly_bit Bit8 in
  let ($->) l r = poly_arrow l r in
  Context.make
    (Env.from_list
    [ "main", _unit $-> _unit
    ; "and", _bit8 $-> (_bit8 $-> _bit8)
    ; "or", _bit8 $-> (_bit8 $-> _bit8)
    ; "xor", _bit8 $-> (_bit8 $-> _bit8)
    ; "neg", _bit8 $-> _bit8
    ])
    Env.empty
