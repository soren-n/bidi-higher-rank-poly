type ('error, 'value) result =
  | Error of 'error
  | Value of 'value

let make_error msg = Error msg
let make_value value = Value value

let map f result =
  match result with
  | Error error -> Error error
  | Value value -> Value (f value)
