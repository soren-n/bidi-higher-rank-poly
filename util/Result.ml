type ('error, 'value) result =
  | Error of 'error
  | Value of 'value

let make_error msg = Error msg
let make_value value = Value value
