type total =
  | EQ
  | LT
  | GT

let total_order left right =
  if left = right then EQ else
  if left < right then LT else
  GT

let int_compare a b =
  if a = b then EQ else
  if a < b then LT else
  GT
