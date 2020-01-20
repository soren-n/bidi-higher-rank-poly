type 'a set
val empty : 'a set
val add : 'a -> 'a set -> ('a set -> 'b) -> 'b

val fold : 'r -> ('a -> 'r -> 'r) -> 'a set -> 'r

val member :
  ('a -> 'a -> bool) ->
  'a -> 'a set -> (unit -> 'b) -> (unit -> 'b) -> 'b

val print :
  ('a -> (string -> 'b) -> 'b) ->
  'a set -> (string -> 'b) -> 'b
