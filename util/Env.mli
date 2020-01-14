type ('key, 'value) env

val empty : ('key, 'value) env

val from_list : ('key * 'value) list -> ('key, 'value) env

val fold : 'a -> ('key -> 'value -> 'a -> 'a) -> ('key, 'value) env -> 'a

val bind :
  'key -> 'value ->
  ('key, 'value) env ->
  (('key, 'value) env -> 'result) ->
  'result

val lookup :
  ('key -> 'key -> bool) ->
  'key -> ('key, 'value) env ->
  (unit -> 'result) ->
  ('value -> 'result) ->
  'result

val bound :
  ('key -> 'key -> bool) ->
  'key -> ('key, 'value) env ->
  (unit -> 'result) ->
  (unit -> 'result) ->
  'result

val print :
  ('key -> (string -> 'a) -> 'a) ->
  ('value -> (string -> 'a) -> 'a) ->
  ('key, 'value) env ->
  (string -> 'a) -> 'a
