let (<==) f g x = f (g x)
let (==>) f g x = g (f x)

let (<<=) f g x y = f (g x y)
let (=>>) f g x y = g (f x y)

let (<?=) f g x = Option.map f (g x)
let (=?>) f g x = Option.map g (f x)

let (<!=) f g x = Result.map f (g x)
let (=!>) f g x = Result.map g (f x)
