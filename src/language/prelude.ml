let flip f a b = f b a

let curry f x y = f (x, y)
let uncurry f (x, y) = f x y

let (<<) f g x = f (g x)
let (>>) g f x = f (g x)

let initLast xs =
  let rec func xs = function
    | []      -> failwith "initLast: expected non-empty list"
    | [y]     -> (xs, y)
    | y :: ys -> func (y :: xs) ys in
  let (ys, y) = func [] xs in (List.rev ys, y)

  let getDigit x = Char.chr (Z.to_int x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let ten = Z.of_int 10

let rec showSubscript x =
  if Z.lt x Z.zero then failwith "showSubscript: expected positive integer"
  else if Z.equal x Z.zero then "" else let (y, d) = Z.div_rem x ten in
    showSubscript y ^ getDigit d
