let (<<) f g x = f (g x)
let (>>) g f x = f (g x)

let initLast xs =
  let rec func xs = function
    | []      -> failwith "initLast: expected non-empty list"
    | [y]     -> (xs, y)
    | y :: ys -> func (y :: xs) ys in
  let (ys, y) = func [] xs in (List.rev ys, y)
