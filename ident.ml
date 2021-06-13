type name =
  | No
  | Name of string * int

let showName : name -> string = function
  | No          -> "_"
  | Name (p, n) -> if !Prefs.trace then p ^ "#" ^ string_of_int n else p

module Name = struct
  type t = name
  let compare x y =
    match (x, y) with
    | No, No -> 0
    | No, Name _ -> -1
    | Name _, No -> 1
    | Name (p, a), Name (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Name)
module Files = Set.Make(String)