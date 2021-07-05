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

module Env   = Map.Make(Name)
module Files = Set.Make(String)

let inc : int ref = ref 0
let gen () = inc := !inc + 1; !inc

let pat : name -> name = function
  | No -> No | Name (p, _) -> Name (p, gen ())

type dir = Zero | One

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

module Dir = struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

module Atom = struct
  type t = name * dir
  let compare (a, x) (b, y) =
    if a = b then Dir.compare x y else Name.compare a b
end

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

let zeroPrim     = ref "0"
let onePrim      = ref "1"
let intervalPrim = ref "I"

exception ExpectedDir of string
let getDir x = if x = !zeroPrim then Zero else if x = !onePrim then One else raise (ExpectedDir x)