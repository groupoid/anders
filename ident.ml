type name =
  | Irrefutable
  | Name of string * int

let showName : name -> string = function
  | Irrefutable -> "_"
  | Name (p, n) -> if !Prefs.indices then p ^ "#" ^ string_of_int n else p

module Name =
struct
  type t = name
  let compare x y =
    match (x, y) with
    | Irrefutable, Irrefutable -> 0
    | Irrefutable, Name _ -> -1
    | Name _, Irrefutable -> 1
    | Name (p, a), Name (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Name)
type dir   = Zero | One
type face  = dir Env.t

module OrderedList (Ord : Map.OrderedType) =
struct
  type t = Ord.t list

  let rec compare a b =
    match (a, b) with
    |   [],      []    -> 0
    |   [],    _ :: _  -> -1
    | _ :: _,    []    -> 1
    | x :: xs, y :: ys -> begin
      match Ord.compare x y with
      | 0 -> compare xs ys
      | n -> n
    end
end

module OrderedPair (X : Map.OrderedType)
                   (Y : Map.OrderedType) =
struct
  type t = X.t * Y.t

  let compare a b =
    match X.compare (fst a) (fst b) with
    | 0 -> Y.compare (snd a) (snd b)
    | n -> n
end

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

module Dir =
struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

module Face =
struct
  type t = face
  module X = OrderedList(OrderedPair(Name)(Dir))
  let compare a b = X.compare (Env.bindings a) (Env.bindings b)
end

module Files = Set.Make(String)

let inc : int ref = ref 0
let gen () = inc := !inc + 1; !inc

let fresh : name -> name = function
  | Irrefutable -> Irrefutable | Name (p, _) -> Name (p, gen ())

let matchIdent p : name -> bool = function
  | Irrefutable -> false | Name (q, _) -> p = q

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let rec showSubscript x =
  if x < 0 then failwith "showSubscript: expected positive integer"
  else if x = 0 then "" else showSubscript (x / 10) ^ getDigit (x mod 10)

let freshName x = let n = gen () in Name (x ^ showSubscript n, n)

module Atom =
struct
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
