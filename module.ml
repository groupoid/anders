open Prelude
open Ident
open Elab
open Expr

type command =
  | Nope
  | Eval    of exp
  | Action  of string
  | Command of string * exp

type decl =
  | Def of string * exp option * exp
  | Axiom of string * exp
  | Record of string * tele list * tele list

type line =
  | Import of string list
  | Option of string * string
  | Decl of decl

type content = line list
type file = string * content

let moduleSep = '/'
let getPath = String.split_on_char moduleSep >> String.concat Filename.dir_sep

let showDecl : decl -> string = function
  | Def (p, Some exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | Def (p, None, exp) -> Printf.sprintf "def %s := %s" p (showExp exp)
  | Axiom (p, exp) -> Printf.sprintf "axiom %s : %s" p (showExp exp)
  | Record (p, xs, ys) ->
    Printf.sprintf "record %s %s := %s" p
      (String.concat " " (List.map showTeleExp xs))
      (String.concat "\n" (List.map showTeleExp ys))

let showLine : line -> string = function
  | Import p -> Printf.sprintf "import %s" (String.concat " " p)
  | Option (opt, value) -> Printf.sprintf "option %s %s" opt value
  | Decl d -> showDecl d

let showContent x = String.concat "\n" (List.map showLine x)
let showFile : file -> string = function | (p, x) -> Printf.sprintf "module %s where\n%s" p (showContent x)

let freshTele ns : tele -> tele = fun (p, e) ->
  let q = fresh p in let e' = salt !ns e in
  ns := Env.add p q !ns; (q, e')

let freshDecl : decl -> decl = function
  | Def (p, Some exp1, exp2) -> Def (p, Some (freshExp exp1), freshExp exp2)
  | Def (p, None, exp) -> Def (p, None, freshExp exp)
  | Axiom (p, exp) -> Axiom (p, freshExp exp)
  | Record (p, xs, ys) ->
    let ns = ref Env.empty in
    let xs = List.map (freshTele ns) xs in
    let ys = List.map (freshTele ns) ys in
    Record (p, xs, ys)