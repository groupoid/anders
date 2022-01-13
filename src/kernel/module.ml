open Prettyprinter
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
  | Ext of string * exp * string
  | Axiom of string * exp

type line =
  | Import of string list
  | Plugin of string
  | Option of string * string
  | Decl of decl

type content = line list
type file = string * content

let moduleSep = '/'
let getPath = String.split_on_char moduleSep >> String.concat Filename.dir_sep

let showDecl : decl -> string = function
  | Def (p, Some exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | Def (p, None, exp) -> Printf.sprintf "def %s := %s" p (showExp exp)
  | Ext (p, t, v) -> Printf.sprintf "def %s : %s :=\nbegin%send" p (showExp t) v
  | Axiom (p, exp) -> Printf.sprintf "axiom %s : %s" p (showExp exp)

let showLine : line -> string = function
  | Import p -> Printf.sprintf "import %s" (String.concat " " p)
  | Plugin p -> Printf.sprintf "plugin %s" p
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
  | Ext (p, t, v) -> Ext (p, freshExp t, v)
  | Axiom (p, exp) -> Axiom (p, freshExp exp)
