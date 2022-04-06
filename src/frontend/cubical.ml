open Language.Spec
open Prettyprinter
open Reader
open Module
open Error

let fail x = raise (ExtractionError x)

let rec extractExp : exp -> string = function
  | EKan n -> if Z.equal n Z.zero then "U" else fail "cubicaltt does not support universe hierarchy"
  | EId _ | ERef _ | EJ _ -> fail "cubicaltt does not support strict equality"
  | EPartial _ | EPartialP _ -> fail "cubicaltt does not support explicit partial"
  | EI -> fail "cubicaltt does not support explicit interval"
  | EPre _ -> fail "cubicaltt does not support explicit pretypes"
  | EInc _ | EOuc _ | ESub _ -> fail "cubicaltt does not support explicit cubical subtypes"
  | EEmpty | EIndEmpty _ -> fail "cubicaltt does not have built-in empty type"
  | EUnit | EStar | EIndUnit _ -> fail "cubicaltt does not have built-in unit type"
  | EBool | EFalse | ETrue | EIndBool _ -> fail "cubicaltt does not have built-in bool type"
  | EW _ | ESup _ | EIndW _ -> fail "cubicaltt does not have built-in W-types"
  | EIm _ | EInf _ | EIndIm _ | EJoin _ -> fail "cubicaltt does not have built-in modality"
  | EGlueElem _ | EUnglue _ -> fail "not implemented yet"
  | EGlue _ -> fail "cubicaltt does not support currying of Glue"
  | EPathP _ -> fail "cubicaltt does not support (partial) currying of PathP"
  | ETransp _ -> fail "cubicaltt does not support currying of generalized transport"
  | ESystem e -> showSystem extractExp e
  | EHComp _ -> fail "not implemented yet"
  | EApp (ETransp (p, i), a) -> Printf.sprintf "transGen %s %s %s" (extractExp p) (extractExp i) (extractExp a)
  | EApp (EApp (EPathP p, a), b) -> Printf.sprintf "PathP %s %s %s" (extractExp p) (extractExp a) (extractExp b)
  | EApp (EApp (EGlue t, _), u) -> Printf.sprintf "Glue %s %s" (extractExp t) (extractExp u)
  | EPLam (ELam (EI, (p, e))) -> Printf.sprintf "(<%s> %s)" (showIdent p) (extractExp e)
  | EPLam _ -> fail "invalid path lambda (should never happen)"
  | EAppFormula (f, x) -> Printf.sprintf "(%s @ %s)" (extractExp f) (extractExp x)
  | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "(%s /\\ %s)" (extractExp a) (extractExp b)
  | EOr (a, b) -> Printf.sprintf "(%s \\/ %s)" (extractExp a) (extractExp b)
  | ENeg a -> Printf.sprintf "-%s" (extractExp a)
  | ELam (a, (p, b)) -> Printf.sprintf "(\\%s -> %s)" (extractTele p a) (extractExp b)
  | EPi (a, (p, b)) -> Printf.sprintf "(%s -> %s)" (extractTele p a) (extractExp b)
  | ESig (a, (p, b)) -> Printf.sprintf "(%s * %s)" (extractTele p a) (extractExp b)
  | EPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (extractExp fst) (extractExp snd)
  | EFst exp -> extractExp exp ^ ".1"
  | ESnd exp -> extractExp exp ^ ".2"
  | EField _ -> fail "cubicaltt does not support named sigma accessors"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (extractExp f) (extractExp x)
  | EVar p -> showIdent p
  | EHole -> "?"
and extractTele p x = Printf.sprintf "(%s : %s)" (showIdent p) (extractExp x)

let extractDecl : decl -> string = function
  | Def (p, Some t, e) -> Printf.sprintf "%s : %s = %s" p (extractExp t) (extractExp e)
  | Def (_, None, _) -> fail "cubicaltt does not support automatic type inference of declaration"
  | Ext _ -> fail "cubicaltt does not support external plugins"
  | Axiom (p, t) -> Printf.sprintf "%s : %s = undefined" p (extractExp t)

let extractLine : line -> string = function
  | Import xs -> String.concat "\n" (List.map (Printf.sprintf "import %s") xs)
  | Plugin _  -> fail "cubicaltt does not support external plugins"
  | Option _  -> fail "cubicaltt obviously does not support Anders-specific options"
  | Decl d    -> extractDecl d

let extractContent x = String.concat "\n" (List.map extractLine x)
let extractFile : file -> string =
  fun (p, x) -> Printf.sprintf "module %s where\n%s" p (extractContent x)

let extract filename =
  let chan = open_in filename in
  Error.handleErrors
    (fun chan ->
      let lexbuf = Lexing.from_channel chan in
      let exp = parseErr Parser.file lexbuf filename in
      print_endline (extractFile exp))
    chan ()
