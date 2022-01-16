open Ident
open Expr

let showDir : dir -> string = function | Zero -> !zeroPrim | One -> !onePrim

let showFace phi =
  if Env.is_empty phi then "(1 = 1)"
  else Env.bindings phi
       |> List.map (fun (x, d) -> Printf.sprintf "(%s = %s)" (showName x) (showDir d))
       |> String.concat " "

let showSystem show xs =
  System.bindings xs
  |> List.map (fun (x, e) -> Printf.sprintf "%s → %s" (showFace x) (show e))
  |> String.concat ", "

let parens b x = if b then "(" ^ x ^ ")" else x

let rec ppExp paren e = let x = match e with
  | EKan n -> "U" ^ showSubscript n
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPi (a, (p, b)) -> showPiExp a p b
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> ppExp true exp ^ ".1"
  | ESnd exp -> ppExp true exp ^ ".2"
  | EField (exp, field) -> ppExp true exp ^ "." ^ field
  | EApp (f, x) -> Printf.sprintf "%s %s" (showExp f) (ppExp true x)
  | EVar p -> showName p
  | EHole -> "?"
  | EPre n -> "V" ^ showSubscript n
  | EPLam (ELam (_, (i, e))) -> Printf.sprintf "<%s> %s" (showName i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppExp true f) (ppExp true x)
  | ESystem x -> Printf.sprintf "[%s]" (showSystem showExp x)
  | ESub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (ppExp true a) (showExp i) (showExp u)
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "%s ∧ %s" (ppExp true a) (ppExp true b)
  | EOr (a, b) -> Printf.sprintf "%s ∨ %s" (ppExp true a) (ppExp true b)
  | ENeg a -> Printf.sprintf "-%s" (ppExp paren a)
  | ETransp (p, i) -> Printf.sprintf "transp %s %s" (ppExp true p) (ppExp true i)
  | EPathP e -> "PathP " ^ ppExp true e
  | EId e -> Printf.sprintf "Id %s" (ppExp true e)
  | ERef e -> Printf.sprintf "ref %s" (ppExp true e)
  | EJ e -> Printf.sprintf "idJ %s" (ppExp true e)
  | EHComp (t, r, u, u0) -> Printf.sprintf "hcomp %s %s %s %s" (ppExp true t) (ppExp true r) (ppExp true u) (ppExp true u0)
  | EPartial e -> Printf.sprintf "Partial %s" (ppExp true e)
  | EPartialP (t, r) -> Printf.sprintf "PartialP %s %s" (ppExp true t) (ppExp true r)
  | EInc (t, r) -> Printf.sprintf "inc %s %s" (ppExp true t) (ppExp true r)
  | EOuc e -> Printf.sprintf "ouc %s" (ppExp true e)
  | EGlue e -> Printf.sprintf "Glue %s" (ppExp true e)
  | EGlueElem (r, u, a) -> Printf.sprintf "glue %s %s %s" (ppExp true r) (ppExp true u) (ppExp true a)
  | EUnglue e -> Printf.sprintf "unglue %s" (ppExp true e)
  | EEmpty -> "𝟎" | EUnit -> "𝟏" | EBool -> "𝟐"
  | EStar -> "★" | EFalse -> "0₂" | ETrue -> "1₂"
  | EIndEmpty e -> Printf.sprintf "ind₀ %s" (ppExp true e)
  | EIndUnit e  -> Printf.sprintf "ind₁ %s" (ppExp true e)
  | EIndBool e  -> Printf.sprintf "ind₂ %s" (ppExp true e)
  | EW (a, (p, b)) -> Printf.sprintf "W %s, %s" (showTeleExp (p, a)) (showExp b)
  | ESup (a, b) -> Printf.sprintf "sup %s %s" (showExp a) (showExp b)
  | EIndW (a, b, c) -> Printf.sprintf "indᵂ %s %s %s" (showExp a) (showExp b) (showExp c)
  | EIm e -> Printf.sprintf "ℑ %s" (ppExp true e)
  | EInf e -> Printf.sprintf "ℑ-unit %s" (ppExp true e)
  | EIndIm (a, b) -> Printf.sprintf "ind-ℑ %s %s" (ppExp true a) (ppExp true b)
  in match e with
  | EVar _ | EFst _ | ESnd _ | EI | EPre _ | ESystem _
  | EKan _ | EHole | EDir _ | EPair _ | ENeg _
  | EEmpty | EUnit | EBool | EStar | EFalse | ETrue -> x
  | _ -> parens paren x

and showExp e = ppExp false e
and showTeleExp (p, x) = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTeleExp (p, a)) (showExp b)

let rec ppValue paren v = let x = match v with
  | VKan n -> "U" ^ showSubscript n
  | VLam (x, (p, clos)) -> Printf.sprintf "λ %s, %s" (showTele p x) (showClos p x clos)
  | VPi (x, (p, clos)) -> showPiValue x p clos
  | VSig (x, (p, clos)) -> Printf.sprintf "Σ %s, %s" (showTele p x) (showClos p x clos)
  | VPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VFst v -> ppValue true v ^ ".1"
  | VSnd v -> ppValue true v ^ ".2"
  | VApp (f, x) -> Printf.sprintf "%s %s" (showValue f) (ppValue true x)
  | Var (p, _) -> showName p
  | VHole -> "?"
  | VPre n -> "V" ^ showSubscript n
  | VTransp (p, i) -> Printf.sprintf "transp %s %s" (ppValue true p) (ppValue true i)
  | VPLam (VLam (_, (p, clos))) -> Printf.sprintf "<%s> %s" (showName p) (showClos p VI clos)
  | VPLam _ -> failwith "showExp: unreachable code was reached"
  | VAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppValue true f) (ppValue true x)
  | VSystem xs -> Printf.sprintf "[%s]" (showSystem showValue xs)
  | VSub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (ppValue true a) (showValue i) (showValue u)
  | VI -> !intervalPrim | VDir d -> showDir d
  | VAnd (a, b) -> Printf.sprintf "%s ∧ %s" (ppValue true a) (ppValue true b)
  | VOr (a, b) -> Printf.sprintf "%s ∨ %s" (ppValue true a) (ppValue true b)
  | VNeg a -> Printf.sprintf "-%s" (ppValue paren a)
  | VPathP v -> "PathP " ^ ppValue true v
  | VId v -> Printf.sprintf "Id %s" (ppValue true v)
  | VRef v -> Printf.sprintf "ref %s" (ppValue true v)
  | VJ v -> Printf.sprintf "idJ %s" (ppValue true v)
  | VPartialP (t, r) -> Printf.sprintf "PartialP %s %s" (ppValue true t) (ppValue true r)
  | VHComp (t, r, u, u0) -> Printf.sprintf "hcomp %s %s %s %s" (ppValue true t) (ppValue true r) (ppValue true u) (ppValue true u0)
  | VInc (t, r) -> Printf.sprintf "inc %s %s" (ppValue true t) (ppValue true r)
  | VOuc v -> Printf.sprintf "ouc %s" (ppValue true v)
  | VGlue v -> Printf.sprintf "Glue %s" (ppValue true v)
  | VGlueElem (r, u, a) -> Printf.sprintf "glue %s %s %s" (ppValue true r) (ppValue true u) (ppValue true a)
  | VUnglue v -> Printf.sprintf "unglue %s" (ppValue true v)
  | VEmpty -> "𝟎" | VUnit -> "𝟏" | VBool -> "𝟐"
  | VStar -> "★" | VFalse -> "0₂" | VTrue -> "1₂"
  | VIndEmpty v -> Printf.sprintf "ind₀ %s" (ppValue true v)
  | VIndUnit v  -> Printf.sprintf "ind₁ %s" (ppValue true v)
  | VIndBool v  -> Printf.sprintf "ind₂ %s" (ppValue true v)
  | W (x, (p, clos)) -> Printf.sprintf "W %s, %s" (showTele p x) (showClos p x clos)
  | VSup (a, b) -> Printf.sprintf "sup %s %s" (ppValue true a) (ppValue true b)
  | VIndW (a, b, c) -> Printf.sprintf "indᵂ %s %s %s" (ppValue true a) (ppValue true b) (ppValue true c)
  | VIm v -> Printf.sprintf "ℑ %s" (ppValue true v)
  | VInf v -> Printf.sprintf "ℑ-unit %s" (ppValue true v)
  | VIndIm (a, b) -> Printf.sprintf "ind-ℑ %s %s" (ppValue true a) (ppValue true b)
  in match v with
  | Var _ | VFst _ | VSnd _ | VI | VPre _ | VSystem _
  | VKan _ | VHole | VDir _ | VPair _ | VNeg _
  | VEmpty | VUnit | VBool | VStar | VFalse | VTrue -> x
  | _ -> parens paren x

and showValue v = ppValue false v
and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showValue x)

and showPiValue x p clos = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppValue true x) (showClos p x clos)
  | _           -> Printf.sprintf "Π %s, %s" (showTele p x) (showClos p x clos)

and showClos p t clos = showValue (clos (Var (p, t)))
and showTerm : term -> string = function Exp e -> showExp e | Value v -> showValue v

let showTermBind : name * record -> string option = function
  | p, (Local, _, t) -> Some (Printf.sprintf "%s := %s" (showName p) (showTerm t))
  | _, _             -> None

let showRho ctx : string = Env.bindings ctx |> List.filter_map showTermBind |> String.concat ", "

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _ -> None)
  |> String.concat "\n"
