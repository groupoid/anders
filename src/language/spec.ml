type ident =
  | Irrefutable
  | Ident of string * int64

module Ident =
struct
  type t = ident
  let compare x y =
    match (x, y) with
    | Irrefutable, Irrefutable -> 0
    | Irrefutable, Ident _ -> -1
    | Ident _, Irrefutable -> 1
    | Ident (p, a), Ident (q, b) ->
      if p = q then compare a b
      else compare p q
end

module Env = Map.Make(Ident)

type dir = Zero | One

module Dir =
struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

type face = dir Env.t
let eps : face = Env.empty

module Face =
struct
  type t = face
  let compare = Env.compare Dir.compare
end

module System = Map.Make(Face)

type tag = (string option) ref

(* Language Expressions *)

type exp =
  | EPre of Z.t | EKan of Z.t                                                          (* cosmos *)
  | EVar of ident | EHole                                                           (* variables *)
  | EPi of exp * (ident * exp) | ELam of exp * (ident * exp) | EApp of exp * exp           (* pi *)
  | ESig of exp * (ident * exp) | EPair of tag * exp * exp                              (* sigma *)
  | EFst of exp | ESnd of exp | EField of exp * string                    (* simga elims/records *)
  | EId of exp | ERef of exp | EJ of exp                                      (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp       (* CCHM interval *)
  | ETransp of exp * exp | EHComp of exp * exp * exp * exp                     (* Kan operations *)
  | EPartial of exp | EPartialP of exp * exp | ESystem of exp System.t      (* partial functions *)
  | ESub of exp * exp * exp | EInc of exp * exp | EOuc of exp                (* cubical subtypes *)
  | EGlue of exp | EGlueElem of exp * exp * exp | EUnglue of exp * exp * exp          (* glueing *)
  | EEmpty | EIndEmpty of exp                                                               (* 𝟎 *)
  | EUnit | EStar | EIndUnit of exp                                                         (* 𝟏 *)
  | EBool | EFalse | ETrue | EIndBool of exp                                                (* 𝟐 *)
  | EW of exp * (ident * exp) | ESup of exp * exp | EIndW of exp * exp * exp                (* W *)
  | EIm of exp | EInf of exp | EIndIm of exp * exp | EJoin of exp      (* Infinitesimal Modality *)

type extension =
  | ECoeq of exp | EIota of exp | EResp of exp | EIndCoeq of exp                  (* Coequalizer *)
  | EDisc of exp | EBase of exp | EHub of exp | ESpoke of exp | EIndDisc of exp          (* Disc *)

type tele = ident * exp

let eLam p a b = ELam (a, (p, b))
let ePi  p a b = EPi  (a, (p, b))
let eSig p a b = ESig (a, (p, b))
let eW   p a b = EW   (a, (p, b))

let ezero = EDir Zero
let eone  = EDir One

let ident x = Ident (x, 0L)
let decl x = EVar (ident x)

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

(* Kernel Interface *)

type req =
  (* checker & evaluator *)
  | Check  of exp * exp
  | Infer  of exp
  | Eval   of exp
  | Conv   of exp * exp
  (* context *)
  | Def    of string * exp * exp
  | Assign of string * exp * exp
  | Assume of string * exp
  | Erase  of string
  | Wipe
  (* configuration *)
  | Set    of string * string
  | Version
  | Ping

type error =
  | Unknown          of string
  | Ineq             of exp * exp
  | ExpectedPi       of exp
  | ExpectedSig      of exp
  | ExpectedType     of exp
  | ExpectedKan      of exp
  | ExpectedPath     of exp
  | ExpectedSubtype  of exp
  | ExpectedSystem   of exp
  | ExpectedConj     of exp
  | ExpectedIm       of exp
  | ExpectedInf      of exp
  | ExpectedGlue     of exp
  | ExpectedSup      of exp
  | DNFSolverError   of exp * dir
  | AlreadyDeclared  of string
  | VariableNotFound of ident
  | InferError       of exp
  | Traceback        of error * (exp * exp) list
  | InvalidOpt       of string
  | InvalidOptValue  of string * string

type resp =
  | Version of int64 * int64 * int64
  | Trace   of string * exp list
  | Hole    of exp * (ident * exp) list
  | Error   of error
  | Bool    of bool
  | Term    of exp
  | Pong
  | OK
