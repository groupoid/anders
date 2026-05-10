open Language.Encode
open Language.Decode
open Language.Spec
open Check
open Elab
open Term
open Rbv

let ctx : ctx ref = ref Env.empty

let getUnitVal opt = function
  | "tt" | "true" -> true
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let showIdent = function Ident (s, _) -> s | Irrefutable -> "_"
let rollup ctx e = rbV (eval ctx e)
let getTerm e = if !Prefs.preeval then Value (eval !ctx e) else Exp e
let assign x te t e = ctx := Env.add (ident x) (Global, Exp te, Value t, getTerm e) !ctx

let get_bundle ctx x e =
  let v = eval ctx e in
  let t = infer ctx e in
  let seen = ref IdentSet.empty in
  let bundle = ref [] in
  let rec collect x =
    if IdentSet.mem x !seen then () else
    begin
      seen := IdentSet.add x !seen;
      match Env.find_opt x ctx with
      | Some (Global, Exp te, Value _, Exp e) ->
        let deps = IdentSet.union (exp_support IdentSet.empty te) (exp_support IdentSet.empty e) in
        IdentSet.iter collect deps;
        bundle := (showIdent x, te, e) :: !bundle
      | Some (Global, Exp te, Value _, Value v) ->
        let e = rbV v in
        let deps = IdentSet.union (exp_support IdentSet.empty te) (exp_support IdentSet.empty e) in
        IdentSet.iter collect deps;
        bundle := (showIdent x, te, e) :: !bundle
      | _ -> ()
    end
  in
  let final_e = match e with
    | EVar i -> (match Env.find_opt i ctx with Some (_, _, _, Exp e) -> e | _ -> rbV v)
    | _ -> rbV v
  in
  let deps = IdentSet.union (exp_support IdentSet.empty (rbV t)) (exp_support IdentSet.empty final_e) in
  IdentSet.iter collect deps;
  List.rev !bundle @ [(x, rbV t, final_e)]

let promote fn = try fn () with exc -> Error (extErr exc)

let proto : req -> resp = function
  | Check (e0, t0)     -> promote (fun () -> reset_fuel (); let t = freshExp t0 in
    ignore (extSet (infer !ctx t)); check !ctx (freshExp e0) (eval !ctx t); OK)
  | Infer e            -> promote (fun () -> Term (rbV (infer !ctx (freshExp e))))
  | Eval e             -> promote (fun () -> Term (rbV (eval !ctx (freshExp e))))
  | Conv (e1, e2)      -> promote (fun () -> Bool (conv (eval !ctx (freshExp e1))
                                                         (eval !ctx (freshExp e2))))
  | Rollup e           -> promote (fun () -> Term (rollup !ctx (freshExp e)))
  | Bundle (x, e)      -> promote (fun () -> Bundle (get_bundle !ctx x (freshExp e)))
  | Def (x, t0, e0)    -> promote (fun () -> reset_fuel ();
    if Env.mem (ident x) !ctx then Error (AlreadyDeclared x)
    else (let t = freshExp t0 in let e = freshExp e0 in
      ignore (extSet (infer !ctx t)); let t' = eval !ctx t in
      check !ctx e t'; assign x t0 t' e; OK))
  | Assign (x, t0, e0) -> promote (fun () -> reset_fuel ();
    if Env.mem (ident x) !ctx then Error (AlreadyDeclared x)
    else (let t = freshExp t0 in ignore (extSet (infer !ctx t));
          assign x t0 (eval !ctx t) (freshExp e0); OK))
  | Assume (x, t0)     -> promote (fun () -> reset_fuel (); let t = freshExp t0 in
    let y = ident x in if Env.mem y !ctx then Error (AlreadyDeclared x)
    else (ignore (extSet (infer !ctx t)); let t' = eval !ctx t in
          ctx := Env.add y (Global, Exp t0, Value t', Value (Var (y, t'))) !ctx; OK))
  | Erase x            -> ctx := Env.remove (ident x) !ctx; OK
  | Wipe               -> ctx := Env.empty; OK
  | Set (p, x)         ->
  begin match p with
    | "trace"           -> promote (fun () -> Prefs.trace           := getBoolVal p x; OK)
    | "preeval"         -> promote (fun () -> Prefs.preeval         := getBoolVal p x; OK)
    | "girard"          -> promote (fun () -> Prefs.girard          := getUnitVal p x; OK)
    | "irrelevance"     -> promote (fun () -> Prefs.irrelevance     := getUnitVal p x; OK)
    | "impredicativity" -> promote (fun () -> Prefs.impredicativity := getUnitVal p x; OK)
    | _                 -> Error (InvalidOpt p)
  end
  | Version            -> Version (1L, 3L, 0L)
  | Ping               -> Pong
