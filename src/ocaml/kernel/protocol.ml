open Language.Prelude
open Language.Spec
open Check
open Elab
open Term
open Rbv

let ctx : ctx ref = ref Env.empty
let history : string list ref = ref []

let getUnitVal opt = function
  | "tt" | "true" -> true
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (Internal (InvalidOptValue (opt, value)))

let showIdent = function
  | Irrefutable -> "_"
  | Ident (xs, 0L) -> xs
  | Ident (xs, n) -> xs ^ showSubscript (Z.of_int64 n)

let rollup ctx e = rbV (eval ctx e)
let getTerm e = if !Options.preeval then Value (eval !ctx e) else Exp e
let assign x te t e =
  if not (List.mem x !history) then history := x :: !history;
  ctx := Env.add (ident x) (Global, Exp te, Value t, getTerm e) !ctx

let get_bundle ctx targets =
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
        bundle := Def (showIdent x, te, e) :: !bundle
      | Some (Global, Exp te, Value _, Value (Var (y, _))) when x = y ->
        let deps = exp_support IdentSet.empty te in
        IdentSet.iter collect deps;
        bundle := Assume (showIdent x, te) :: !bundle
      | Some (Global, Exp te, Value _, Value v) ->
        let e = rbV v in
        let deps = IdentSet.union (exp_support IdentSet.empty te) (exp_support IdentSet.empty e) in
        IdentSet.iter collect deps;
        bundle := Def (showIdent x, te, e) :: !bundle
      | _ -> ()
    end
  in
  List.iter (fun r ->
    let x = match r with Def (x, _, _) | Assume (x, _) | Assign (x, _, _) -> x | _ -> failwith "Invalid bundle target" in
    let e = match r with Def (_, _, e) -> e | Assume (x, _) -> EVar (ident x) | _ -> failwith "Invalid bundle target" in
    let v = eval ctx e in
    let t = infer ctx e in
    let final_e = match e with
      | EVar i -> (match Env.find_opt i ctx with Some (_, _, _, Exp e) -> e | _ -> rbV v)
      | _ -> rbV v
    in
    let deps = IdentSet.union (exp_support IdentSet.empty (rbV t)) (exp_support IdentSet.empty final_e) in
    IdentSet.iter collect deps;
    let i = ident x in
    if not (IdentSet.mem i !seen) then (
      seen := IdentSet.add i !seen;
      bundle := (match r with Assume _ -> Assume (x, rbV t) | _ -> Def (x, rbV t, final_e)) :: !bundle
    )
  ) targets;
  let res = List.rev !bundle in
  let h_rev = List.rev !history in
  let pos x =
    let rec find i = function
      | [] -> 1000000 (* not in history, put at end *)
      | y :: ys -> if (match x with Def (n, _, _) | Assume (n, _) | Assign (n, _, _) -> n = y | _ -> false) then i else find (i + 1) ys
    in find 0 h_rev
  in
  let sorted = List.sort (fun x y -> compare (pos x) (pos y)) res in
  let config = [
    Set ("girard", if !Options.girard then "tt" else "ff");
    Set ("preeval", if !Options.preeval then "true" else "false");
    Set ("irrelevance", if !Options.irrelevance then "tt" else "ff");
    Set ("impredicativity", if !Options.impredicativity then "tt" else "ff");
    Set ("gidx", Int64.to_string !Sequence.gidx)
  ] in
  config @ sorted

let promote fn = try fn () with exc -> Error (extErr exc)

let rec proto : req -> resp = function
  | Check (e0, t0)     -> promote (fun () -> reset_fuel (); let t = freshExp t0 in
    ignore (extSet (infer !ctx t)); check !ctx (freshExp e0) (eval !ctx t); OK)
  | Infer e            -> promote (fun () -> Term (rbV (infer !ctx (freshExp e))))
  | Eval e             -> promote (fun () -> Term (rbV (eval !ctx (freshExp e))))
  | Conv (e1, e2)      -> promote (fun () -> Bool (conv (eval !ctx (freshExp e1)) (eval !ctx (freshExp e2))))
  | Rollup e           -> promote (fun () -> Term (rollup !ctx (freshExp e)))
  | RestoreBundle xs   -> List.iter (fun r -> ignore (proto r)) xs; OK
  | SaveBundle xs      -> promote (fun () -> RestoreBundle (get_bundle !ctx xs))
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
    else (if not (List.mem x !history) then history := x :: !history;
          ignore (extSet (infer !ctx t)); let t' = eval !ctx t in
          ctx := Env.add y (Global, Exp t0, Value t', Value (Var (y, t'))) !ctx; OK))
  | Erase x            -> history := List.filter ((<>) x) !history; ctx := Env.remove (ident x) !ctx; OK
  | Wipe               -> history := []; ctx := Env.empty; OK
  | Set (p, x)         ->
  begin match p with
    | "trace"           -> promote (fun () -> Options.trace           := getBoolVal p x; OK)
    | "preeval"         -> promote (fun () -> Options.preeval         := getBoolVal p x; OK)
    | "girard"          -> promote (fun () -> Options.girard          := getUnitVal p x; OK)
    | "irrelevance"     -> promote (fun () -> Options.irrelevance     := getUnitVal p x; OK)
    | "impredicativity" -> promote (fun () -> Options.impredicativity := getUnitVal p x; OK)
    | "gidx"            -> promote (fun () -> Sequence.gidx := max !Sequence.gidx (Int64.of_string x); OK)
    | _                 -> Error (InvalidOpt p)
  end
  | Version            -> Version (1L, 3L, 0L)
  | Ping               -> Pong
