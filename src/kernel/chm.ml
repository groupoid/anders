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

let getTerm e = if !Prefs.preeval then Value (eval !ctx e) else Exp e
let assign x t e = ctx := Env.add (ident x) (Global, Value t, getTerm e) !ctx

let promote fn = try fn () with exc -> Error (extErr exc)

let proto : req -> resp = function
  | Check (e0, t0)     -> promote (fun () -> let t = freshExp t0 in
    ignore (extSet (infer !ctx t)); check !ctx (freshExp e0) (eval !ctx t); OK)
  | Infer e            -> promote (fun () -> Term (rbV (infer !ctx (freshExp e))))
  | Eval e             -> promote (fun () -> Term (rbV (eval !ctx (freshExp e))))
  | Conv (e1, e2)      -> promote (fun () -> Bool (conv (eval !ctx (freshExp e1))
                                                        (eval !ctx (freshExp e2))))
  | Def (x, t0, e0)    -> promote (fun () ->
    if Env.mem (ident x) !ctx then Error (AlreadyDeclared x)
    else (let t = freshExp t0 in let e = freshExp e0 in
      ignore (extSet (infer !ctx t)); let t' = eval !ctx t in
      check !ctx e t'; assign x t' e; OK))
  | Assign (x, t0, e0) -> promote (fun () ->
    if Env.mem (ident x) !ctx then Error (AlreadyDeclared x)
    else (let t = freshExp t0 in ignore (extSet (infer !ctx t));
          assign x (eval !ctx t) (freshExp e0); OK))
  | Assume (x, t0)     -> promote (fun () -> let t = freshExp t0 in
    let y = ident x in if Env.mem y !ctx then Error (AlreadyDeclared x)
    else (ignore (extSet (infer !ctx t)); let t' = eval !ctx t in
          ctx := Env.add y (Global, Value t', Value (Var (y, t'))) !ctx; OK))
  | Erase x            -> ctx := Env.remove (ident x) !ctx; OK
  | Wipe               -> ctx := Env.empty; OK
  | Set (p, x)         ->
  begin match p with
    | "trace"           -> promote (fun () -> Prefs.trace           := getBoolVal p x; OK)
    | "pre-eval"        -> promote (fun () -> Prefs.preeval         := getBoolVal p x; OK)
    | "girard"          -> promote (fun () -> Prefs.girard          := getUnitVal p x; OK)
    | "irrelevance"     -> promote (fun () -> Prefs.irrelevance     := getUnitVal p x; OK)
    | "impredicativity" -> promote (fun () -> Prefs.impredicativity := getUnitVal p x; OK)
    | _                 -> Error (InvalidOpt p)
  end
  | Version            -> Version (1L, 3L, 0L)
  | Ping               -> Pong

let () = try while true do
  Serialize.resp (try proto (Deserialize.req ())
    with Invalid_argument xs
       | Failure xs -> Error (Unknown xs));
  flush_all ()
done with End_of_file -> ()