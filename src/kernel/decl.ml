open Module
open Check
open Error
open Ident
open Expr
open Elab

let ext x = x ^ ".anders"

type state = ctx * Files.t
let empty : state = (Env.empty, Files.empty)

let plugExt x = x ^ ".cmxs"

type plug = string -> exp -> string -> exp
let plugin : (plug option) ref = ref None

let getDeclName : decl -> string = function Def (p, _, _) | Ext (p, _, _) | Axiom (p, _) -> p
let getTerm e ctx = if !Prefs.preeval then Value (eval e ctx) else Exp e

let rec checkDecl ctx d : ctx =
  let x = getDeclName d in if Env.mem (name x) ctx then
    raise (AlreadyDeclared x);
  match d with
  | Def (p, Some a, e) ->
    ignore (extSet (infer ctx a));
    let t = eval a ctx in check ctx e t;
    Env.add (name p) (Global, Value t, getTerm e ctx) ctx
  | Ext (p, t, v) -> begin match !plugin with
    | Some g -> checkDecl ctx (Def (p, Some t, g p t v))
    | None -> failwith "external plugin isn’t loaded"
  end
  | Def (p, None, e) ->
    Env.add (name p) (Global, Value (infer ctx e), getTerm e ctx) ctx
  | Axiom (p, a) ->
    ignore (extSet (infer ctx a)); let x = name p in
    let t = eval a ctx in Env.add x (Global, Value t, Value (Var (x, t))) ctx

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (UnknownOptionValue (opt, value))

let rec checkLine st : line -> state =
  let (ctx, checked) = st in function
  | Decl d ->
    if !Prefs.verbose then begin
      Printf.printf "Checking: %s\n" (getDeclName d); flush_all ()
    end; (checkDecl ctx (freshDecl d), checked)
  | Plugin p ->
    plugin := None;
    Dynlink.loadfile (plugExt p);
    begin match !plugin with
      | Some _ -> ()
      | None   -> failwith (Printf.sprintf "Module “%s” was not initialized." p)
    end; st
  | Option (opt, value) ->
    begin match opt with
      | "girard"      -> Prefs.girard      := getBoolVal opt value
      | "irrelevance" -> Prefs.irrelevance := getBoolVal opt value
      | "verbose"     -> Prefs.verbose     := getBoolVal opt value
      | "pre-eval"    -> Prefs.preeval     := getBoolVal opt value
      | _             -> raise (UnknownOption opt)
    end; st
  | Import xs -> List.fold_left (fun st x -> let path = ext x in
    if Files.mem path checked then st else checkFile st path) st xs
and checkFile p path =
  let (ctx, checked) = p in
  let filename = Filename.basename path in

  let chan = open_in path in
  let (name, con) = Reader.parseErr Parser.file (Lexing.from_channel chan) path in
  close_in chan; if !Prefs.verbose then begin
    Printf.printf "Parsed “%s” successfully.\n" filename; flush_all ()
  end;

  if ext name = filename then ()
  else raise (InvalidModuleName (name, filename));

  let res = checkContent (ctx, Files.add path checked) con in
  print_endline ("File “" ^ filename ^ "” checked."); res
and checkContent st xs = List.fold_left checkLine st xs
