open Language.Spec
open Module
open Error
open Radio

module Files = Set.Make(String)

let ext x = x ^ ".anders"
let plugExt x = x ^ ".cmxs"

type plug = string -> exp -> string -> exp
let plugin : (plug option) ref = ref None

let getDeclName = function
  | Def (p, _, _) | Ext (p, _, _) | Axiom (p, _) -> p

let rec checkDecl d =
  match d with
  | Def (p, Some t, e) -> def p t e
  | Def (p, None, e) -> assign p (infer e) e
  | Ext (p, t, v) -> begin match !plugin with
    | Some g -> checkDecl (Def (p, Some t, g p t v))
    | None -> failwith "external plugin isn’t loaded"
  end
  | Axiom (p, t) -> assume p t

let getBoolVal opt = function
  | "tt" | "true"  -> true
  | "ff" | "false" -> false
  | value -> raise (UnknownOptionValue (opt, value))

let rec checkLine fs : line -> Files.t = function
  | Decl d ->
    if !Prefs.verbose then begin
      Printf.printf "Checking: %s\n" (getDeclName d); flush_all ()
    end; checkDecl d; fs
  | Plugin p ->
    plugin := None;
    Dynlink.loadfile (plugExt p);
    begin match !plugin with
      | Some _ -> ()
      | None   -> failwith (Printf.sprintf "Module “%s” was not initialized." p)
    end; fs
  | Option (opt, value) ->
    begin match opt with
      | "girard"   | "irrelevance"
      | "pre-eval" | "impredicativity" -> set opt value
      | "verbose" -> Prefs.verbose := getBoolVal opt value
      | _         -> raise (UnknownOption opt)
    end; fs
  | Import xs -> List.fold_left (fun fs x -> let path = ext x in
    if Files.mem path fs then fs else checkFile fs path) fs xs
and checkFile fs path =
  let filename = Filename.basename path in

  let chan = open_in path in
  let (name, con) = Reader.parseErr Parser.file (Lexing.from_channel chan) path in
  close_in chan; if !Prefs.verbose then begin
    Printf.printf "Parsed “%s” successfully.\n" filename; flush_all ()
  end;

  if ext name = filename then ()
  else raise (InvalidModuleName (name, filename));

  let res = checkContent (Files.add path fs) con in
  print_endline ("File “" ^ filename ^ "” checked."); res
and checkContent fs xs = List.fold_left checkLine fs xs
