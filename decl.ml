open Expr
open Eval
open Check
open Error

type state = rho * gamma * Files.t
let ext x = x ^ ".tt"

let rec listLast : 'a list -> 'a = function
  | []      -> raise (Failure "listLast")
  | [x]     -> x
  | x :: xs -> listLast xs

let getDeclName : decl -> name = function
  | Annotated (p, _, _)
  | NotAnnotated (p, _) -> p

let checkDecl rho gma d : rho * gamma =
  match d with
  | Annotated (p, a, e) ->
    let b = infer 1 rho gma a in
    if not (isVSet b) then raise (ExpectedVSet b) else ();
    let a' = eval a rho in
    let gma' = upGlobal gma p a' in
    ignore (check 1 rho gma' e a');
    (upDec rho d, gma')
  | NotAnnotated (p, e) ->
    let a = infer 1 rho gma e in
    let gma' = upGlobal gma p a in
    ignore (check 1 rho gma' e a);
    (upDec rho d, gma')

let rec checkContent p : content -> state =
  let (rho, gma, checked) = p in function
  | Decl (d, rest) ->
    let name = getDeclName d in
    Printf.printf "Checking: %s\n" (Expr.showName name);
    let (rho', gma') = checkDecl rho gma d in
    checkContent (rho', gma', checked) rest
  | Import (x, rest) ->
    let path = ext x in
    let p' =
      if Files.mem path checked then p
      else checkFile p path in
    checkContent p' rest
  | End -> (rho, gma, checked)
and checkFile p path =
  let (rho, gma, checked) = p in
  let filename = Filename.basename path in
  let chan = open_in path in
  let (name, con) = Lexparse.parseErr Parser.file (Lexing.from_channel chan) in
  close_in chan; Printf.printf "Parsed “%s” successfully.\n" filename;
  if ext name = filename then ()
  else raise (InvalidModuleName (name, filename));
  let res = checkContent (rho, gma, Files.add path checked) con in
  Printf.printf "File loaded.\n"; res