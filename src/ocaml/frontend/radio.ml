open Language.Encode
open Language.Decode
open Language.Spec
open Prettyprinter
open Error

let trace x xs = Printf.printf "%s: [%s]\n" x (String.concat "; " (List.map showExp xs)); flush_all ()

let traceHole e gma = print_string "\nHole:\n\n";
  List.iter (fun (i, e') -> Printf.printf "%s : %s\n" (showIdent i) (showExp e')) gma;
  print_string ("\n" ^ String.make 80 '-' ^ "\n" ^ showExp e ^ "\n\n")

let showResp = function
  | Version (i, j, k) -> Printf.printf "Version (%Ld, %Ld, %Ld)\n" i j k
  | Trace (x, xs)     -> trace x xs
  | Hole (e, gma)     -> traceHole e gma
  | Error err         -> print_string (prettyPrintError err)
  | Bool false        -> print_string "false\n"
  | Bool true         -> print_string "true\n"
  | Term e            -> Printf.printf "%s\n" (showExp e)
  | Bundle _          -> ()
  | Pong              -> print_string "pong\n"
  | OK                -> print_string "OK\n"

let () = Kernel.Trace.callback := showResp

let over = function
  | OK            -> ()
  | Error err     -> raise (Kernel err)
  | r             -> showResp r; raise ProtocolViolation

let recvTerm = function
  | Term e        -> e
  | Error err     -> raise (Kernel err)
  | r             -> showResp r; raise ProtocolViolation

let eval e  = recvTerm (Kernel.Chm.proto (Eval e))
let infer e = recvTerm (Kernel.Chm.proto (Infer e))

let def p t e = over (Kernel.Chm.proto (Def (p, t, e)))
let assign p t e = over (Kernel.Chm.proto (Assign (p, t, e)))
let assume p t = over (Kernel.Chm.proto (Assume (p, t)))

let set p x = over (Kernel.Chm.proto (Set (p, x)))
let wipe () = over (Kernel.Chm.proto Wipe)

let save filename x e =
  let b = match Kernel.Chm.proto (Bundle (x, e)) with
    | Bundle b -> b | Error err -> raise (Kernel err) | _ -> raise ProtocolViolation
  in
  let oc = open_out_bin filename in
  let module W = Language.Encode.Encode(struct
    let put c = output_char oc c
    let puts s = output_string oc s
  end) in
  output_byte oc (if !Kernel.Prefs.girard then 1 else 0);
  output_byte oc (if !Kernel.Prefs.impredicativity then 1 else 0);
  output_byte oc (if !Kernel.Prefs.irrelevance then 1 else 0);
  output_binary_int oc (List.length b);
  List.iter (fun (x, t, e) ->
    output_binary_int oc (String.length x);
    output_string oc x;
    W.exp t;
    W.exp e) b;
  close_out oc

let load filename =
  let ic = open_in_bin filename in
  let module R = Language.Decode.Decode(struct
    let get () = input_char ic
    let getn n = really_input_string ic (Int64.to_int n)
  end) in
  let g = input_byte ic in
  let i = input_byte ic in
  let ir = input_byte ic in
  set "girard" (if g = 1 then "tt" else "ff");
  set "impredicativity" (if i = 1 then "tt" else "ff");
  set "irrelevance" (if ir = 1 then "tt" else "ff");
  let n = input_binary_int ic in
  let rec read acc n =
    if n = 0 then acc else
      let len = input_binary_int ic in
      let x = really_input_string ic len in
      let t = R.exp () in
      let e = R.exp () in
      read ((x, t, e) :: acc) (n-1)
  in
  let b = read [] n in close_in ic;
  List.iter (fun (x, t, e) ->
    Printf.printf "Checking: %s\n" x;
    ignore (Kernel.Chm.proto (Def (x, t, e)))) b;
  let (x, t, e) = List.hd (List.rev b) in (e, t)

let receive () = ()
