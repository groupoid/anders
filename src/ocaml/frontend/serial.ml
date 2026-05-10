open Language.Spec
open Printer
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
  | RestoreBundle _          -> ()
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

let save filename targets =
  let b = match Kernel.Chm.proto (SaveBundle (List.map (fun (x, e) -> Def (x, EHole, e)) targets)) with
    | RestoreBundle b -> b | Error err -> raise (Kernel err) | _ -> raise ProtocolViolation
  in
  let oc = open_out_bin filename in
  let module W = Language.Encode.Encode(struct
    let put c = output_char oc c
    let puts s = output_string oc s
  end) in
  W.req (RestoreBundle b);
  close_out oc

let load filename =
  let ic = open_in_bin filename in
  let module R = Language.Decode.Decode(struct
    let get () = input_char ic
    let getn n = really_input_string ic (Int64.to_int n)
  end) in
  let b = R.req () in close_in ic;
  over (Kernel.Chm.proto b);
  match b with
  | RestoreBundle xs ->
    let rec find = function
      | [] -> (EHole, EHole)
      | Def (_, t, e) :: [] -> (e, t)
      | Assume (_, t) :: [] -> (EVar Irrefutable, t)
      | _ :: ys -> find ys
    in find xs
  | _ -> (EHole, EHole)

let receive () = ()
