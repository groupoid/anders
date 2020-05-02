open Expr

exception TypeIneq of value * value
exception InferError of exp
exception VariableNotFound of name
exception InvalidApplication of value * value
exception ExpectedPi of value
exception ExpectedSig of value
exception ExpectedESet of exp
exception ExpectedVSet of value
exception UnknownCommand of string
exception Parser of int * int
exception InvalidModuleName of string * string

let prettyPrintError : exn -> unit = function
  | TypeIneq (u, v) ->
    Printf.printf "Type mismatch:\n%s\n  =/=\n%s\n"
                  (showValue u) (showValue v)
  | InferError e ->
    Printf.printf "Cannot infer type of\n  %s\n" (showExp e)
  | VariableNotFound p ->
    Printf.printf "Variable %s was not found\n" (showName p)
  | InvalidApplication (x, y) ->
    Printf.printf "Invalid application \n  %s\nto\n  %s\n"
                  (showValue x) (showValue y)
  | InvalidModuleName (name, filename) ->
    Printf.printf "Module “%s” does not match name of its file: %s\n"
                  name filename
  | ExpectedESet x ->
    Printf.printf "  %s\nexpected to be universe\n" (showExp x)
  | ExpectedVSet x ->
    Printf.printf "  %s\nexpected to be universe\n" (showValue x)
  | ExpectedPi x ->
    Printf.printf "  %s\nexpected to be Pi-type\n" (showValue x)
  | ExpectedSig x ->
    Printf.printf "  %s\nexpected to be Sigma-type\n" (showValue x)
  | UnknownCommand s ->
    Printf.printf "Unknown command “%s”\n" s
  | Parser (x, y) ->
    Printf.printf "Parsing error at characters %d:%d\n" x y
  | Sys_error s -> print_endline s
  | ex -> Printf.printf "uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default