open Ident
open Expr

exception Restart
exception InferError of exp
exception ExpectedPi of value
exception ExpectedESet of exp
exception ExpectedSig of value
exception ExpectedVSet of value
exception Parser of int * string
exception UnknownOption of string
exception UnknownCommand of string
exception VariableNotFound of name
exception TypeIneq of value * value
exception AlreadyDeclared of string
exception InvalidFormulaNeg of value
exception InvalidFormulaOr of value * value
exception InvalidFormulaAnd of value * value
exception InvalidApplication of value * value
exception InvalidModuleName of string * string
exception UnknownOptionValue of string * string

let prettyPrintError : exn -> unit = function
  | AlreadyDeclared p -> Printf.printf "“%s” is already declared.\n" p
  | InvalidFormulaNeg v -> Printf.printf "Cannot evaluate invalid formula:\n  -%s\n" (showValue v)
  | InvalidFormulaOr (u, v) -> Printf.printf "Cannot evaluate invalid formula:\n  %s ∨ %s\n" (showValue u) (showValue v)
  | InvalidFormulaAnd (u, v) -> Printf.printf "Cannot evaluate invalid formula:\n  %s ∧ %s\n" (showValue u) (showValue v)
  | TypeIneq (u, v) -> Printf.printf "Type mismatch:\n%s\n  =/=\n%s\n" (showValue u) (showValue v)
  | InferError e -> Printf.printf "Cannot infer type of\n  %s\n" (showExp e)
  | VariableNotFound p -> Printf.printf "Variable %s was not found\n" (showName p)
  | InvalidApplication (x, y) -> Printf.printf "Invalid application \n  %s\nto\n  %s\n" (showValue x) (showValue y)
  | InvalidModuleName (name, filename) -> Printf.printf "Module “%s” does not match name of its file: %s\n" name filename
  | ExpectedESet x -> Printf.printf "  %s\nexpected to be universe\n" (showExp x)
  | ExpectedVSet x -> Printf.printf "  %s\nexpected to be universe\n" (showValue x)
  | ExpectedPi x -> Printf.printf "  %s\nexpected to be Pi-type\n" (showValue x)
  | ExpectedSig x -> Printf.printf "  %s\nexpected to be Sigma-type\n" (showValue x)
  | UnknownCommand s -> Printf.printf "Unknown command “%s”\n" s
  | UnknownOption opt -> Printf.printf "Unknown option “%s”\n" opt
  | UnknownOptionValue (opt, value) -> Printf.printf "Unknown value “%s” of option “%s”\n" value opt
  | Parser (x, buf) -> Printf.printf "Parsing error at line %d: “%s”\n" x buf
  | Sys_error s -> print_endline s
  | Restart -> raise Restart
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default