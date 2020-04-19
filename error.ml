open Expr

exception TypeMismatch of value * value
exception InferError of exp
exception VariableNotFound of name
exception InvalidApplication of value * value
exception ExpectedPi of value
exception ExpectedSig of value
exception UnknownCommand of string