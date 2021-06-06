%{
  open Expr
  exception UnexpectedToken of string
%}

%token <string> IDENT
%token <int> NAT
%token LPARENS RPARENS COMMA COLON NO EOF HOLE
%token SET DEFEQ ARROW FST SND LAM DEF
%token DIRSEP MODULE WHERE IMPORT AXIOM
%token SIGMA PI OPTION

%start <Expr.file> file
%start <Expr.command> repl

%%

ident:
  | NO    { No }
  | IDENT { Name ($1, 0) }

idents:
  | ident idents { $1 :: $2 }
  | ident { [$1] }

tele:
  | LPARENS idents COLON exp1 RPARENS { List.map (fun x -> (x, $4)) $2 }

cotele:
  | tele cotele { List.append $1 $2 }
  | tele { $1 }

empcotele:
  | cotele { $1 }
  | { [] }

exp0:
  | exp1 COMMA exp0 { EPair ($1, $3) }
  | exp1 { $1 }

exp1:
  | LAM cotele COMMA exp1 { cotele eLam $4 $2 }
  | PI cotele COMMA exp1 { cotele ePi $4 $2 }
  | SIGMA cotele COMMA exp1 { cotele eSig $4 $2 }
  | exp2 ARROW exp1 { EPi ((No, $1), $3) }
  | exp2 { $1 }

exp2:
  | exp2 exp3 { EApp ($1, $2) }
  | exp3 { $1 }

exp3:
  | HOLE { EHole }
  | SET NAT { ESet $2 }
  | SET { ESet 0 }
  | exp3 FST { EFst $1 }
  | exp3 SND { ESnd $1 }
  | LPARENS exp0 RPARENS { $2 }
  | ident { EVar $1 }

decl:
  | DEF IDENT empcotele COLON exp1 DEFEQ exp1 { Annotated ($2, cotele ePi $5 $3, cotele eLam $7 $3) }
  | DEF IDENT empcotele DEFEQ exp1 { NotAnnotated ($2, cotele eLam $5 $3) }
  | AXIOM IDENT empcotele COLON exp1 { Annotated ($2, cotele ePi $5 $3, EAxiom ($2, $5)) }

path:
  | IDENT { $1 }
  | IDENT DIRSEP path { $1 ^ Filename.dir_sep ^ $3 }

line:
  | IMPORT path { Import $2 }
  | OPTION IDENT IDENT { Option ($2, $3) }
  | decl { Decl $1 }

content:
  | line content { $1 :: $2 }
  | EOF { [] }

file:
  | MODULE IDENT WHERE content { ($2, $4) }

repl:
  | COLON IDENT exp1 EOF { Command ($2, $3) }
  | COLON IDENT EOF { Action $2 }
  | exp0 EOF { Eval $1 }
  | EOF { Nope }
