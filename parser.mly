%{
  open Expr
  exception UnexpectedToken of string
%}

%token <string> IDENT
%token <string> OTHER
%token <int> NAT
%token LPARENS RPARENS COMMA COLON NO EOF HOLE
%token SET STAR DEFEQ ARROW FST SND LAM SKIP
%token DIRSEP MODULE WHERE IMPORT

%start <Expr.file> file
%start <Expr.command> repl

%%

ident:
  | NO    { No }
  | IDENT { Name ($1, 0) }

idents:
  | ident idents { $1 :: $2 }
  | ident { [$1] }

exp0:
  | exp1 COMMA exp0 { EPair ($1, $3) }
  | exp1 { $1 }
  | OTHER { raise (UnexpectedToken $1) }

tele:
  | LPARENS idents COLON exp1 RPARENS { List.map (fun x -> (x, $4)) $2 }

cotele:
  | tele cotele { List.append $1 $2 }
  | tele { $1 }

empcotele:
  | cotele { $1 }
  | { [] }

exp1:
  | LAM cotele ARROW exp1 { cotele eLam $4 $2 }
  | cotele ARROW exp1 { cotele ePi $3 $1 }
  | cotele STAR exp1 { cotele eSig $3 $1 }
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
  | ident { EVar $1 }
  | LPARENS exp0 RPARENS { $2 }

decl:
  | ident empcotele COLON exp1 DEFEQ SKIP* exp1
    { Annotated ($1, cotele ePi $4 $2, cotele eLam $7 $2) }
  | ident empcotele DEFEQ SKIP* exp1
    { NotAnnotated ($1, cotele eLam $5 $2) }

path:
  | IDENT { $1 }
  | IDENT DIRSEP path { $1 ^ Filename.dir_sep ^ $3 }

content:
  | IMPORT path SKIP+ content { Import ($2, $4) }
  | decl SKIP+ content { Decl ($1, $3) }
  | decl SKIP* EOF { Decl ($1, End) }

file:
  | MODULE IDENT WHERE SKIP* content { ($2, $5) }

repl:
  | COLON IDENT exp1 EOF { Command ($2, $3) }
  | COLON IDENT EOF { Action $2 }
  | exp1 EOF { Eval $1 }
  | EOF { Nope }