%{
  open Expr
%}

%token <string> IDENT
%token LPARENS RPARENS COMMA COLON HOLE EOF
%token SET STAR DEFEQ ARROW FST SND LAM SKIP

%start <Expr.exp> codecl
%start <Expr.command> repl

%%

ident:
  | HOLE  { Hole }
  | IDENT { Name ($1, 0) }

exp0:
  | exp1 COMMA exp0 { EPair ($1, $3) }
  | exp1 { $1 }

tele:
  | LPARENS ident COLON exp1 RPARENS { ($2, $4) }

cotele:
  | tele cotele { $1 :: $2 }
  | tele { [$1] }

exp1:
  | LAM cotele ARROW exp1 { cotele eLam $4 $2 }
  | cotele ARROW exp1 { cotele ePi  $3 $1 }
  | cotele STAR exp1  { cotele eSig $3 $1 }
  | exp2 ARROW exp1   { EPi ((Hole, $1), $3) }
  | exp2 { $1 }

exp2:
  | exp2 exp3 { EApp ($1, $2) }
  | exp3 { $1 }

exp3:
  | SET { ESet }
  | exp3 FST { EFst $1 }
  | exp3 SND { ESnd $1 }
  | ident { EVar $1 }
  | LPARENS exp0 RPARENS { $2 }

decl:
  | ident COLON exp1 DEFEQ SKIP? exp1 { ($1, $3, $6) }

codecl:
  | decl SKIP codecl { EDec ($1, $3) }
  | decl EOF { EDec ($1, ESet) }

repl:
  | COLON IDENT exp0 EOF { Command ($2, $3) }
  | exp0 EOF { Eval $1 }
  | EOF { Nope }