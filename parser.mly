%{
  open Expr
%}

%token <string> IDENT
%token LPARENS RPARENS COMMA HOLE SET DEF PI SIGMA
%token FST SND COLON DEFEQ ARROW LAM EOF

%start <Expr.exp> exp

%%

patt:
  | patt1 COMMA patt { Pair ($1, $3) }
  | patt1 { $1 }

patt1:
  | HOLE { Unit }
  | IDENT { Var $1 }
  | LPARENS patt RPARENS { $2 }

exp0:
  | exp1 COMMA exp0 { EPair ($1, $3) }
  | exp1 { $1 }

exp1:
  | LAM patt1 COMMA exp1 { ELam ($2, $4) }
  | PI LPARENS patt1 COLON exp1 RPARENS COMMA exp1
    { EPi  ($3, $5, $8) }
  | SIGMA LPARENS patt1 COLON exp1 RPARENS COMMA exp1
    { ESig ($3, $5, $8) }
  | exp2 ARROW exp1 { EPi (Unit, $1, $3) }
  | exp2 { $1 }

exp2:
  | exp2 exp3 { EApp ($1, $2) }
  | exp3 { $1 }

exp3:
  | SET { ESet }
  | exp3 FST { EFst $1 }
  | exp3 SND { ESnd $1 }
  | IDENT { EVar $1 }
  | LPARENS exp0 RPARENS { $2 }

decl:
  | DEF patt1 COLON exp1 DEFEQ exp1 { ($2, $4, $6) }

exp:
  | decl exp { EDec ($1, $2) }
  | EOF { ESet }