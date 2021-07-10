%{ open Module
   open Ident
   open Elab
   open Expr
%}

%token <string> IDENT
%token <int> KAN
%token <int> PRE
%token LPARENS RPARENS LSQ RSQ
%token COMMA COLON IRREF EOF HOLE
%token DEFEQ PROD ARROW FST SND LAM DEF
%token MODULE WHERE IMPORT AXIOM
%token SIGMA PI OPTION LT GT
%token APPFORMULA PATHP TRANSP HCOMP
%token PARTIAL MAP INC OUC
%token AND OR NEGATE
%token ID REF IDJ

%left OR
%left AND

%nonassoc PATHP TRANSP HCOMP PARTIAL ID REF IDJ INC OUC
%nonassoc NEGATE
%nonassoc FST SND

%start <Module.file> file
%start <Module.command> repl

%%

ident : IRREF { Irrefutable } | IDENT { Name ($1, 0) }
vars : ident+ { $1 }
lense : LPARENS vars COLON exp1 RPARENS { List.map (fun x -> (x, $4)) $2 }
telescope : lense telescope { List.append $1 $2 } | lense { $1 }
params : telescope { $1 } | { [] }
exp0 : exp1 COMMA exp0 { EPair ($1, $3) } | exp1 { $1 }
exp2 : exp2 exp3 { EApp ($1, $2) } | exp3 { $1 } | exp2 APPFORMULA exp3 { EAppFormula ($1, $3) }
path : IDENT { getPath $1 }

file : MODULE IDENT WHERE line* EOF { ($2, $4) }
line : IMPORT path+ { Import $2 } | OPTION IDENT IDENT { Option ($2, $3) } | declarations { Decl $1 }
repl : COLON IDENT exp1 EOF { Command ($2, $3) } | COLON IDENT EOF { Action $2 } | exp0 EOF { Eval $1 } | EOF { Nope }
face : LPARENS IDENT IDENT IDENT RPARENS { face $3 $2 $4 }
partial : face+ ARROW exp1 { (Env.of_seq (List.to_seq $1), $3) }

exp1:
  | LAM telescope COMMA exp1 { telescope eLam $4 $2 }
  | PI telescope COMMA exp1 { telescope ePi $4 $2 }
  | SIGMA telescope COMMA exp1 { telescope eSig $4 $2 }
  | LSQ IRREF ARROW exp1 RSQ { ESystem (Const $4) }
  | LSQ separated_list(COMMA, partial) RSQ { ESystem (Split $2) }
  | exp2 ARROW exp1 { impl $1 $3 }
  | exp2 PROD exp1  { prod $1 $3 }
  | LT vars GT exp1 { pLam $4 $2 }
  | exp2 { $1 }

exp3:
  | HOLE { EHole }
  | PRE { EPre $1 }
  | KAN { EKan $1 }
  | exp3 FST { EFst $1 }
  | exp3 SND { ESnd $1 }
  | NEGATE exp3 { ENeg $2 }
  | exp3 AND exp3 { EAnd ($1, $3) }
  | exp3 OR exp3 { EOr ($1, $3) }
  | ID exp3 { EId $2 }
  | REF exp3 { ERef $2 }
  | IDJ exp3 { EJ $2 }
  | INC exp3 { EInc $2 }
  | OUC exp3 { EOuc $2 }
  | PATHP exp3 { EPathP $2 }
  | TRANSP exp3 exp3 { ETransp ($2, $3) }
  | HCOMP exp3 { EHComp $2 }
  | PARTIAL exp3 { EPartial $2 }
  | IDENT LSQ exp0 MAP exp0 RSQ { ESub (decl $1, $3, $5) }
  | LPARENS exp0 RPARENS LSQ exp0 MAP exp0 RSQ { ESub ($2, $5, $7) }
  | LPARENS exp0 RPARENS { $2 }
  | IDENT { getVar $1 }

declarations:
  | DEF IDENT params COLON exp1 DEFEQ exp1 { Def ($2, Some (telescope ePi $5 $3), telescope eLam $7 $3) }
  | DEF IDENT params DEFEQ exp1 { Def ($2, None, telescope eLam $5 $3) }
  | AXIOM IDENT params COLON exp1 { Axiom ($2, telescope ePi $5 $3) }
