%{
open Ast
%}

%token <string> IDENT
%token ALL EXISTS IMPL IFF OR AND NOT DOT LPAREN RPAREN COMMA QUESTION EOF

%start main
%type <Ast.formula> main

%%

main:
  | formula EOF { $1 }

formula:
  | atom                                { $1 }
  | NOT formula                         { Not $2 }
  | formula AND formula                 { And ($1, $3) }
  | formula OR formula                  { Or ($1, $3) }
  | formula IMPL formula                { Imp ($1, $3) }
  | formula IFF formula                 { Iff ($1, $3) }
  | ALL IDENT DOT formula               { Forall ($2, $4) }
  | EXISTS IDENT DOT formula            { Exists ($2, $4) }
  | LPAREN formula RPAREN               { $2 }

atom:
  | IDENT                               { Var $1 }
  | IDENT LPAREN terms RPAREN           { Pred ($1, $3) }

terms:
  | term                                { [$1] }
  | term COMMA terms                      { $1 :: $3 }

term:
  | IDENT                               { Const $1 }
  | IDENT LPAREN terms RPAREN           { Func ($1, $3) }
