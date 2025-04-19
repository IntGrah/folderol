%{
open Ast
%}

%token ALL EXISTS DOT
%token LPAREN RPAREN COMMA QUESTION
%token NEG AND OR IMPLIES IFF
%token <string> IDENT
%token EOF

%nonassoc IFF
%right IMPLIES
%right OR
%right AND
%nonassoc NEG

%start main
%type <Ast.formula> main
%%

main:
  | formula EOF { $1 }

formula:
  | ALL IDENT DOT formula    { Quant (All, $2, Ast.abstract (Fun ($2, [])) $4) }
  | EXISTS IDENT DOT formula { Quant (Exists, $2, Ast.abstract (Fun ($2, [])) $4) }
  | simple_formula           { $1 }

simple_formula:
  | simple_formula IFF simple_formula     { Binop ($1, Iff, $3) }
  | simple_formula IMPLIES simple_formula { Binop ($1, Implies, $3) }
  | simple_formula OR simple_formula      { Binop ($1, Or, $3) }
  | simple_formula AND simple_formula     { Binop ($1, And, $3) }
  | NEG simple_formula                    { Neg $2 }
  | atomic_formula                        { $1 }

atomic_formula:
  | LPAREN formula RPAREN         { $2 }
  | IDENT                         { Pred ($1, []) }
  | IDENT LPAREN term_list RPAREN { Pred ($1, $3) }

term:
  | IDENT LPAREN term_list RPAREN { Fun ($1, $3) }
  | IDENT                         { Fun ($1, []) }
  | QUESTION IDENT                { Var $2 }

term_list:
  | term COMMA term_list          { $1 :: $3 }
  | term                          { [$1] }