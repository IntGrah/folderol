type token =
  | ALL
  | EXISTS
  | NEG
  | DOT
  | COMMA
  | LPAREN
  | RPAREN
  | QUESTION
  | IMPLIES
  | IFF
  | AND
  | OR
  | IDENT of string

val scan : token list -> char list -> token list
